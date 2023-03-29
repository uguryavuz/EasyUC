type evalConditionResult = 
  | Bool of bool
  | Undecided
  
let get_ttenv () =
  {
    EcHiGoal.tt_provers    = (fun _ -> {
      EcProvers.dft_prover_infos with pr_provers = EcProvers.dft_prover_names
      });
    EcHiGoal.tt_smtmode    = `Standard;
    EcHiGoal.tt_implicits  = true;
    EcHiGoal.tt_oldip      = false;
    EcHiGoal.tt_redlogic   = true;
    EcHiGoal.tt_und_delta  = false;
  }
  
let run_tac (tac : EcCoreGoal.FApi.backward) (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let tc1 = EcCoreGoal.tcenv1_of_proof proof in
  let tc = tac tc1 in
  let proof' = EcCoreGoal.proof_of_tcenv tc in
  proof'

(*move => |>.*)
let crush (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_crush = (*modified from ecHiGoal.ml*)
    let delta, tsolve = (false , None) in
    EcCoreGoal.FApi.t_or
      (EcPhlConseq.t_conseqauto ~delta ?tsolve)
      (EcLowGoal.t_crush ~delta ?tsolve)
  in
  run_tac intro1_crush proof

let tac_move_hyp_form_to_concl 
(h_id : EcIdent.t) 
(proof : EcCoreGoal.proof) 
: EcCoreGoal.proof =
  let generalize_hyp = EcLowGoal.t_generalize_hyp ~clear:`Yes h_id in
  run_tac generalize_hyp proof

let get_only_pregoal (proof : EcCoreGoal.proof) : EcCoreGoal.pregoal =
  let goal = EcCoreGoal.opened proof in
  match goal with
  | Some (1, pregoal) -> pregoal
  | _ -> failwith "failed getting the one and only pregoal"
  
let move_all_hyp_forms_to_concl (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let hyps = (get_only_pregoal proof).g_hyps  in
  let hyp_ids = List.filter_map ( fun h -> 
      match h with 
      | (id, EcBaseLogic.LD_hyp _) -> Some id
      | _ -> None
    ) (EcEnv.LDecl.tohyps hyps).h_local
  in
  let proof' = List.fold_right tac_move_hyp_form_to_concl hyp_ids proof in
  proof'

(* proof pretty printer
let pp_tc tc = (* copied from ecLowGoal.ml *)
  let pr = EcCoreGoal.proofenv_of_proof (EcCoreGoal.proof_of_tcenv tc) in
  let cl = List.map (fun h -> EcCoreGoal.FApi.get_pregoal_by_id h pr) (EcCoreGoal.FApi.tc_opened tc) in
  let cl = List.map (fun (x:EcCoreGoal.pregoal) -> (EcEnv.LDecl.tohyps x.g_hyps, x.g_concl)) cl in

  match cl with [] -> () | hd :: tl ->

  Format.eprintf "%a@."
    (EcPrinting.pp_goal (EcPrinting.PPEnv.ofenv (EcCoreGoal.FApi.tc_env tc)) {prpo_pr = true; prpo_po = true})
    (hd, `All tl)

let pp_proof (proof : EcCoreGoal.proof) : unit =
  pp_tc (EcCoreGoal.tcenv_of_proof proof)
*)

let can_prove_smt (proof : EcCoreGoal.proof) : bool =
  let dft_pi = { 
    EcProvers.dft_prover_infos with pr_provers = EcProvers.dft_prover_names
  } in
  let goal = EcCoreGoal.opened proof in
  try
    match goal with
    | Some (1, pregoal) -> EcSmt.check dft_pi pregoal.g_hyps pregoal.g_concl
    | _ -> false
  with _ -> false

let can_prove_crush (proof : EcCoreGoal.proof) : bool =
  let proof_m = move_all_hyp_forms_to_concl proof in
  let proof_c = crush proof_m in
  EcCoreGoal.closed proof_c

let can_prove (proof : EcCoreGoal.proof) : bool =
  if can_prove_crush proof
    then true
    else can_prove_smt proof

let to_LDecl_hyps (hyps : EcBaseLogic.hyps) : EcEnv.LDecl.hyps =
  let local_h = List.rev hyps.h_local in
  let env = UcEcInterface.env () in
  EcEnv.LDecl.init env ~locals:local_h hyps.h_tvar

let evalCondition (hyps : EcBaseLogic.hyps) (form : EcCoreFol.form) : evalConditionResult =
  let hyps = to_LDecl_hyps hyps in
  let proof_true = EcCoreGoal.start hyps form in
  let proof_false = EcCoreGoal.start hyps (EcCoreFol.f_not form) in

  if can_prove proof_true
    then
      Bool true
    else
      if can_prove proof_false
        then
          Bool false
        else
          Undecided
      
let unique_id_for_proof (proof : EcCoreGoal.proof) : EcIdent.t = 
  let pregoal = get_only_pregoal proof in
  let hyps = pregoal.g_hyps in
  let name = EcUid.NameGen.ofint (EcUid.unique ()) in
  EcEnv.LDecl.fresh_id hyps name

(*move => [#].*)
let move_hash (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_full_case tc (*modified from ecHiGoal.ml*)
  =
    let red = `NoDelta in

    let t_case =
      let t_and = fun tc -> ([2]   , EcLowGoal.t_elim_and ~reduce:red tc) in
      let ts = [t_and] in
      fun tc -> EcCoreGoal.FApi.t_or_map ts tc
    in

    let doit tc =
      let rec aux imax tc =
        if imax = Some 0 then EcLowGoal.t_id tc else

        try
          let ntop, tc = t_case tc in

          EcCoreGoal.FApi.t_sublasts
            (List.map (fun i tc -> aux (EcUtils.omap ((+) (i-1)) imax) tc) ntop)
            tc
        with EcCoreGoal.InvalidGoalShape ->
          try
            tc |> EcLowGoal.t_intro_sx_seq
              `Fresh
              (fun id ->
                EcCoreGoal.FApi.t_seq
                  (aux (EcUtils.omap ((+) (-1)) imax))
                  (EcLowGoal.t_generalize_hyps ~clear:`Yes [id]))
          with
          | EcCoreGoal.TcError _ when EcUtils.is_some imax ->
              EcCoreGoal.tc_error (EcCoreGoal.(!!) tc) "not enough top-assumptions"
          | EcCoreGoal.TcError _ ->
              EcLowGoal.t_id tc
      in
      aux (Some 1) tc
    in
    doit tc
  in
  run_tac intro1_full_case proof

(*move => hyp_name.*)    
let move_up (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_core id tc = (*modified from ecHiGoal.ml*)
    EcLowGoal.t_intros [id] tc
  in
  let h_id = unique_id_for_proof proof in
  let h_id_mloc = EcUtils.Tagged (h_id,Some EcLocation._dummy) in
  run_tac (intro1_core h_id_mloc) proof

(*move => /=.*)
let move_simplify (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  let intro1_simplify tc = (*modified from ecHiGoal.ml*)
    EcLowGoal.t_simplify ~delta:false ~logic:(Some `Full) tc
  in
  run_tac intro1_simplify proof

let is_concl_p (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : bool =
  let pregoal = get_only_pregoal proof in
  let concl = pregoal.g_concl in
  begin match (EcCoreFol.f_node concl) with
  | Fapp (f, _ ) -> 
    begin match (EcCoreFol.f_node f) with
    | Flocal id when id = p_id -> true
    | _ -> false
    end
  | _ -> false
  end
  
let extract_form (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreFol.form =
  let pregoal = get_only_pregoal proof in
  let concl = pregoal.g_concl in
  begin match (EcCoreFol.f_node concl) with
  | Fapp (f, [fs]) -> 
    begin match (EcCoreFol.f_node f) with
    | Flocal id when id = p_id -> fs
    | _ -> failwith "extract_form failed - not application of p_id"
    end
  | _ -> failwith "extract_form failed - not application"
  end

let progression 
(f : EcCoreGoal.proof -> EcCoreGoal.proof option)
(proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let rec r 
  (first_call : bool) (proof : EcCoreGoal.proof) 
  : EcCoreGoal.proof option 
  = match f proof with
    | None -> 
      if first_call
      then None
      else Some proof
    | Some proof_new -> r false proof_new
  in
  r true proof
  
let move_hash_all (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
  let hash_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
    if (is_concl_p proof p_id)
    then
      None
    else
      let proof_a = try move_hash proof with _ -> proof in
      let proof_b = move_simplify proof_a in
      let proof_c = move_up proof_b in
      Some proof_c
   in
   let proof_o = progression hash_step proof in
   match proof_o with
   | None -> proof
   | Some pr -> pr
   

let prelims (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
  let proof_a = move_all_hyp_forms_to_concl proof in
  let proof_b = move_hash_all proof_a p_id in
  let proof_c = move_all_hyp_forms_to_concl proof_b in
  proof_c

let intro1_rw s tc = (*modified from ecHiGoal.ml*)
  let process_rewrite1_core ?(close = true) s pt tc =
    let tc = EcHiGoal.LowRewrite.t_rewrite_r (s, None, None) pt tc in
    let cl = fun tc ->
      if EcFol.f_equal EcFol.f_true (EcCoreGoal.FApi.tc1_goal tc) then
        EcLowGoal.t_true tc
      else EcLowGoal.t_id tc
    in 
    if close then EcCoreGoal.FApi.t_last cl tc else tc
  in
  let h = EcIdent.create "_" in
  let rwt tc =
    let pt = EcProofTerm.pt_of_hyp (EcCoreGoal.(!!) tc) (EcCoreGoal.FApi.tc1_hyps tc) h in
    process_rewrite1_core ~close:false s pt tc
  in 
  EcCoreGoal.FApi.t_seqs [EcLowGoal.t_intros_i [h]; rwt; EcLowGoal.t_clear h] tc

(*move => ->.*)  
let move_right (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tac (intro1_rw `LtoR) proof

(*move => <-.*)
let move_left (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  run_tac (intro1_rw `RtoL) proof
  
let try_move_lr_all (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let try_move_lr_step (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
    try 
      let proof_a = move_right proof in
      let proof_b = move_simplify proof_a in
      Some proof_b
    with _ ->
      try 
        let proof_a = move_left proof in
        let proof_b = move_simplify proof_a in
        Some proof_b
      with _ -> None
  in
  progression try_move_lr_step proof 
  
let move_down (h_id : EcIdent.t) (proof : EcCoreGoal.proof) : EcCoreGoal.proof =
  tac_move_hyp_form_to_concl h_id proof
  
let rec move_all_hyps_up (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
  if (is_concl_p proof p_id)
  then 
    proof
  else 
    let proof' = move_up proof in
    move_all_hyps_up proof' p_id

let count_hyp_forms (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : int =
  let proof' = move_all_hyps_up proof p_id in
  let pregoal = get_only_pregoal proof' in
  let h = (EcEnv.LDecl.tohyps pregoal.g_hyps).h_local in
  let h_forms = List.filter 
    (
      fun (_,l_k) -> 
        match l_k with 
        | EcBaseLogic.LD_hyp _ -> true 
        | _ -> false 
    ) h 
  in
  List.length h_forms

let rotate_hyps (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof =
  let proof_a = move_all_hyps_up proof p_id in
  let pregoal = get_only_pregoal proof_a in
  let h = (EcEnv.LDecl.tohyps pregoal.g_hyps).h_local in
  let form_ids = List.filter_map 
    (
      fun (n,l_k) -> 
        match (n,l_k) with 
        | (n, EcBaseLogic.LD_hyp _) -> Some n 
        | _ -> None 
    ) h 
  in
  match form_ids with
  | [] -> 
    proof
  | hd :: tl -> 
    let proof_b = move_down hd proof_a in
    let proof_c = List.fold_right (fun id pr -> move_down id pr) tl proof_b
    in 
    proof_c

let try_simplification_cycle (p_id : EcIdent.t) (proof : EcCoreGoal.proof) : EcCoreGoal.proof option =
  let rec try_simpcyc_r 
  (counter : int) (proof : EcCoreGoal.proof) 
  : EcCoreGoal.proof option 
  = if counter=0 then None
    else
      match try_move_lr_all proof with
      | Some pr -> Some pr
      | None -> try_simpcyc_r (counter-1) (rotate_hyps proof p_id) 
  in
  let counter = count_hyp_forms proof p_id in
  try_simpcyc_r counter proof
  
let try_simp (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreGoal.proof option = 
  progression (try_simplification_cycle p_id) proof 

let simplify_heuristic (proof : EcCoreGoal.proof) (p_id : EcIdent.t) : EcCoreFol.form =
  let proof_a = prelims proof p_id in
  let proof_o = try_simp proof_a p_id in
  match proof_o with
  | None -> extract_form proof p_id
  | Some pr -> extract_form pr p_id

let simplify_by_crushing 
(proof : EcCoreGoal.proof) 
(p_id : EcIdent.t) 
: EcCoreFol.form =
(*simplification by crushing*)
  let default = extract_form proof p_id in
  let proof_m = move_all_hyp_forms_to_concl proof in
  let proof_c = crush proof_m in
(*if conclusion is p(f), return f, otherwise return original formula*)
  let form_s =	
    let goal = EcCoreGoal.opened proof_c in
    begin match goal with
    | Some (1, pregoal) ->
      let c = pregoal.g_concl in
      begin match (EcCoreFol.f_node c) with
      | Fapp (f, [fs]) -> 
        begin match (EcCoreFol.f_node f) with
        | Flocal id when id = p_id -> fs
        | _ -> default
        end
      | _ -> default
      end
    | _ -> default
    end 
  in
  form_s
              
let simplifyFormula (hyps : EcBaseLogic.hyps) (form : EcCoreFol.form) : EcCoreFol.form =
(*for conclusion, make a dummy predicate p with form as input*)
  let f_ty = EcCoreFol.f_ty form in
  let p_ty = EcTypes.tcpred f_ty in
  let p_name = EcUid.NameGen.ofint (EcUid.unique ()) in
  let p_id = EcIdent.create p_name in
(*add predicate p to hypotheses*)
  let l_k = EcBaseLogic.LD_var (p_ty, None) in
  let hyps = {hyps with h_local = hyps.h_local @ [(p_id,l_k)]} in
  let hyps = to_LDecl_hyps hyps in
(*make concl and start proof*)  
  let fp = EcCoreFol.f_local p_id p_ty in
  let concl = EcCoreFol.f_app fp [form] EcTypes.tbool in
  let proof = EcCoreGoal.start hyps concl in
(*try to simplify form*)  
  (*simplify_by_crushing proof p_id*)
  simplify_heuristic proof p_id







