require import UCBasicTypes.
require export Process FMap.

(* Ubiquitous *)
type operation = [Read | Write].
type port_map = (process, port) fmap.

(* For real *)
type real_status = [Real_Invoked | R1 | W1 | W2 | Real_Terminated].
type local_vars = { x : int option }.
op init_vars = {| x = None |}.
type real_state = { rlst_status : real_status;
                    rlst_op : operation;
                    rlst_arg : int option;
                    rlst_vars : local_vars }.
type real_state_map = (process, real_state) fmap.

(* For ideal *)
type ideal_status = [Ideal_Invoked | Ideal_Linearized].
type ideal_state = { idlst_status : ideal_status; 
                     idlst_op  : operation;
                     idlst_arg : int option;
                     idlst_ret : int option }.
type ideal_state_map = (process, ideal_state) fmap.

(* Simplification hints *)
hint simplify get_set_sameE.
hint simplify set_set_eqE.
hint simplify mem_empty.

lemma mem_set_in (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  x \in m.[x <- y].
proof.
  by rewrite -mem_fdom fdom_set in_fsetU in_fset1.
qed.
hint simplify mem_set_in.

lemma rem_singl_empty (x : 'a, y : 'b) :
  (rem empty.[x <- y] x) = empty.
proof.
  rewrite fdom_eq0 //.
  rewrite fdom_rem fdom_set fdom0.
  by rewrite fset0U fsetDv.
qed.
hint simplify rem_singl_empty.

lemma neq_mem_singl_false (x1 : 'a, x2 : 'a, y : 'b) :
  x1 <> x2 => x1 \notin empty.[x2 <- y].
proof.
  apply contra.
  rewrite mem_set.
  move => [H1 | H2] //.
  by rewrite mem_empty in H1.
qed.
hint simplify neq_mem_singl_false.

lemma nin_rem_set_id (m : ('a, 'b) fmap, x : 'a, y : 'b) :
  x \notin m => rem m.[x <- y] x = m.
proof.
  move => H1.
  apply fmap_eqP.
  move => x0.
  rewrite remE.
  case (x0 = x) => H2.
  + rewrite H2.
    apply get_none in H1.
    by rewrite H1.
  + by apply get_set_neqE.
qed.
hint simplify nin_rem_set_id.
