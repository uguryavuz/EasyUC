uc_requires ReadCAS.
ec_requires +ReadWriteGeneric.

direct IO' {
  in pt@init_with(v : int)
  out init_done@pt
  in pt@inv(p : process, oper : operation, arg : int option)
  out rsp(p : process, oper : operation, v : int option)@pt
}

direct IO {D : IO'}

adversarial Scheduler_Real' {
  out init_req(v : int)
  in init_ok
  out suspend
  in resume(p : process)
}

adversarial Scheduler_Real {A : Scheduler_Real'}

functionality RW_Real implements IO Scheduler_Real {
  subfun ReadCASReg = ReadCAS.ReadCAS_Spec
  party IOHandler serves IO.D Scheduler_Real.A {
    initial state Init {
      match message with 
      | pt@IO.D.init_with(v) => {
          send Scheduler_Real.A.init_req(v)
          and transition InitPending(pt, v).
        }
      | * => { fail. }
      end
    }
    state InitPending(init_pt : port, init_val : int) {
      match message with
      | Scheduler_Real.A.init_ok => {
          send ReadCASReg.I.initialize(init_val)
          and transition InitPending(init_pt, init_val).
        }
      | ReadCASReg.I.initialized => {
          send IO.D.init_done@init_pt
          and transition Final(empty, empty).
        }
      | * => { fail. }
      end
    }
    state Final(p_map : port_map, s_map : real_state_map) {
      var new_port_map : port_map;
      var new_state_map : real_state_map;
      var new_vars : local_vars;
      match message with
      | pt@IO.D.inv(p, oper, arg) => {
          if (p \in p_map) { fail. }
          elif (p \in s_map) { fail. }
          else {
            match oper with
            | Read => { 
                match arg with 
                | Some v => { fail. }
                | None => { 
                    new_port_map <- p_map.[p <- pt];
                    new_state_map <- s_map.[p <- {| rlst_status = Real_Invoked; rlst_op = Read; rlst_arg = None; rlst_vars = init_vars |}];
                    send Scheduler_Real.A.suspend
                    and transition Final(new_port_map, new_state_map).
                  }
                end
              }
            | Write => { 
                match arg with 
                | None => { fail. }
                | Some v => { 
                    new_port_map <- p_map.[p <- pt];
                    new_state_map <- s_map.[p <- {| rlst_status = Real_Invoked; rlst_op = Write; rlst_arg = Some v; rlst_vars = init_vars |}];
                    send Scheduler_Real.A.suspend
                    and transition Final(new_port_map, new_state_map).
                  }
                end
              }
            end
          }
        }
      | Scheduler_Real.A.resume(p) => { 
          if (p \notin p_map) { fail. }
          elif (p \notin s_map) { fail. }
          else {
            match (oget s_map.[p]).`rlst_status with
            | Real_Invoked => { 
                match (oget s_map.[p]).`rlst_op with
                | Read => { 
                    new_state_map <- s_map.[p <- {| (oget s_map.[p]) with rlst_status = R1 |}];
                    send Scheduler_Real.A.suspend
                    and transition Final(p_map, new_state_map).
                  }
                | Write => { 
                    new_state_map <- s_map.[p <- {| (oget s_map.[p]) with rlst_status = W1 |}];
                    send Scheduler_Real.A.suspend
                    and transition Final(p_map, new_state_map).
                  }
                end
              }
            | R1 => { 
                send ReadCASReg.D.read_req(p)
                and transition Final(p_map, s_map).
              }
            | W1 => { 
                send ReadCASReg.D.read_req(p)
                and transition Final(p_map, s_map).
              }
            | W2 => { 
                send ReadCASReg.D.cas_req(p, oget (oget s_map.[p]).`rlst_vars.`x, oget (oget s_map.[p]).`rlst_arg)
                and transition Final(p_map, s_map).
              }
            | Real_Terminated => { 
                new_port_map <- rem p_map p;
                new_state_map <- rem s_map p;
                match (oget s_map.[p]).`rlst_op with
                | Read => { 
                    send IO.D.rsp(p, Read, (oget s_map.[p]).`rlst_vars.`x)@(oget p_map.[p])
                    and transition Final(new_port_map, new_state_map).
                  }
                | Write => { 
                    send IO.D.rsp(p, Write, None)@(oget p_map.[p])
                    and transition Final(new_port_map, new_state_map).
                  }
                end
              }
            end
          }      
        }
      | ReadCASReg.D.read_rsp(p, v) => { 
          new_vars <- {| x = Some v |};
          match (oget s_map.[p]).`rlst_status with
          | R1 => { 
              new_state_map <- s_map.[p <- {| (oget s_map.[p]) with rlst_status = Real_Terminated; rlst_vars = new_vars |}];
              send Scheduler_Real.A.suspend
              and transition Final(p_map, new_state_map).
            }
          | W1 => { 
              new_state_map <- s_map.[p <- {| (oget s_map.[p]) with rlst_status = W2; rlst_vars = new_vars |}];
              send Scheduler_Real.A.suspend
              and transition Final(p_map, new_state_map).
            }
          | Real_Invoked => { fail. }
          | Real_Terminated => { fail. }
          | W2 => { fail. }
          end
        }
      | ReadCASReg.D.cas_rsp(p, b) => { 
          match (oget s_map.[p]).`rlst_status with
          | W2 => { 
              if (b) {
                new_state_map <- s_map.[p <- {| (oget s_map.[p]) with rlst_status = Real_Terminated |}];
                send Scheduler_Real.A.suspend
                and transition Final(p_map, new_state_map).
              }
              else {
                new_state_map <- s_map.[p <- {| (oget s_map.[p]) with rlst_status = W1 |}];
                send Scheduler_Real.A.suspend
                and transition Final(p_map, new_state_map).
              }
            }
          | Real_Invoked => { fail. }
          | Real_Terminated => { fail. }
          | R1 => { fail. }
          | W1 => { fail. }
          end
        }
      | * => { fail. }
      end
    }
  }
}

adversarial Scheduler_Ideal {
  out init_req(v : int)
  in init_ok
  out invoked(p : process, idst : ideal_state)
  in linearize(p : process)
  out linearized(p : process, idst : ideal_state)
  in return_ok(p : process)
}

functionality RW_Ideal implements IO Scheduler_Ideal {
  initial state Init {
    match message with 
    | pt@IO.D.init_with(v) => {
        send Scheduler_Ideal.init_req(v)
        and transition InitPending(pt, v).
      }
    | * => { fail. }
    end
  }
  state InitPending(init_pt : port, init_val : int) {
    match message with
    | Scheduler_Ideal.init_ok => {
        send IO.D.init_done@init_pt
        and transition Final(init_val, empty, empty).
      }
    | * => { fail. }
    end
  }
  state Final(cur_val : int, p_map : port_map, is_map : ideal_state_map) {
    var new_port_map : port_map;
    var new_is_map : ideal_state_map;
    match message with
    | pt@IO.D.inv(p, oper, arg) => { 
        if (p \in p_map) { fail. }
        elif (p \in is_map) { fail. }
        else {
          match oper with
          | Read => { 
              match arg with 
              | Some v => { fail. }
              | None => { 
                  new_port_map <- p_map.[p <- pt];
                  new_is_map <- is_map.[p <- {| idlst_status = Ideal_Invoked; idlst_op = Read; idlst_arg = None; idlst_ret = None |}];
                  send Scheduler_Ideal.invoked(p, {| idlst_status = Ideal_Invoked; idlst_op = Read; idlst_arg = None; idlst_ret = None |})
                  and transition Final(cur_val, new_port_map, new_is_map).
                }
              end
            }
          | Write => { 
              match arg with
              | None => { fail. }
              | Some v => { 
                  new_port_map <- p_map.[p <- pt];
                  new_is_map <- is_map.[p <- {| idlst_status = Ideal_Invoked; idlst_op = Write; idlst_arg = Some v; idlst_ret = None |}];
                  send Scheduler_Ideal.invoked(p, {| idlst_status = Ideal_Invoked; idlst_op = Write; idlst_arg = Some v; idlst_ret = None |})
                  and transition Final(cur_val, new_port_map, new_is_map).
                }
              end  
            }
          end
        }
      }
    | Scheduler_Ideal.linearize(p) => { 
        if (p \notin p_map) { fail. }
        elif (p \notin is_map) { fail. }
        elif ((oget is_map.[p]).`idlst_status = Ideal_Linearized) { fail. }
        else {
          match (oget is_map.[p]).`idlst_op with
          | Read => { 
              new_is_map <- is_map.[p <- {| (oget is_map.[p]) with idlst_status = Ideal_Linearized; idlst_ret = Some cur_val |}];
              send Scheduler_Ideal.linearized(p, {| (oget is_map.[p]) with idlst_status = Ideal_Linearized; idlst_ret = Some cur_val |})
              and transition Final(cur_val, p_map, new_is_map).
            }
          | Write => { 
              new_is_map <- is_map.[p <- {| (oget is_map.[p]) with idlst_status = Ideal_Linearized |}];
              send Scheduler_Ideal.linearized(p, {| (oget is_map.[p]) with idlst_status = Ideal_Linearized |})
              and transition Final(oget (oget is_map.[p]).`idlst_arg, p_map, new_is_map).
            }
          end
        } 
      }
    | Scheduler_Ideal.return_ok(p) => { 
        if (p \notin p_map) { fail. }
        elif (p \notin is_map) { fail. }
        elif ((oget is_map.[p]).`idlst_status <> Ideal_Linearized) { fail. }
        else {
          new_port_map <- rem p_map p;
          new_is_map <- rem is_map p;
          send IO.D.rsp(p, (oget is_map.[p]).`idlst_op, (oget is_map.[p]).`idlst_ret)@(oget p_map.[p])
          and transition Final(cur_val, new_port_map, new_is_map).
        }
      }
    | * => { fail. }
    end
  }
}

(* Matched incoming messages should be as follows: *)
(* 
  Scheduler_Ideal.invoked,
  Scheduler_Ideal.linearized,
  RW_Real.Scheduler_Real.A.resume 

  --- init ---
  Scheduler_Ideal.init_req,
  RW_Real.Scheduler_Real.A.init_ok
*)
(* Outgoing messages should be as follows: *)
(* 
  RW_Real.Scheduler_Real.A.suspend,
  Scheduler_Ideal.return_ok,
  Scheduler_Ideal.linearize,

  --- init ---
  Scheduler_Ideal.init_ok,
  RW_Real.Scheduler_Real.A.init_req) *)

simulator Sim uses Scheduler_Ideal simulates RW_Real {
  initial state Init {
    match message with 
    | Scheduler_Ideal.init_req(v) => { 
        send RW_Real.Scheduler_Real.A.init_req(v)
        and transition InitPending(v).
      }
    | * => { fail. }
    end
  }
  state InitPending(init_val : int) {
    match message with
    | RW_Real.Scheduler_Real.A.init_ok => {
        send Scheduler_Ideal.init_ok
        and transition Final(init_val, empty).
      }
    | * => { fail. }
    end
  }
  state Final(cur_val : int, sim_rs_map : real_state_map) {
    var new_sim_rs_map : real_state_map;
    match message with
    | Scheduler_Ideal.invoked(p, idst) => {
        new_sim_rs_map <- sim_rs_map.[p <- {| rlst_status = Real_Invoked; rlst_op = idst.`idlst_op; rlst_arg = idst.`idlst_arg; rlst_vars = init_vars |}];
        send RW_Real.Scheduler_Real.A.suspend
        and transition Final(cur_val, new_sim_rs_map).
      }
    | RW_Real.Scheduler_Real.A.resume(p) => {
        (* TODO: Should you check p \in sim_rs_map? *)
        match (oget sim_rs_map.[p]).`rlst_status with
        | Real_Invoked => { 
            match (oget sim_rs_map.[p]).`rlst_op with
            | Read => { 
                new_sim_rs_map <- sim_rs_map.[p <- {| (oget sim_rs_map.[p]) with rlst_status = R1 |}];
                send RW_Real.Scheduler_Real.A.suspend
                and transition Final(cur_val, new_sim_rs_map).
              }
            | Write => { 
                new_sim_rs_map <- sim_rs_map.[p <- {| (oget sim_rs_map.[p]) with rlst_status = W1 |}];
                send RW_Real.Scheduler_Real.A.suspend
                and transition Final(cur_val, new_sim_rs_map).
              }
            end
          }
        | R1 => { 
            new_sim_rs_map <- sim_rs_map.[p <- {| (oget sim_rs_map.[p]) with rlst_status = Real_Terminated; rlst_vars = {| x = Some cur_val |} |}];
            send Scheduler_Ideal.linearize(p)
            and transition Final(cur_val, new_sim_rs_map).
          }
        | W1 => { 
            new_sim_rs_map <- sim_rs_map.[p <- {| (oget sim_rs_map.[p]) with rlst_status = W2; rlst_vars = {| x = Some cur_val |} |}];
            send RW_Real.Scheduler_Real.A.suspend
            and transition Final(cur_val, new_sim_rs_map).
          }
        | W2 => { 
            if (oget (oget sim_rs_map.[p]).`rlst_vars.`x = cur_val) {
              new_sim_rs_map <- sim_rs_map.[p <- {| (oget sim_rs_map.[p]) with rlst_status = Real_Terminated |}];
              send Scheduler_Ideal.linearize(p)
              and transition Final(cur_val, new_sim_rs_map).
            }
            else {
              new_sim_rs_map <- sim_rs_map.[p <- {| (oget sim_rs_map.[p]) with rlst_status = W1 |}];
              send RW_Real.Scheduler_Real.A.suspend
              and transition Final(cur_val, new_sim_rs_map).
            }
          }
        | Real_Terminated => { 
            new_sim_rs_map <- rem sim_rs_map p;
            send Scheduler_Ideal.return_ok(p)
            and transition Final(cur_val, new_sim_rs_map).
          }
        end
      }
    | Scheduler_Ideal.linearized(p, idst) => {
        match (oget sim_rs_map.[p]).`rlst_op with
        | Read => {
            send RW_Real.Scheduler_Real.A.suspend
            and transition Final(cur_val, sim_rs_map).
          }
        | Write => {
            send RW_Real.Scheduler_Real.A.suspend
            and transition Final(oget idst.`idlst_arg, sim_rs_map).
          }
        end
      }
    | * => { fail. }
    end
  }
}

