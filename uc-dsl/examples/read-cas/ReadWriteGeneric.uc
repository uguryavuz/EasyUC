uc_requires ReadCAS.
ec_requires +ReadWriteGeneric.

direct IO {
  in pt@inv(p : process, oper : operation, arg : int option)
  out rsp(p : process, oper : operation, v : int option)@pt
}

(* You cannot merge this into a single direct interface and have a single party *)
(* Be mindful of the following:
   "send and transition of initial state of party of real functionality that
    serves basic adversarial interface must send adversarial message to adversary" *)

direct Init {
  in pt@initialize(v : int)
  out initialized@pt
}

direct IO_Init {
  D : IO
  I : Init
}

adversarial Sched_Adv' {
  out suspend
  in resume(p : process)
}

adversarial Sched_Adv {A : Sched_Adv'}

functionality ReadWriteGeneric implements IO_Init Sched_Adv {
  subfun ReadCASReg = ReadCAS.ReadCAS_Spec
  party Initializer serves IO_Init.I {
    initial state Init {
      match message with
      | pt@IO_Init.I.initialize(v) => {
          send ReadCASReg.I.initialize(v)
          and transition WaitingInit(pt).
        }
      | * => { fail. }
      end
    }
    state WaitingInit(init_pt : port) {
      match message with
      | ReadCASReg.I.initialized => {
          send IO_Init.I.initialized@init_pt
          and transition Final.
        }
      | * => { fail. }
      end
    }
    state Final {
      match message with
      | * => { fail. }
      end
    }
  }
  party IOHandler serves IO_Init.D Sched_Adv.A {
    initial state Init {
      var new_port_map : port_map; 
      var new_state_map : state_map;
      match message with
      | pt@IO_Init.D.inv(p, oper, arg) => {
          new_port_map <- empty.[p <- pt];
          match oper with
          | Read => { 
              match arg with
              | Some v => { fail. }
              | None => { 
                  new_state_map <- empty.[p <- {| pc = R1; arg = None; vars = init_vars |}];
                  send Sched_Adv.A.suspend
                  and transition PostInit(new_port_map, new_state_map).
                }
              end
            }
          | Write => { 
              match arg with
              | Some v => { 
                  new_state_map <- empty.[p <- {| pc = W1; arg = Some v; vars = init_vars |}];
                  send Sched_Adv.A.suspend
                  and transition PostInit(new_port_map, new_state_map).
                }
              | None => { fail. }
              end
            }
          end
        }
      | * => { fail. }
      end
    }
    state PostInit(p_map : port_map, s_map : state_map) {
      var new_port_map : port_map; 
      var new_state_map : state_map;
      var new_vars : local_vars;
      match message with
      | pt@IO_Init.D.inv(p, oper, arg) => { 
          if (p \in p_map) { fail. }
          elif (p \in s_map) { fail. }
          else {
            match oper with
            | Read => { 
                match arg with
                | Some v => { fail. }
                | None => { 
                    new_port_map <- p_map.[p <- pt];
                    new_state_map <- s_map.[p <- {| pc = R1; arg = None; vars = init_vars |}]; 
                    send Sched_Adv.A.suspend
                    and transition PostInit(new_port_map, new_state_map).
                  }
                end
              }
            | Write => {
                match arg with
                | Some v => { 
                    new_port_map <- p_map.[p <- pt];
                    new_state_map <- s_map.[p <- {| pc = W1; arg = Some v; vars = init_vars |}];
                    send Sched_Adv.A.suspend
                    and transition PostInit(new_port_map, new_state_map).
                  }
                | None => { fail. }
                end
              }
            end
          }
        }
      | Sched_Adv.A.resume(p) => { 
          if (p \notin p_map) { fail. }
          elif (p \notin s_map) { fail. }
          else {
            match (oget s_map.[p]).`pc with
            | R1 => { 
                send ReadCASReg.D.read_req(p)
                and transition PostInit(p_map, s_map).
              }
            | R2 => { 
                new_port_map <- rem p_map p;
                new_state_map <- rem s_map p;
                send IO_Init.D.rsp(p, Read, (oget s_map.[p]).`vars.`x)@(oget p_map.[p])
                and transition PostInit(new_port_map, new_state_map).
              }
            | W1 => { 
                send ReadCASReg.D.read_req(p)
                and transition PostInit(p_map, s_map).
              }
            | W2 => { 
                send ReadCASReg.D.cas_req(p, oget (oget s_map.[p]).`vars.`x, oget (oget s_map.[p]).`arg)
                and transition PostInit(p_map, s_map).
              }
            | W3 => { 
                new_port_map <- rem p_map p;
                new_state_map <- rem s_map p;
                send IO_Init.D.rsp(p, Write, None)@(oget p_map.[p])
                and transition PostInit(new_port_map, new_state_map).
              }
            end
          }
        }
      | ReadCASReg.D.read_rsp(p, v) => { 
          match (oget s_map.[p]).`pc with
          | R1 => { 
              new_vars <- {| x = Some v |};
              new_state_map <- s_map.[p <- {| (oget s_map.[p]) with pc = R2; vars = new_vars |}];
              send Sched_Adv.A.suspend
              and transition PostInit(p_map, new_state_map).
            }
          | W1 => {
              new_vars <- {| x = Some v |};
              new_state_map <- s_map.[p <- {| (oget s_map.[p]) with pc = W2; vars = new_vars |}];
              send Sched_Adv.A.suspend
              and transition PostInit(p_map, new_state_map).
            }
          | R2 => { fail. }
          | W2 => { fail. }
          | W3 => { fail. }
          end
        }
      | ReadCASReg.D.cas_rsp(p, b) => { 
          match (oget s_map.[p]).`pc with
          | W2 => { 
              if (b) {
                new_state_map <- s_map.[p <- {| (oget s_map.[p]) with pc = W3 |}];
                send Sched_Adv.A.suspend
                and transition PostInit(p_map, new_state_map).
              }
              else {
                new_state_map <- s_map.[p <- {| (oget s_map.[p]) with pc = W1 |}];
                send Sched_Adv.A.suspend
                and transition PostInit(p_map, new_state_map).
              } 
            }
          | R1 => { fail. }
          | R2 => { fail. }
          | W1 => { fail. }
          | W3 => { fail. }
          end
        }
      | * => { fail. }
      end
    }
  }
}

adversarial Sched_Adv_Ideal {
  out initialized
  in initialization_ok
  out suspend
  in linearize(p : process)
  in allow_return(p : process)
}

functionality ReadWriteGeneric_Ideal implements IO_Init Sched_Adv_Ideal {
  (* TODO: send and transition of initial state of ideal functionality with adversarial
     interface must send adversarial message (to simulator if there is one,
     otherwise to adversary) *)
  initial state Init {
    match message with
    | pt@IO_Init.I.initialize(v) => {
        send Sched_Adv_Ideal.initialized
        and transition WaitingInit(pt, v).
      }
    | * => { fail. }
    end
  }
  state WaitingInit(init_pt : port, init_val : int) {
    match message with
    | Sched_Adv_Ideal.initialization_ok => {
        send IO_Init.I.initialized@init_pt
        and transition PostInit(init_val, empty, empty).
      }
    | * => { fail. }
    end
  }
  state PostInit(cur_val : int, p_map : port_map, is_map : ideal_state_map) {
    var new_port_map : port_map;
    var new_is_map : ideal_state_map;
    match message with
    | pt@IO_Init.D.inv(p, oper, arg) => {
        if (p \in p_map) { fail. }
        elif (p \in is_map) { fail. }
        else {
          match oper with
          | Read => { 
              match arg with 
              | Some v => { fail. }
              | None => { 
                  new_port_map <- p_map.[p <- pt];
                  new_is_map <- is_map.[p <- {| idlst_act = Invoked; 
                                                idlst_op = Read;
                                                idlst_arg = None; 
                                                idlst_ret = None |}];
                  send Sched_Adv_Ideal.suspend
                  and transition PostInit(cur_val, new_port_map, new_is_map).
                }
              end
            }
          | Write => { 
              match arg with 
              | Some v => { 
                  new_port_map <- p_map.[p <- pt];
                  new_is_map <- is_map.[p <- {| idlst_act = Invoked; 
                                                idlst_op = Write; 
                                                idlst_arg = Some v; 
                                                idlst_ret = None |}];
                  send Sched_Adv_Ideal.suspend
                  and transition PostInit(cur_val, new_port_map, new_is_map).
                }
              | None => { fail. }
              end
            }
          end
        }
      }
    | Sched_Adv_Ideal.linearize(p) => {
        if (p \notin p_map) { fail. }
        elif (p \notin is_map) { fail. }
        elif ((oget is_map.[p]).`idlst_act = Linearized) { fail. }
        else {
          match (oget is_map.[p]).`idlst_op with
          | Read => { 
              new_is_map <- is_map.[p <- {| (oget is_map.[p]) with 
                                            idlst_act = Linearized;
                                            idlst_ret = Some cur_val |}];
              send Sched_Adv_Ideal.suspend
              and transition PostInit(cur_val, p_map, new_is_map).
            }
          | Write => { 
              new_is_map <- is_map.[p <- {| (oget is_map.[p]) with 
                                            idlst_act = Linearized |}];
              send Sched_Adv_Ideal.suspend
              and transition PostInit(oget (oget is_map.[p]).`idlst_arg, p_map, new_is_map).
            }
          end
        }
      }
    | Sched_Adv_Ideal.allow_return(p) => {
        if (p \notin p_map) { fail. }
        elif (p \notin is_map) { fail. }
        elif ((oget is_map.[p]).`idlst_act <> Linearized) { fail. }
        else {
          new_port_map <- rem p_map p;
          new_is_map <- rem is_map p;
          send IO_Init.D.rsp(p, (oget is_map.[p]).`idlst_op, (oget is_map.[p]).`idlst_ret)@(oget p_map.[p])
          and transition PostInit(cur_val, new_port_map, new_is_map).
        }
      }
    | * => { fail. }
    end
  }
}

simulator Sim uses Sched_Adv_Ideal simulates ReadWriteGeneric {
  initial state Init {
    match message with
    | * => { fail. }
    end
  }
}


