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
          if (dom p_map p) { fail. }
          elif (dom s_map p) { fail. }
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
          if (!dom p_map p) { fail. }
          elif (!dom s_map p) { fail. }
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
  out suspend
  in resume(p : process)
}

functionality ReadWriteGeneric_Ideal implements IO_Init Sched_Adv_Ideal {
  initial state Init {
    match message with
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


