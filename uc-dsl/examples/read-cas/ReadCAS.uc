ec_requires +Process.

direct ReadCAS_Dir' {
  in pt@read_req(p : process)
  out read_rsp(p : process, v : int)@pt
  in pt@cas_req(p : process, old : int, new : int)
  out cas_rsp(p : process, b : bool)@pt
}

direct Initialize {
  in pt@initialize(v : int)
  out initialized@pt
}

direct ReadCAS_Dir {
  D : ReadCAS_Dir'
  I : Initialize
}

functionality ReadCAS_Spec implements ReadCAS_Dir {
  initial state Init {
    match message with
    | pt@ReadCAS_Dir.I.initialize(v) => {
        send ReadCAS_Dir.I.initialized@pt
        and transition PostInit(v).
      }
    | * => { fail. }
    end
  }
  
  state PostInit(cur_val : int) {
    match message with 
    | pt@ReadCAS_Dir.D.read_req(p) => {
        send ReadCAS_Dir.D.read_rsp(p, cur_val)@pt
        and transition PostInit(cur_val).
      }
    | pt@ReadCAS_Dir.D.cas_req(p, old, new) => {
        if (old = cur_val) {
          send ReadCAS_Dir.D.cas_rsp(p, true)@pt
          and transition PostInit(new).
        }
        else {
          send ReadCAS_Dir.D.cas_rsp(p, false)@pt
          and transition PostInit(cur_val).
        }
      }
    | * => { fail. }
    end
  }
}