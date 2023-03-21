uc_requires Sub.

direct D' {
  in x@bla()
  out bli()@x
}

direct D {D:D'}

adversarial I {
  in  bla()
  out bli()
}

functionality IF() implements D I {
  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
}

functionality RF(Foo : Sub.D) implements D {
 party P serves D.D {
  initial state Is {
  match message with * => {fail.} end
  }
 }
}

simulator S uses I simulates RF(Sub.IF) {

  initial state Is {
  match message with I.* => {fail.} end
  }
}

