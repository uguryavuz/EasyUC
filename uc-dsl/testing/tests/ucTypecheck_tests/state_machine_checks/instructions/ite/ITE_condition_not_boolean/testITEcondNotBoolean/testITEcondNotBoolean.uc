direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     sender@D.D.bla() => {if (sender) {send G.D.bla() and transition I.} else {fail.}}
   | * => {fail.}
   end
  }
 }
}