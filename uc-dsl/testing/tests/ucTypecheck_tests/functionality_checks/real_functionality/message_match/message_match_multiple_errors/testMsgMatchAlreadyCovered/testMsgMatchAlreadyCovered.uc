direct D_ {
in x@bla()
out bli()@x
}

direct D {D:D_}

adversarial A_ {
in  bla()
out bli()
}

adversarial A {A:A_}

functionality F implements D A_ {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
}


functionality S(X:D) implements D A {

 subfun F=F

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     sender@D.D.bla => {fail.}
   | D.D.* => {fail.}
   | X.D.bli => {fail.}
   | X.D.* => {fail.}
   | F.D.bli => {fail.}
   | F.D.* => {fail.}
   | A.A.bla => {fail.}
   | A.A.* => {fail.}
   | * => {fail.}
   end
  }
 }
}
