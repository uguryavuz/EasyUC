ec_requires KeysExponentsAndPlainTexts.

direct a {
in x@bla()
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    * => {fail.}
   end
  }
 
  state II(k:kye) {
   match message with
    * => {fail.}
   end
  }
 }
}
