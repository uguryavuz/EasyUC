direct a {
in  x@bla(u:univ)
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    bla(k) => {	decode k as int * int with
                  ok x =>{fail.}
		| error=>{fail.}
		end
	      }
   |othermsg => {fail.}
   end
  }
 }
}
