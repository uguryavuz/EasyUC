direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

adversarial Iio {
in  bla()
out bli()
}

functionality R(F:D) implements D {

 party P serves D.D {

  initial state In {
  match message with *  => {fail.} end
  }
 }
}

functionality I() implements D Iio {

  initial state In {
  match message with * => {fail.} end
  }
}

simulator S uses Iio simulates R(I) {

 initial state In {
  match message with Iio.* => {fail.} end
 }

 state II() {
  match message with
  R.F.Iio.bla() => {fail.}
  | * => {fail.}
  end
 }

}