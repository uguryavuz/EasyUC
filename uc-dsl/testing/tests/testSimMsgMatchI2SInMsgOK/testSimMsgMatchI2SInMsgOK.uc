direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial iio {
in  i2sbla()
out i2sbli()
}

functionality R(F:D) implements D {

 party P serves D.D {

  initial state In {
  match message with * => {fail.} end
  }
 }
}

functionality I() implements D iio {

  initial state In {
  match message with * => {fail.} end
  }
}

simulator S uses iio simulates R(I) {

 initial state In {
  match message with iio.i2sbli() => {fail.} end
 }

}
