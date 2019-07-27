#include "share/HATS/temptory_staload_bucs320.hats"

#staload "./SATS/array_prf.sats"
#staload LIBC_STRING = "./SATS/libc_string.sats"

#staload "./SATS/strbuf.sats"

#staload UN = "libats/SATS/unsafe.sats"

implfun
main0 () = {
//
fun init (): void = {
  var p_sbf : b0ytes(50)
  val (pf_sbf | ()) = strbuf_of_bytes (view@ p_sbf | addr@ p_sbf)  
  prval () = view@ p_sbf := bytes_of_strbuf pf_sbf
}
fun init_substring (): void = {
  var sbf : b0ytes(50)
  val p_sbf = addr@ sbf
  val () = strbuf_of_substring (
    view@ sbf | p_sbf, "hello, world", i2sz 7, i2sz 5
  )
  
  #define get(x,i) strbuf_test_char_at_size(!(x), i2sz i)

  val () = assertloc ('w' = get(p_sbf, 0))
  val () = assertloc ('o' = get(p_sbf, 1))
  val () = assertloc ('r' = get(p_sbf, 2))
  val () = assertloc ('l' = get(p_sbf, 3))
  val () = assertloc ('d' = get(p_sbf, 4))
  val () = assertloc ('\0' = get(p_sbf, 5))
  
  prval () = view@ sbf := bytes_of_strbuf (view@ sbf)
}
//
fun get_set (): void = {
  var sbf : b0ytes(50)
  val p_sbf = addr@ sbf
  val () = strbuf_of_string (
    view@ sbf | p_sbf, "hello, world", i2sz 12
  )
  
  #define get(x,i) strbuf_get_char_at(!(x), i2sz i)
  #define set(x,i,c) strbuf_set_char_at(!(x), i2sz i, c)

  val () = assertloc ('h' = get(p_sbf, 0))
  val () = assertloc ('e' = get(p_sbf, 1))
  val () = assertloc ('l' = get(p_sbf, 2))
  val () = assertloc ('l' = get(p_sbf, 3))
  val () = assertloc ('o' = get(p_sbf, 4))

  val () = set(p_sbf, 5, ';')
  val () = assertloc (';' = get(p_sbf, 5))  
  
  prval () = view@ sbf := bytes_of_strbuf (view@ sbf)
}
//
val () = init ()
val () = init_substring ()
val () = get_set ()
  // append string to sbf
  // append something else
  // start all over from the start, unconsing stuff in a loop, printing

}
