#include "share/HATS/temptory_staload_bucs320.hats"

#include "./../mylibies.hats"

// re-open in this scope
#staload $BINHEAP

(* ****** ****** *)

implement main1 () = let
//
impltmp
gcompare$ref<int>(x,y) =
  // NOTE: inverted!
  if (x < y) then 1 else if (x > y) then ~1 else 0
//
var h: HEAPNODE0
//
val () = heap_make_nil<int> (h, (i2sz)10)
val () = heap_push<int> (h, 5)
val () = heap_push<int> (h, 4)
val () = heap_push<int> (h, 3)
val () = heap_push<int> (h, 100)
val () = heap_push<int> (h, 6)
val () = heap_push<int> (h, 10)
//
val () = assertloc (heap_front (h) = 100)
val _ = heap_pop (h)
val () = assertloc (heap_front (h) = 10)
val _ = heap_pop (h)
val () = assertloc (heap_front (h) = 6)
val _ = heap_pop (h)
val () = assertloc (heap_front (h) = 5)
val _ = heap_pop (h)
val () = assertloc (heap_front (h) = 4)
val _ = heap_pop (h)
val () = assertloc (heap_front (h) = 3)
val _ = heap_pop (h)
//
val () = heap_free (h)
//
in
  0
end
