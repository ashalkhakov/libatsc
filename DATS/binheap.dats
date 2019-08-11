#staload
"libats/SATS/array.sats"
#staload
_ = "libats/DATS/array.dats"
#staload
"libats/SATS/gint.sats"
#staload
_ = "libats/DATS/gint.dats"

#staload
UN = "libats/SATS/unsafe.sats"

#staload
"./../SATS/array_prf.sats"
#staload
"./../SATS/pointer.sats"
#staload
_ = "./../DATS/pointer.dats"
#staload
"./../SATS/binheap.sats"
#staload LIBC_STRING = "./../SATS/libc_string.sats"

(* ****** ****** *)

extern
prfun
lemma_size_param {i:int} (size(i)): [i>=0] void

(* ****** ****** *)

impltmp{T}
gcompare$ptr {l1,l2} (pf1, pf2 | p1, p2) = gcompare$ref<T>(!p1, !p2)

(* ****** ****** *)

dataprop myprop (int,int) = {m,n:int | m >= n} MYPROP (m, n)

absimpl heap (T:tflt, m:int, n:int, l:addr) = (
  array_v (T, l, n),
  array_v (T?, l+n*sizeof(T), m-n),
  mfree_gc_v (l),
  myprop (m, n)
| HEAPNODE (T, m, n, l)
)

impltmp{T}
heap_init (h, sz) = {
  val (pf_arr, pf_gc | p_arr) = array_ptr_alloc<T> (sz)
  prval () = h.0 := array_v_nil {T} ()
  prval () = h.1 := pf_arr
  prval () = h.2 := pf_gc
  prval () = h.3 := MYPROP ()
  val () = h.4.size := sz
  val () = h.4.count := (i2sz)0
  val () = h.4.data := p_arr
}

impltmp{T}
heap_term (h) = {
  prval pf1_arr = h.0
  prval pf2_arr = h.1
  prval pf_gc = h.2
  prval MYPROP () = h.3
  
  prval pf1_arr = __trustme (pf1_arr) where { extern prfun __trustme {n:int;l:addr} (array_v (T,l,n)): array_v (T?,l,n) }
  
  prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
  val p_arr = h.4.data
  val () = array_ptr_mfree (pf_arr, pf_gc | p_arr)

  prval () = h.3 := unit_p ()
  val () = h.4.size := (i2sz)0
  val () = h.4.count := (i2sz)0
  val () = h.4.data := the_null_ptr
}

impltmp{T}
heap_push {m,n,l} (h, v) = {
  // Find out where to put the element and put it
  fun
  aux {l:addr} {i,n1:nat | i <= n1} (
    pf1_arr: array_v (T, l, i)
  , pf_at: T? @ l+i*sizeof(T)
  , pf2_arr: array_v (T, l+(i+1)*sizeof(T), n1-i)
  | base: ptr l, index: size i, n1: size n1
  ): [i1:nat | i1 <= i] (
    array_v (T, l, i1), T? @ l+i1*sizeof(T), array_v (T, l+(i1+1)*sizeof(T), n1-(i1))
  | size i1
  ) =
    if index = 0 then let
    in
      (pf1_arr, pf_at, pf2_arr | index)
    end else let
      val parent = pred (index) // parent0 >=0
      val parent = parent / ((i2sz)2)
      val (pf1_at, fpf | p_parent) = array_ptr_takeout<T> (pf1_arr | base, parent)
      var v = v
      val res = gcompare$ptr<T> (pf1_at, view@v | p_parent, addr@v) < 0
      prval pf1_arr = fpf (pf1_at)
    in
      if res then let
      in
        (pf1_arr, pf_at, pf2_arr | index)
      end else let
        // need to split pf1_arr by parent into pf11_arr, pf1_at, pf12_arr
        // and then, to assign:
        prval (pf11_arr, pf12_arr) = array_v_split_at (pf1_arr | parent)
        prval (pf1_at, pf12_arr) = array_v_uncons (pf12_arr)
        val p_index = ptr1_add<T> (base, index)
        val p_parent = ptr1_add<T> (base, parent)
        // so data[index] is now initialized
        var v_parent = !p_parent
        val () = !p_index := v_parent
        // but data[parent] is now un-initialized...
        prval pf2_arr = array_v_unsplit (pf12_arr, array_v_cons (pf_at, pf2_arr))
      in
        aux (pf11_arr, pf1_at, pf2_arr | base, parent, n1)
      end
    end

  val count = h.4.count
  val base = h.4.data

  prval pf1_arr = h.0
  prval pf3_arr = h.1
  prval MYPROP () = h.3

  prval (pf_at, pf3_arr) = array_v_uncons (pf3_arr)
  prval pf2_arr = array_v_nil ()
  //
  prval () = __trustme () where { extern prfun __trustme (): [n>=0] void }
  //
  val (pf1_arr, pf_at, pf2_arr | index) = aux (pf1_arr, pf_at, pf2_arr | base, count, count)
  val p_index = ptr1_add<T> (base, index)
  val () = !p_index := v
  prval pf2_arr = array_v_cons (pf_at, pf2_arr)
  //
  val () = h.4.count := succ(count)
  prval () = h.0 := array_v_unsplit (pf1_arr, pf2_arr)
  prval () = h.1 := pf3_arr
  prval () = h.3 := MYPROP ()
}

impltmp{T}
heap_pop {m,n,l} (h) = {
  // Remove the biggest element
  val count = h.4.count
  val count = pred(count)
  val base = h.4.data

  prval pf1_arr = h.0
  prval pf2_arr = h.1
  prval MYPROP () = h.3

  val () = h.4.count := count
  val p_temp = ptr1_add<T> (base, count)
  prval (pf1_arr, pf_temp) = array_v_unextend {T} (pf1_arr)

  // Reorder the elements
  fun
  aux {n,i:nat | i < n} {l,l1:addr} (
    pf_arr: !array_v (T, l, n)
  , pf_tmp: !T @ l1
  | data: ptr l, index: size i, count: size n,
    p_tmp: ptr l1
  ): [i1: nat | i1 < n] size i1 = let
    // Find the child to swap with
    val swap = (index + index) + (i2sz)1
  in
    if swap >= count then index // If there are no children, the heap is reordered
    else let
      val other = swap + (i2sz)1
      val swap =
        (if other < count then (
           if gcompare$ref<T> (!data.[other], !data.[swap]) < 0 then other
           else swap
        ) else swap) : Sizelt(n)
      //
      prval () = lemma_size_param (swap)
      
      val (pf1_at, fpf | p_swap) = array_ptr_takeout<T> (pf_arr | data, swap)
      val res = gcompare$ptr<T> (pf_tmp, pf1_at | p_tmp, p_swap) < 0
      prval () = pf_arr := fpf (pf1_at)
    in
      if res then index // If the bigger child is less than or equal to its parent, the heap is reordered
      else let
        val () = !data.[index] := !data.[swap]
      in
        aux (pf_arr, pf_tmp | data, swap, count, p_tmp)
      end
    end
  end
  // AS: guess I fixed a bug here!
  val () =
    if count > 0 then {
      val index = aux (pf1_arr, pf_temp | base, (i2sz)0, count, p_temp)
      val temp = !p_temp
      val () = array_set_at_size<T> (!base, index, temp)
    }

  prval () = h.0 := pf1_arr
    
  prval pf2_arr = array_v_cons (pf_temp, pf2_arr)
  prval () = h.1 := pf2_arr
  prval () = h.3 := MYPROP ()
}

impltmp{T}
heap_front {m,n,l} (h) = res where {
  val count = h.4.count
  val base = h.4.data

  prval pf1_arr = h.0
  prval (pf_at, pf1_arr) = array_v_uncons (pf1_arr)
  prval pf2_arr = h.1
  prval MYPROP () = h.3

  val p_index = base
  val res = !p_index
  prval pf1_arr = array_v_cons (pf_at, pf1_arr)
  //
  prval () = h.0 := pf1_arr
  prval () = h.1 := pf2_arr
  prval () = h.3 := MYPROP ()
} (* end of [heap_front] *)

implfun
heap_isnot_full {a} {m,n,l} (h) = res where {
  val count = h.4.count
  val size = h.4.size
  prval MYPROP () = h.3
  val res = count < size
} (* end of [heap_isnot_full] *)

impltmp{T}
heap_resize {m,m1,n,l} (h, size) = {
  val p11_arr = h.4.data

  prval pf11_arr = h.0
  prval pf12_arr = h.1
  prval pf_gc = h.2
  prval MYPROP () = h.3

  prval () = lemma_array_v_param (pf11_arr)

  val (pf2_arr, pf2_gc | p2_arr) = array_ptr_alloc<T> (size)

  prval (pf21_arr, pf22_arr) = array_v_split_at (pf2_arr | h.4.count)

  val nb = (h.4.count)*sizeof<T>
  val (pf11_arr, pf21_arr | _) =
    $LIBC_STRING.memcpy (pf11_arr, pf21_arr | p2_arr, p11_arr, nb)

  prval pf1_arr = array_v_unsplit (pf11_arr, pf12_arr)
  val () = array_ptr_mfree (pf1_arr, pf_gc | p11_arr)

  val () = h.4.size := size
  val () = h.4.data := p2_arr
  prval () = h.0 := pf21_arr
  prval () = h.1 := pf22_arr
  prval () = h.2 := pf2_gc
  prval () = h.3 := MYPROP ()
} (* end of [heap_resize] *)

(* ****** ****** *)
