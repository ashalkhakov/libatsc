#staload
"libats/SATS/array.sats"
#staload
"libats/SATS/gint.sats"

#staload
UN = "libats/SATS/unsafe.sats"

#staload
"./../SATS/array_prf.sats"
#staload
"./../SATS/pointer.sats"
#staload
DA = "./../SATS/dynarray.sats"
#staload
"./../SATS/binheap.sats"
#staload LIBC_STRING = "./../SATS/libc_string.sats"

(* ****** ****** *)

extern
prfun
lemma_size_param {i:int} (size(i)): [i>=0] void

extern
prfun
array_v_split_at2 {a:vtflt} {l:addr} {n,i,j:int | i < n; j < n} (
  array_v (a, l, n)
| size i
, size j
):<> (
  a @ l+i*sizeof(a), a @ l+j*sizeof(a)
, (a @ l+i*sizeof(a), a @ l+j*sizeof(a)) -<lin,prf> array_v (a, l, n)
)

(* ****** ****** *)

impltmp{T}
gcompare$ptr {l1,l2} (pf1, pf2 | p1, p2) = gcompare$ref<T>(!p1, !p2)

(* ****** ****** *)

local

absimpl
heap_vtflt_int_tflt = $DA.dynarray

in

impltmp{T}
heap_make_nil (h, sz) = $DA.dynarray_make_nil (h, sz)

impltmp{T}
heap_free_tflt (h) = $DA.dynarray_free_tflt (h)

impltmp{T}
heap_free (h) = $DA.dynarray_free (h)

impltmp{T}
heap_front {n} (h) = $DA.dynarray_get_at_size (h, i2sz 0)

impltmp{T}
heap_getref_front {n} (h) = $DA.dynarray_getref_at_size (h, i2sz 0)

impltmp{}
heap_get_size {a}{n} (h) = $DA.dynarray_get_size (h)

impltmp{}
heap_get_capacity {a}{n} (h) = $DA.dynarray_get_capacity (h)

impltmp{T}
heap_push {n} (h, v) = {
  var v = v
  val p_v = addr@ v
  prval pf_v = view@ v

  // Find out where to put the element and put it
  fun
  aux {l:addr} {i,n1:nat | i <= n1} (
    pf1_arr: array_v (T, l, i)
  , pf_at: T? @ l+i*sizeof(T)
  , pf2_arr: array_v (T, l+(i+1)*sizeof(T), n1-i)
  , pf_v: !T @ v
  | base: ptr l, index: size i, n1: size n1
  ): [i1:nat | i1 <= i] (
    array_v (T, l, i1)
  , T? @ l+i1*sizeof(T)
  , array_v (T, l+(i1+1)*sizeof(T), n1-(i1))
  | size i1
  ) =
    if index = 0 then let
    in
      (pf1_arr, pf_at, pf2_arr | index)
    end else let
      val parent = pred (index) // parent0 >=0
      val parent = parent / ((i2sz)2)
      val (pf1_at, fpf | p_parent) = array_ptr_takeout<T> (pf1_arr | base, parent)
      val res = gcompare$ptr<T> (pf1_at, pf_v | p_parent, p_v) < 0
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
        val () = !p_index := !p_parent
        // but data[parent] is now un-initialized...
        prval pf2_arr = array_v_unsplit (pf12_arr, array_v_cons (pf_at, pf2_arr))
      in
        aux (pf11_arr, pf1_at, pf2_arr, pf_v | base, parent, n1)
      end
    end

  val count = $DA.dynarray_get_size (h)
  val count1 = succ(count)
  prval () = lemma_size_param (count)
  val _ = $DA.dynarray_reset_capacity (h, count1)
  
  val (pf1_arr, pf3_arr | base, cap, cnt) =
    $DA.dynarray_takeout_array {T}(h)
  
  val () = assert_errmsg (cap > count, "unable to resize dynarray")

  prval (pf_at, pf3_arr) = array_v_uncons (pf3_arr)
  prval pf2_arr = array_v_nil ()
  //
  prval () = lemma_size_param (count)
  //
  val (pf1_arr, pf_at, pf2_arr | index) = aux (pf1_arr, pf_at, pf2_arr, pf_v | base, count, count)
  prval () = view@ v := pf_v
  val p_index = ptr1_add<T> (base, index)
  val () = ptr_write<T> (pf_at | p_index, v)
  prval pf2_arr = array_v_cons (pf_at, pf2_arr)
  //
  prval pf_arr = array_v_unsplit (pf1_arr, pf2_arr)
  val () = $DA.dynarray_restore_array {T} (pf_arr, pf3_arr | h, cap, succ(cnt))
}

impltmp{T}
heap_pop {n} (h) = let
  // Remove the biggest element

  val (pf1_arr, pf2_arr | base, cap, count) =
    $DA.dynarray_takeout_array {T}(h)
  val count = pred(count)

  val p_temp = ptr1_add<T> (base, count)
  prval (pf1_arr, pf_temp) = array_v_unextend {T} (pf1_arr)

  // Reorder the elements
  fun
  aux {i,n1:nat | i <= n1} {l:addr} (
    pf_arr: array_v (T, l, n1)
  | data: ptr l, index: size i, count: size n1
  ): [i1: nat | i1 <= n1] (
    array_v (T, l, n1)
  | size i1
  ) = let  
    // Find the child to swap with
    val swap = index + index + (i2sz)1
  in
    if swap >= count then (
      // If there are no children, the heap is reordered
      (pf_arr | index)
    ) else let
      val other = swap + (i2sz)1
      prval () = lemma_size_param (other)
      val swap = (
        if other < count then let
          prval (pf_swap, pf_other, fpf) = array_v_split_at2 (pf_arr | swap, other)
          val p_other = ptr1_add<T> (data, other)
          val p_swap = ptr1_add<T> (data, swap)

          val res = gcompare$ptr<T> (pf_other, pf_swap | p_other, p_swap) < 0

          prval () = pf_arr := fpf (pf_swap, pf_other)          
        in
          if res then other
          else swap
        end else swap
      ) : [s:int | s > i; s < n1] size(s)
      //
      prval () = lemma_size_param (swap)
      
      val p_index = ptr1_add<T> (data, index)
      val p_swap = ptr1_add<T> (data, swap)
      prval (pf_index, pf_swap, fpf) = array_v_split_at2 (pf_arr | index, swap)
      
      val res = gcompare$ptr<T> (pf_index, pf_swap | p_index, p_swap) < 0
    in
      // If the bigger child is less than or equal to its parent, the heap is reordered
      if res then let
        prval () = pf_arr := fpf (pf_index, pf_swap)
      in
        (pf_arr | index)
      end else let
        var tmp = ptr_read<T> (pf_index | p_index)
        var swp = ptr_read<T>(pf_swap | p_swap)
        val () = ptr_write<T> (pf_index | p_index, swp)
        val () = ptr_write<T> (pf_swap | p_swap, tmp)
        prval () = pf_arr := fpf (pf_index, pf_swap)
      in
        aux (pf_arr | data, swap, count)
      end
    end
  end
  
  prval () = lemma_size_param (count)
in
  // AS: guess I fixed a bug here!
  if count = 0 then let
    val res = !p_temp
    prval pf2_arr = array_v_cons (pf_temp, pf2_arr)
    val () = $DA.dynarray_restore_array{T} (pf1_arr, pf2_arr | h, cap, count)
  in
    res
  end else let
    prval (pf_at, pf1_arr) = array_v_uncons (pf1_arr)
    val res = !base
    val () = !base := !p_temp
    prval pf1_arr = array_v_cons (pf_at, pf1_arr)
    val (pf1_arr | index) = aux (
      pf1_arr
    | base, (i2sz)0, count
    )
    prval pf2_arr = array_v_cons (pf_temp, pf2_arr)
    val () = $DA.dynarray_restore_array {T} (
      pf1_arr, pf2_arr
    | h, cap, count
    )
  in
    res
  end
end

impltmp{T}
heap_reset_capacity {n} (h, c) =
  $DA.dynarray_reset_capacity (h, c)

end

(* ****** ****** *)
