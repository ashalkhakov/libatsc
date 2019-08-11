// NOTE: based on this code: https://gist.github.com/martinkunev/1365481

fun{T:vtflt}
gcompare$ptr {l1,l2:addr} (!T @ l1, !T @ l2 | ptr l1, ptr l2): int

(* ****** ****** *)

typedef HEAPNODE (a:tflt, m:int, n:int, l:addr) = @{
    size= size m,
    count= size n,
    data= ptr l
}

(* ****** ****** *)

absvtflt heap (a:tflt+,m:int,n:int,l:addr) = HEAPNODE (a, m, n, l)
vtypedef heap (a:tflt, m:int,n:int) = [l:addr] heap (a, m, n, l)


fun{a:tflt}
heap_init {m:pos} (&heap (INV(a), 0, 0, null)? >> heap (a, m, 0, l), size m): #[l:addr] void

fun{a:tflt}
heap_term {m,n:int;l:addr} (&heap (INV(a), m, n, l) >> heap (a, 0, 0, null)?): void

fun{a:tflt}
heap_push {m,n:int;l:addr | n < m} (
  &heap (a, m,n, l) >> heap (a, m, n+1, l), INV(a)
): void

fun{a:tflt}
heap_pop {m,n:int;l:addr | n > 0} (&heap (INV(a),m,n,l) >> heap (a, m,n-1,l)): void

fun{a:tflt}
heap_front {m,n:int;l:addr | n > 0} (&heap (INV(a), m, n, l) >> _): a

fun
heap_isnot_full {a:tflt} {m,n:int;l:addr} (
  &heap (a, m, n, l) >> _
): bool (n < m)

fun{a:tflt}
heap_resize {m,m1,n:int;l:addr | n <= m1} (
  &heap (INV(a), m, n, l) >> heap (a, m1, n, l1), size m1
): #[l1:addr] void
