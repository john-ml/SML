(* -------------------- Notation -------------------- *)

infix &
infixr 9 o 
infixr 5 ++

(* -------------------- Basics -------------------- *)

datatype cmp = Lt | Eq | Gt

datatype 'a opt = None | Some of 'a

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b

datatype ('a, 'b) prod = & of 'a * 'b

fun (f o g) x = f (g x)

fun opt susp = Some(susp()) handle _ => None

(*
Naming scheme: for some signature M,
  signature MkM = minimal definitions needed to make an M
  functor MkM(M : MkM) : M = build M from minimal definitions
  signature M' = M extended with various helper functions
  functor MkM'(M : M) : M' = build M' from M
  structure FooM : M = a Foo-y implementation of M
*)

(* -------------------- Semigroup & co. -------------------- *)

signature Sgp = sig
  type 'a t (* 'a for extra info since no HKTs *)
  val dot : 'a t * 'a t -> 'a t
end

signature Mnd = sig
  include Sgp
  val e : 'a t
end

signature Grp = sig
  include Sgp
  val e : 'a t
  val inv : 'a t -> 'a t
end

(* -------------------- Semigroup & co. instances -------------------- *)

(* Lex monoid for comparisons *)
structure MndCmp : Mnd = struct
  type 'e t = cmp
  fun dot(Eq, x) = x
    | dot(x, _) = x
  val e = Eq
end

(* + group *)
structure GrpAddInt : Grp = struct
  type 'e t = int
  val dot = op+
  val e = 0
  val inv = op~
end

(* * monoid *)
structure MndMulInt : Mnd = struct
  type 'e t = int
  val dot = op*
  val e = 1
end

(* List monoid *)
structure MndList : Mnd = struct
  type 'a t = 'a list
  val dot = List.@
  val e = []
end

(* Endo monoid *)
structure MndEndo : Mnd = struct
  type 'a t = 'a -> 'a
  val dot = (op o)
  fun e x = x
end

(* ---------- Products ---------- *)

functor SgpTup(structure A : Sgp; structure B : Sgp) : Sgp = struct
  type 'e t = 'e A.t * 'e B.t
  fun dot((x1, y1), (x2, y2)) = (A.dot(x1, x2), B.dot(y1, y2))
end

functor MndTup(structure A : Mnd; structure B : Mnd) : Mnd = let
  structure S = SgpTup(structure A = A; structure B = B)
in
  struct
    open S
    val e = (A.e, B.e)
  end
end

functor GrpTup(structure A : Grp; structure B : Grp) : Grp = let
  structure S = MndTup(structure A = A; structure B = B)
in
  struct
    open S
    fun inv(x, y) = (A.inv x, B.inv y)
  end
end

(* -------------------- Functor -------------------- *)

signature Fun = sig
  type ('e, 'a) f (* A functor in 'a. 'e for extra info since no HKTs *)
  val map : ('a -> 'b) * ('e, 'a) f -> ('e, 'b) f
end

signature Fun1 = sig
  type 'a f
  val map : ('a -> 'b) * 'a f -> 'b f
end

functor MkFun(F : Fun1) : Fun = struct
  type ('e, 'a) f = 'a F.f
  val map = F.map
end

(* -------------------- Applicative -------------------- *)

signature App = sig
  include Fun
  val ret : 'a -> ('e, 'a) f
  val ap : ('e, 'a -> 'b) f * ('e, 'a) f -> ('e, 'b) f
end

signature App1 = sig
  include Fun1
  val ret : 'a -> 'a f
  val ap : ('a -> 'b) f * 'a f -> 'b f
end

functor MkApp(F : App1) : App =
  let structure S = MkFun(F) in
    struct
      open S
      val ret = F.ret
      val ap = F.ap
    end
  end

(* -------------------- Monad -------------------- *)

signature Mon = sig
  include App
  val bind : ('e, 'a) f * ('a -> ('e, 'b) f) -> ('e, 'b) f
end

signature Mon1 = sig
  include App1
  val bind : 'a f * ('a -> 'b f) -> 'b f
end

signature MkMon = sig
  type ('e, 'a) f
  val ret : 'a -> ('e, 'a) f
  val bind : ('e, 'a) f * ('a -> ('e, 'b) f) -> ('e, 'b) f
end

functor MkMon1(M : Mon1) : Mon =
  let structure S = MkApp(M) in
    struct
      open S
      val bind = M.bind
    end
  end

functor MkMon(M : MkMon) : Mon = struct
  type ('e, 'a) f = ('e, 'a) M.f
  val ret = M.ret
  val bind = M.bind
  fun map(f, mx) = bind(mx, fn x => ret(f x))
  fun ap(mf, mx) = bind(mf, fn f => map(f, mx))
end

(* -------------------- FMA instances -------------------- *)

structure MonOpt : Mon = MkMon(struct
  type ('e, 'a) f = 'a opt
  val ret = Some
  fun bind(Some x, f) = f x
    | bind _ = None
end)

structure MonSum : Mon = MkMon(struct
  type ('e, 'a) f = ('e, 'a) sum
  val ret = Inr
  fun bind(Inr x, f) = f x
    | bind(Inl x, _) = Inl x
end)

structure MonList : Mon = MkMon(struct
  type ('e, 'a) f = 'a list
  fun ret x = [x]
  fun bind(xs, f) = List.concat (List.map f xs)
end)

structure MonSt : Mon = MkMon(struct
  type ('e, 'a) f = 'e -> 'e * 'a
  fun ret x s = (s, x)
  fun bind(m, f) s = let val (s, x) = m s in f x s end
end)

signature CPS = sig
  include Mon
  val run : ('a, 'a) f -> 'a
  val shift : (('a -> 'r) -> 'r) -> ('r, 'a) f
  val reset : ('a, 'a) f -> ('r, 'a) f
end

structure MonCPS : CPS = let
  structure M = MkMon(struct
    type ('r, 'a) f = ('a -> 'r) -> 'r
    fun ret x k = k x
    fun bind(m, f) k = m(fn x => f x k)
  end)
in
  struct
    open M
    fun run m = m(fn x => x)
    fun shift f k = f k
    fun reset m k = k(run m)
  end
end

(* -------------------- Orders -------------------- *)

signature Ord = sig
  type 'a t
  val le : 'a t * 'a t -> bool
  val lt : 'a t * 'a t -> bool
  val eq : 'a t * 'a t -> bool
  val ne : 'a t * 'a t -> bool
  val ge : 'a t * 'a t -> bool
  val gt : 'a t * 'a t -> bool
end

signature MkOrd = sig
  type 'a t
  val le : 'a t * 'a t -> bool
  val eq : 'a t * 'a t -> bool
end

functor MkOrd(M : MkOrd) : Ord = struct
  open M
  fun ne xy = not(eq xy)
  fun lt xy = le xy andalso ne xy
  fun gt xy = not(le xy)
  fun ge xy = not(lt xy)
end

(* -------------------- Partial orders -------------------- *)

signature POrd = sig
  include Ord
  val cmp : 'a t * 'a t -> cmp opt
end

signature MkPOrd = sig
  type 'a t
  val cmp : 'a t * 'a t -> cmp opt
end

functor MkPOrd(M : MkPOrd) : POrd = struct
  open M
  fun le xy = case cmp xy of Some Lt => true | Some Eq => true | _ => false
  fun lt xy = case cmp xy of Some Lt => true | _ => false
  fun eq xy = case cmp xy of Some Eq => true | _ => false
  fun ne xy = case cmp xy of Some Lt => true | Some Gt => true | _ => false
  fun ge xy = case cmp xy of Some Gt => true | Some Eq => true | _ => false
  fun gt xy = case cmp xy of Some Gt => true | _ => false
end

(* -------------------- Total orders -------------------- *)

signature TOrd = sig
  include Ord
  val cmp : 'a t * 'a t -> cmp
end

signature MkTOrd = sig
  type 'a t
  val cmp : 'a t * 'a t -> cmp
end

functor MkTOrd(M : MkTOrd) : TOrd = struct
  open M
  fun le xy = case cmp xy of Lt => true | Eq => true | _ => false
  fun lt xy = case cmp xy of Lt => true | _ => false
  fun eq xy = case cmp xy of Eq => true | _ => false
  fun ne xy = case cmp xy of Lt => true | Gt => true | _ => false
  fun ge xy = case cmp xy of Gt => true | Eq => true | _ => false
  fun gt xy = case cmp xy of Gt => true | _ => false
end

structure TOrdBool : TOrd = MkTOrd(struct
  type 'a t = bool
  fun cmp(false, true) = Lt
    | cmp(true, false) = Gt
    | cmp _ = Eq
end)

structure TOrdInt : TOrd = MkTOrd(struct
  type 'a t = int
  fun cmp(x, y) = if x < y then Lt else if x = y then Eq else Gt
end)

structure TOrdChar : TOrd = MkTOrd(struct
  type 'a t = char
  fun cmp xy =
    case Char.compare xy
    of LESS => Lt
     | EQUAL => Eq
     | GREATER => Gt
end)

functor TOrdList(A : TOrd) : TOrd = MkTOrd(struct
  type 'a t = 'a A.t list
  fun cmp([], []) = Eq
    | cmp([], _ :: _) = Lt
    | cmp(_ :: _, []) = Gt
    | cmp(x :: xs, y :: ys) = case A.cmp(x, y) of Eq => cmp(xs, ys) | c => c
end)

(* -------------------- Lattices -------------------- *)

signature Semilattice = sig
  include POrd
  val join : 'a t * 'a t -> 'a t
end

signature Lattice = sig
  include Semilattice
  val meet : 'a t * 'a t -> 'a t
end

functor TOrdLattice(M : MkTOrd) : Lattice = let
  structure P = MkPOrd(struct
    type 'a t = 'a M.t
    fun cmp xy = Some(M.cmp xy)
  end)
in
  struct
    open P
    fun join(x, y) = case M.cmp(x, y) of Lt => y | _ => x
    fun meet(x, y) = case M.cmp(x, y) of Gt => y | _ => x
  end
end

(* -------------------- Okasaki's skew-binary random-access lists -------------------- *)

signature RList = sig
  type 'a t
  exception Index
  exception Empty
  val emp : 'a t
  val cons : 'a * 'a t -> 'a t
  val ucons : 'a t -> ('a * 'a t) opt
  val hd : 'a t -> 'a opt
  val tl : 'a t -> 'a t opt
  val get : 'a t * int -> 'a opt
  val set : 'a t * int * 'a -> 'a t opt
  val upd : 'a t * int * ('a -> 'a) -> 'a t opt
  val ucons_ : 'a t -> 'a * 'a t
  val hd_ : 'a t -> 'a
  val tl_ : 'a t -> 'a t
  val get_ : 'a t * int -> 'a
  val set_ : 'a t * int * 'a -> 'a t
  val upd_ : 'a t * int * ('a -> 'a) -> 'a t
end

structure RList :> RList = struct
  datatype 'a tree = Leaf of 'a | Node of 'a tree * 'a * 'a tree
  type 'a t = (int * 'a tree) list
  exception Empty
  exception Index
  exception RListInternal

  val emp = []

  (* O(1) *)
  fun cons(x, ts as (v, l) :: (w, r) :: ts') =
      if v = w
      then ((1 + v + w, Node(l, x, r)) :: ts')
      else (1, Leaf x) :: ts
    | cons(x, ts) = (1, Leaf x) :: ts

  (* O(1) *)
  fun ucons_[] = raise Empty
    | ucons_((1, Leaf x) :: ts) = (x, ts)
    | ucons_((w, Node(l, x, r)) :: ts) = (x, (w div 2, l) :: (w div 2, r) :: ts)
    | ucons_((_, _) :: _) = raise RListInternal

  fun hd_ xs = let val (x, _) = ucons_ xs in x end
  fun tl_ xs = let val (_, xs) = ucons_ xs in xs end

  fun ucons xs = Some (ucons_ xs) handle Empty => None
  fun hd xs = Some (hd_ xs) handle Empty => None
  fun tl xs = Some (tl_ xs) handle Empty => None

  fun get_tree_(1, Leaf x, 0) = x
    | get_tree_(1, Leaf _, _) = raise Index
    | get_tree_(_, Node(_, x, _), 0) = x
    | get_tree_(w, Node(l, x, r), i) =
      let val i = i - 1 in
        if i < w div 2
        then get_tree_(w div 2, l, i)
        else get_tree_(w div 2, r, i - w div 2)
      end
    | get_tree_ _ = raise RListInternal

  (* O(min(i, log(n))) *)
  fun get_([], _) = raise Index
    | get_((w, t) :: ts, i) = if i < w then get_tree_(w, t, i) else get_(ts, i - w)

  fun upd_tree_(1, Leaf x, 0, f) = Leaf(f x)
    | upd_tree_(1, Leaf _, _, _) = raise Index
    | upd_tree_(_, Node(l, x, r), 0, f) = Node(l, f x, r)
    | upd_tree_(w, Node(l, x, r), i, f) =
      let val i = i - 1 in
        if i < w div 2
        then Node(upd_tree_(w div 2, l, i, f), x, r)
        else Node(l, x, upd_tree_(w div 2, r, i - w div 2, f))
      end
    | upd_tree_ _ = raise RListInternal

  (* O(min(i, log(n))) *)
  fun upd_([], _, _) = raise Index
    | upd_((w, t) :: ts, i, f) =
      if i < w
      then (w, upd_tree_(w, t, i, f)) :: ts
      else (w, t) :: upd_(ts, i - w, f)

  fun set_(xs, i, y) = upd_(xs, i, fn _ => y)

  fun get xsi = Some(get_ xsi) handle Index => None
  fun upd xsif = Some(upd_ xsif) handle Index => None
  fun set xsiy = Some(set_ xsiy) handle Index => None
end

(* -------------------- Lazy lists -------------------- *)

(* Use linearly! Does not memoize! *)
structure LList = struct
  datatype 'a t = LList of unit -> ('a * 'a t) opt | App of 'a t * 'a t
  val emp = LList(fn _ => None)
  fun cons xxs = LList(fn _ => Some xxs)
  fun go(LList xs) = xs()
    | go(App(xs, ys)) = case go xs of None => go ys | r => r
  val app = App
  fun map(f : 'a -> 'b, xs as LList _) =
      LList (fn _ =>
        case go xs
        of Some(x, xs) => Some(f x, map(f, xs))
         | None => None)
    | map(f, App(xs, ys)) = App(map(f, xs), map(f, ys))
  fun foldr(xs, e, f) =
    case go xs
    of None => e
     | Some(x, xs) => f(x, foldr(xs, e, f))
  fun foldl(xs, e, f) =
    case go xs
    of None => e
     | Some(x, xs) => foldl(xs, f(e, x), f)
end

(* Use linearly! Does not memoize! *)
structure MonLList : Mon = MkMon(struct
  open LList
  type ('e, 'a) f = 'a t
  fun ret x = cons(x, emp)
  fun bind(xs, f) = foldl(map(f, xs), emp, app)
end)

(* -------------------- Functor fixpoints -------------------- *)

signature Fix = sig
  include Fun
  datatype 'e t = Fix of ('e, 'e t) f
  val fold : 'e t * (('e, 'a) f -> 'a) -> 'a
end

signature FixExt = sig
  include Fix
  val subs : 'e t -> 'e t LList.t
end

(* -------------------- Map sigs -------------------- *)

(* A minimal signature for maps *)
signature Map = sig
  exception NotFound
  type 'e k (* The type of keys *)
  type ('e, 'a) t
  val emp : ('e, 'a) t
  val get_ : ('e, 'a) t * 'e k -> 'a
  val adj : ('e, 'a) t * 'e k * ('a opt -> 'a opt) -> ('e, 'a) t
end

(* An extended signature for maps *)
signature ExtMap = sig
  exception NotFound
  type 'e k (* The type of keys *)
  type ('e, 'a) t
  val emp : ('e, 'a) t
  val get : ('e, 'a) t * 'e k -> 'a opt
  val get_ : ('e, 'a) t * 'e k -> 'a
  val set : ('e, 'a) t * 'e k * 'a -> ('e, 'a) t
  val upd : ('e, 'a) t * 'e k * ('a -> 'a) -> ('e, 'a) t
  val del : ('e, 'a) t * 'e k -> ('e, 'a) t
  val adj : ('e, 'a) t * 'e k * ('a opt -> 'a opt) -> ('e, 'a) t
  val union : ('e, 'a) t * ('e, 'a) t -> ('e, 'a) t
  val inter : ('e, 'a) t * ('e, 'a) t -> ('e, 'a) t
  val diff : ('e, 'a) t * ('e, 'a) t -> ('e, 'a) t
  val map : ('a -> 'b) * ('e, 'a) t -> ('e, 'b) t
end

(* -------------------- Map structs -------------------- *)

(* Functional maps *)
functor ExtMapFun(type 'e k; val eq : 'e k -> 'e k -> bool) : ExtMap = struct
  exception NotFound
  type 'e k = 'e k
  type ('e, 'a) t = 'e k -> 'a
  fun emp _ = raise NotFound
  fun get_(m, k) = m k
  fun get(m, k) = Some(get_(m, k)) handle NotFound => None
  fun set(m, k, v) k' = if eq k k' then v else m k'
  fun upd(m, k, f) k' = if eq k k' then f(m k') else m k'
  fun del(m, k) k' = if eq k k' then raise NotFound else m k'
  fun adj(m, k, f) k' =
    case f(get(m, k))
    of Some v => v
     | None => raise NotFound
  fun union(m, n) k = m k handle NotFound => n k
  fun inter(m, n) k = let val r = m k val _ = n k in r end
  fun diff(m, n) k =
    case m k & get(n, k)
    of v & None => v
     | _ => raise NotFound
  fun map(f, m) k = f(m k)
end

(* Map for unit *)
structure MapUnit : Map = struct
  exception NotFound
  type 'e k = unit
  type ('e, 'a) t = 'a opt
  val emp = None
  fun get_(Some v, _) = v
    | get_(None, _) = raise NotFound
  fun adj(v, _, f) = f v
end

(* Map for product *)
functor MapProd(structure A : Map; structure B : Map) : Map = struct
  exception NotFound
  type 'e k = 'e A.k * 'e B.k
  type ('e, 'a) t = ('e, ('e, 'a) B.t) A.t
  val emp = A.emp
  fun get_(m, (x, y)) = B.get_(A.get_(m, x), y)
  fun adj(m, (x, y), f) =
    A.adj(m, x,
     fn None => Some(B.adj(B.emp, y, f))
      | Some m => Some(B.adj(m, y, f)))
end

(* Map for sum *)
functor MapSum(structure A : Map; structure B : Map) : Map = struct
  exception NotFound
  type 'e k = ('e A.k, 'e B.k) sum
  type ('e, 'a) t = ('e, 'a) A.t * ('e, 'a) B.t
  val emp = (A.emp, B.emp)
  fun get_((m, _), Inl x) = A.get_(m, x)
    | get_((_, m), Inr x) = B.get_(m, x)
  fun adj((ma, mb), Inl x, f) = (A.adj(ma, x, f), mb)
    | adj((ma, mb), Inr x, f) = (ma, B.adj(mb, x, f))
end

(* Map for opt *)
functor MapOpt(A : Map) : Map = struct
  exception NotFound
  type 'e k = 'e A.k opt
  type ('e, 'a) t = 'a opt * ('e, 'a) A.t
  val emp = (None, A.emp)
  fun get_((Some v, _), None) = v
    | get_((None, _), None) = raise NotFound
    | get_((_, m), Some x) = A.get_(m, x)
  fun adj((v, m), None, f) = (f v, m)
    | adj((v, m), Some x, f) = (v, A.adj(m, x, f))
end

(* Map for list *)
functor MapList(A : Map) : Map = struct
  exception NotFound
  type 'e k = 'e A.k list
  datatype ('e, 'a) t = M of 'a opt * ('e, ('e, 'a) t) A.t
  val emp = M(None, A.emp)
  fun get_(M(Some v, _), []) = v
    | get_(M(_, m), x::xs) = get_(A.get_(m, x), xs)
    | get_ _ = raise NotFound
  fun adj(M(v, m), [], f) = M(f v, m)
    | adj(M(v, m), x::xs, f) =
      M(v, A.adj(m, x,
       fn Some m => Some(adj(m, xs, f))
        | None => Some(adj(emp, xs, f))))
end

(* Map for lazy list *)
functor MapLList(A : Map) : Map = struct
  exception NotFound
  type 'e k = 'e A.k LList.t
  datatype ('e, 'a) t = M of 'a opt * ('e, ('e, 'a) t) A.t
  val emp = M(None, A.emp)
  fun get_(m, xs) =
    case m & LList.go xs
    of M(Some v, _) & None => v
     | M(_, m) & Some(x, xs) => get_(A.get_(m, x), xs)
     | _ => raise NotFound
  fun adj(m, xs, f) =
    case m & LList.go xs
    of M(v, m) & None => M(f v, m)
     | M(v, m) & Some(x, xs) =>
       M(v, A.adj(m, x,
        fn Some m => Some(adj(m, xs, f))
         | None => Some(adj(emp, xs, f))))
end

(* Map from fixpoints *)
signature MapFixExtArg = sig
  structure F : FixExt
  (* A map for one "layer" of F.f *)
  structure M : Map where type 'e k = 'e F.t
end
functor MapFixExt(M : MapFixExtArg) : Map = struct
  exception NotFound
  structure L = MapLList(MapOpt(M.M))
  structure LL = LList

  type 'e k = 'e M.F.t
  datatype ('e, 'a) t = M of ('e, 'a opt * ('e, 'a) t) L.t

  fun smush xs =
    let open MonLList in
      bind(xs, fn Some x => LL.cons(None, map(Some, M.F.subs x)) | None => LL.emp)
    end

  val emp = M L.emp

  fun get_l_(M m, xs) =
    case L.get_(m, xs) & LL.go(smush xs)
    of (Some v, _) & None => v
     | (None, _) & None => raise NotFound
     | (_, m) & Some(x, xs) => get_l_(m, LL.cons(x, xs))
  fun get_(m, x) = get_l_(m, LL.cons(Some x, LL.emp))

  fun adj_l(M m, xs, f) =
    M(L.adj(m, xs, fn r =>
      case r & LL.go(smush xs)
      of Some(v, m) & None => Some(f v, m)
       | Some(v, m) & Some(x, xs) => Some(v, adj_l(m, LL.cons(x, xs), f))
       | None & None => Some(f None, M L.emp)
       | None & Some(x, xs) => Some(None, adj_l(emp, LL.cons(x, xs), f))))
  fun adj(m, x, f) = adj_l(m, LL.cons(Some x, LL.emp), f)
end

signature ArgsMapRepr = sig
  structure A : sig
    type 'e k
    type 'e repr
    val repr : 'e k -> 'e repr
  end
  structure M : Map where type 'e k = 'e A.repr
end

functor MapRepr(X : ArgsMapRepr) : Map = struct
  open X
  open A
  exception NotFound
  type ('e, 'a) t = ('e, 'a) M.t
  val emp = M.emp
  fun get_(m, x) = M.get_(m, repr x)
  fun adj(m, x, f) = M.adj(m, repr x, f)
end

(* -------------------- Tests -------------------- *)

structure Tests = struct
  exception Chk
  fun chk(x, y) = if x = y then () else raise Chk
  structure CPSTests = struct
    structure C = MonCPS
    fun product[] = C.ret 1
      | product(0 :: xs) = C.shift(fn _ => 0)
      | product(x :: xs) = C.map(fn y => x*y, product xs)
    val _ = chk(12, C.run(product[2, 2, 3]))
    val _ = chk(0, C.run(product[1, 2, 0, 3]))
    val _ = chk(0, C.run(C.map(fn x => x + 3, product[1, 2, 0, 3])))
    val _ = chk(3, C.run(C.map(fn x => x + 3, C.reset(product [1, 2, 0, 3]))))
    fun find_zero[] = C.ret false
      | find_zero(0 :: _) = C.shift(fn _ => true)
      | find_zero(_ :: xs) = find_zero xs
    val _ = chk(false, C.run(find_zero[2, 2, 3]))
    val _ = chk(true, C.run(find_zero[1, 2, 0, 3]))
    val _ = chk(1, C.run(C.map(fn true => 1 | _ => 0, C.reset(find_zero[1, 2, 0, 3]))))
    structure L = RList
    val xs = L.cons(1, L.cons(2, L.cons(3, L.emp)))
  end
  (*
  structure PolyRecTests = struct
    datatype 'a tup = End | Tup of 'a * ('a * 'a) tup
    fun ('a, 'b) map(f : 'a -> 'b, xs : 'a tup) : 'b tup =
      case xs
      of End => End
       | Tup(x, xs) => Tup(f x, map(fn(x, y) => (f x, f y), xs))
  end *)
  structure ListTrieTests = struct
    structure ListF = struct
      datatype ('e, 'a) f = NilF | ConsF of 'e * 'a
      datatype 'e t = Fix of ('e, 'e t) f
      fun map(_, NilF) = NilF
        | map(f, ConsF(x, xs)) = ConsF(x, f xs)
      val emp = Fix NilF
      fun cons(x, xs) = Fix(ConsF(x, xs))
      fun fold(Fix xs, g) = g(map(fn x => fold(x, g), xs))
      fun subs(Fix NilF) = LList.emp
        | subs(Fix(ConsF(_, xs))) = LList.cons(xs, LList.emp)
    end
    structure MapUnitListF : Map = MapRepr(struct
      structure A = struct
        open ListF
        type 'e k = unit t
        type 'e repr = unit opt
        fun repr(Fix NilF) = None
          | repr(Fix(ConsF(x, _))) = Some x
      end
      structure M = MapOpt(MapUnit)
    end)
    structure M = MapUnitListF
    structure L = ListF
    val _ = chk(0, M.get_(M.emp, L.emp) handle NotFound => 0)
    val _ = chk(3, M.get_(M.adj(M.emp, L.emp, fn _ => Some 3), L.emp) handle NotFound => 0)
    val _ =
      let val xs = L.cons((), L.cons((), L.cons((), L.emp))) in
        chk(4,
          M.get_(
            M.adj(M.adj(M.emp, xs, fn _ => Some 4), L.emp, fn _ => Some 3),
            xs) handle NotFound => 0);
        chk(3,
          M.get_(
            M.adj(M.adj(M.emp, xs, fn _ => Some 4), xs, fn _ => Some 3),
            xs) handle NotFound => 0)
      end
  end
end
