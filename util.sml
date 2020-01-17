(* -------------------- Notation -------------------- *)

infix &
infixr 9 o 
infixr 5 ++

(* -------------------- Basics -------------------- *)

exception NotFound

datatype cmp = Lt | Eq | Gt

datatype 'a opt = None | Some of 'a

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b

datatype ('a, 'b) prod = & of 'a * 'b

fun (f o g) x = f (g x)

fun opt susp = Some(susp()) handle _ => None

(*
Naming
- For some signature M,
    signature MkM = minimal definitions needed to make an M
    functor MkM(M : MkM) : M = build M from minimal definitions
    signature M' = M extended with various helper functions
    functor MkM'(M : M) : M' = build M' from M
    structure FooM : M = a Foo-y implementation of M
- f_ might raise; f returns opt
*)

(* -------------------- Semigroup & co. -------------------- *)

signature Sgp = sig
  type ('x, 'y, 'z) t (* 'x, 'y, 'z for extra info since no HKTs *)
  val dot : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> ('x, 'y, 'z) t
end

signature Mnd = sig
  include Sgp
  val e : ('x, 'y, 'z) t
end

signature Grp = sig
  include Sgp
  val e : ('x, 'y, 'z) t
  val inv : ('x, 'y, 'z) t -> ('x, 'y, 'z) t
end

(* -------------------- Semigroup & co. instances -------------------- *)

(* Lex monoid for comparisons *)
structure MndCmp : Mnd = struct
  type ('x, 'y, 'z) t = cmp
  fun dot(Eq, x) = x
    | dot(x, _) = x
  val e = Eq
end

(* + group *)
structure GrpAddInt : Grp = struct
  type ('x, 'y, 'z) t = int
  val dot = op+
  val e = 0
  val inv = op~
end

(* * monoid *)
structure MndMulInt : Mnd = struct
  type ('x, 'y, 'z) t = int
  val dot = op*
  val e = 1
end

(* List monoid *)
structure MndList : Mnd = struct
  type ('x, 'y, 'a) t = 'a list
  val dot = List.@
  val e = []
end

(* Endo monoid *)
structure MndEndo : Mnd = struct
  type ('x, 'y, 'a) t = 'a -> 'a
  val dot = (op o)
  fun e x = x
end

(* ---------- Products ---------- *)

functor SgpTup(structure A : Sgp; structure B : Sgp) : Sgp = struct
  type ('x, 'y, 'z) t = ('x, 'y, 'z) A.t * ('x, 'y, 'z) B.t
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
  type ('x, 'y, 'z, 'a) f (* A functor in 'a *)
  val map : ('a -> 'b) * ('x, 'y, 'z, 'a) f -> ('x, 'y, 'z, 'b) f
end

signature Fun1 = sig
  type 'a f
  val map : ('a -> 'b) * 'a f -> 'b f
end

functor MkFun(F : Fun1) : Fun = struct
  type ('x, 'y, 'z, 'a) f = 'a F.f
  val map = F.map
end

(* -------------------- Applicative -------------------- *)

signature App = sig
  include Fun
  val ret : 'a -> ('x, 'y, 'z, 'a) f
  val ap : ('x, 'y, 'z, 'a -> 'b) f * ('x, 'y, 'z, 'a) f -> ('x, 'y, 'z, 'b) f
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
  val bind : ('x, 'y, 'z, 'a) f * ('a -> ('x, 'y, 'z, 'b) f) -> ('x, 'y, 'z, 'b) f
end

signature Mon1 = sig
  include App1
  val bind : 'a f * ('a -> 'b f) -> 'b f
end

signature MkMon = sig
  type ('x, 'y, 'z, 'a) f
  val ret : 'a -> ('x, 'y, 'z, 'a) f
  val bind : ('x, 'y, 'z, 'a) f * ('a -> ('x, 'y, 'z, 'b) f) -> ('x, 'y, 'z, 'b) f
end

functor MkMon1(M : Mon1) : Mon =
  let structure S = MkApp(M) in
    struct
      open S
      val bind = M.bind
    end
  end

functor MkMon(M : MkMon) : Mon = struct
  type ('x, 'y, 'z, 'a) f = ('x, 'y, 'z, 'a) M.f
  val ret = M.ret
  val bind = M.bind
  fun map(f, mx) = bind(mx, fn x => ret(f x))
  fun ap(mf, mx) = bind(mf, fn f => map(f, mx))
end

(* -------------------- FMA instances -------------------- *)

structure MonOpt : Mon = MkMon(
  type ('x, 'y, 'z, 'a) f = 'a opt
  val ret = Some
  fun bind(Some x, f) = f x
    | bind _ = None
)

structure MonSum : Mon = MkMon(
  type ('x, 'y, 'a, 'b) f = ('a, 'b) sum
  val ret = Inr
  fun bind(Inr x, f) = f x
    | bind(Inl x, _) = Inl x
)

structure MonList : Mon = MkMon(
  type ('x, 'y, 'z, 'a) f = 'a list
  fun ret x = [x]
  fun bind(xs, f) = List.concat (List.map f xs)
)

signature CPS = sig
  include Mon
  val run : ('x, 'y, 'a, 'a) f -> 'a
  val shift : (('a -> 'r) -> 'r) -> ('x, 'y, 'r, 'a) f
  val reset : ('x, 'y, 'a, 'a) f -> ('x, 'y, 'r, 'a) f
end

structure MonCPS : CPS = let
  structure M = MkMon(
    type ('x, 'y, 'r, 'a) f = ('a -> 'r) -> 'r
    fun ret x k = k x
    fun bind(m, f) k = m(fn x => f x k)
  )
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
  type ('x, 'y, 'z) t
  val le : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
  val lt : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
  val eq : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
  val ne : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
  val ge : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
  val gt : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
end

signature MkOrd = sig
  type ('x, 'y, 'z) t
  val le : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
  val eq : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> bool
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
  val cmp : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> cmp opt
end

signature MkPOrd = sig
  type ('x, 'y, 'z) t
  val cmp : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> cmp opt
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
  val cmp : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> cmp
end

signature MkTOrd = sig
  type ('x, 'y, 'z) t
  val cmp : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> cmp
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

structure TOrdBool : TOrd = MkTOrd(
  type ('x, 'y, 'z) t = bool
  fun cmp(false, true) = Lt
    | cmp(true, false) = Gt
    | cmp _ = Eq
)

structure TOrdInt : TOrd = MkTOrd(
  type ('x, 'y, 'z) t = int
  fun cmp(x, y) = if x < y then Lt else if x = y then Eq else Gt
)

structure TOrdChar : TOrd = MkTOrd(
  type ('x, 'y, 'z) t = char
  fun cmp xy =
    case Char.compare xy
    of LESS => Lt
     | EQUAL => Eq
     | GREATER => Gt
)

functor TOrdTup(structure A : TOrd; structure B : TOrd) : TOrd = MkTOrd(
  type ('x, 'y, 'z) t = ('x, 'y, 'z) A.t * ('x, 'y, 'z) B.t
  fun cmp((x1, y1), (x2, y2)) =
    case A.cmp(x1, x2)
    of Eq => B.cmp(y1, y2)
     | r => r
)

functor TOrdSum(structure A : TOrd; structure B : TOrd) : TOrd = MkTOrd(
  type ('x, 'y, 'z) t = (('x, 'y, 'z) A.t, ('x, 'y, 'z) B.t) sum
  fun cmp(Inl _, Inr _) = Lt
    | cmp(Inr _, Inl _) = Gt
    | cmp(Inl x, Inl y) = A.cmp(x, y)
    | cmp(Inr x, Inr y) = B.cmp(x, y)
)

functor TOrdOpt(structure A : TOrd) : TOrd = MkTOrd(
  type ('x, 'y, 'z) t = ('x, 'y, 'z) A.t opt
  fun cmp(None, Some _) = Lt
    | cmp(None, None) = Eq
    | cmp(Some _, None) = Gt
    | cmp(Some x, Some y) = A.cmp(x, y)
)

functor TOrdList(A : TOrd) : TOrd = MkTOrd(
  type ('x, 'y, 'a) t = ('x, 'y, 'a) A.t list
  fun cmp([], []) = Eq
    | cmp([], _::_) = Lt
    | cmp(_::_, []) = Gt
    | cmp(x::xs, y::ys) = case A.cmp(x, y) of Eq => cmp(xs, ys) | c => c
)

(* -------------------- Lattices -------------------- *)

signature Semilattice = sig
  include POrd
  val join : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> ('x, 'y, 'z) t
end

signature Lattice = sig
  include Semilattice
  val meet : ('x, 'y, 'z) t * ('x, 'y, 'z) t -> ('x, 'y, 'z) t
end

functor TOrdLattice(M : MkTOrd) : Lattice = let
  structure P = MkPOrd(
    type ('x, 'y, 'z) t = ('x, 'y, 'z) M.t
    fun cmp xy = Some(M.cmp xy)
  )
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
  fun cons(x, ts as (v, l)::(w, r)::ts') =
      if v = w
      then ((1 + v + w, Node(l, x, r))::ts')
      else (1, Leaf x)::ts
    | cons(x, ts) = (1, Leaf x)::ts

  (* O(1) *)
  fun ucons_[] = raise Empty
    | ucons_((1, Leaf x)::ts) = (x, ts)
    | ucons_((w, Node(l, x, r))::ts) = (x, (w div 2, l)::(w div 2, r)::ts)
    | ucons_((_, _)::_) = raise RListInternal

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
    | get_((w, t)::ts, i) = if i < w then get_tree_(w, t, i) else get_(ts, i - w)

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
    | upd_((w, t)::ts, i, f) =
      if i < w
      then (w, upd_tree_(w, t, i, f))::ts
      else (w, t)::upd_(ts, i - w, f)

  fun set_(xs, i, y) = upd_(xs, i, fn _ => y)

  fun get xsi = Some(get_ xsi) handle Index => None
  fun upd xsif = Some(upd_ xsif) handle Index => None
  fun set xsiy = Some(set_ xsiy) handle Index => None
end

(* -------------------- Non-memoizing lazy lists -------------------- *)

(* Use linearly! *)
structure LList :> sig
  type 'a t
  val sus : (unit -> ('a * 'a t) opt) -> 'a t
  val go : 'a t -> ('a * 'a t) opt
  val emp : 'a t
  val cons : 'a * 'a t -> 'a t
  val app : 'a t * 'a t -> 'a t
  val map : ('a -> 'b) * 'a t -> 'b t
  val foldr : 'a t * 'b * ('a * 'b -> 'b) -> 'b
  val foldl : 'a t * 'b * ('b * 'a -> 'b) -> 'b
end = struct
  datatype 'a t
    = LList of unit -> ('a * 'a t) opt
    | App of 'a t * 'a t
  val sus = LList
  val emp = LList(fn _ => None)
  fun cons xxs = LList(fn _ => Some xxs)
  fun go(LList xs) = xs()
    | go(App(xs, ys)) = case go xs of None => go ys | r => r
  val app = App
  fun map(f : 'a -> 'b, LList xs) =
      LList (fn _ =>
        case xs()
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

structure MonLList : Mon = MkMon(
  open LList
  type ('x, 'y, 'z, 'a) f = 'a t
  fun ret x = cons(x, emp)
  fun bind(xs, f) = foldr(map(f, xs), emp, app)
)


(* -------------------- Representing one type as another -------------------- *)

signature Rep = sig
  type ('x, 'y, 'z) t
  type ('x, 'y, 'z) rep
  val rep : ('x, 'y, 'z) t -> ('x, 'y, 'z) rep
end

(* -------------------- Tree-like data -------------------- *)

signature Tree = sig
  include Rep (* Representation of one recursive 'layer' *)
  (* A lazy list of immediate subtrees *)
  val subs : ('x, 'y, 'z) t -> ('x, 'y, 'z) t LList.t
end

structure TreeList = struct
  type ('x, 'y, 'a) t = 'a list
  type ('x, 'y, 'a) rep = 'a opt
  fun subs[] = LList.emp
    | subs(_::xs) = LList.cons(xs, LList.emp)
  fun rep[] = None
    | rep(x::_) = Some x
end

(* -------------------- Functional maps -------------------- *)

functor MapFn(
  type ('x, 'y, 'z) k
  val eq : ('x, 'y, 'z) k -> ('x, 'y, 'z) k -> bool
) : sig
  type ('x, 'y, 'z) k (* The type of keys *)
  type ('x, 'y, 'z, 'a) t
  val emp : ('x, 'y, 'z, 'a) t
  val get : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> 'a opt
  val get_ : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> 'a
  val set : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k * 'a -> ('x, 'y, 'z, 'a) t
  val upd : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k * ('a -> 'a) -> ('x, 'y, 'z, 'a) t
  val del : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> ('x, 'y, 'z, 'a) t
  val adj : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k * ('a opt -> 'a opt) -> ('x, 'y, 'z, 'a) t
  val union : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z, 'a) t -> ('x, 'y, 'z, 'a) t
  val inter : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z, 'a) t -> ('x, 'y, 'z, 'a) t
  val diff : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z, 'a) t -> ('x, 'y, 'z, 'a) t
  val map : ('a -> 'b) * ('x, 'y, 'z, 'a) t -> ('x, 'y, 'z, 'b) t
end = struct
  type ('x, 'y, 'z) k = ('x, 'y, 'z) k
  type ('x, 'y, 'z, 'a) t = ('x, 'y, 'z) k -> 'a
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

(* -------------------- Maps -------------------- *)

signature MkMap = sig
  type ('x, 'y, 'z) k (* The type of keys *)
  type ('x, 'y, 'z, 'a) t
  val emp : ('x, 'y, 'z, 'a) t
  val get_ : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> 'a
  val adj : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k * ('a opt -> 'a opt) -> ('x, 'y, 'z, 'a) t
end

signature Map = sig
  include MkMap
  val has : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> bool
  val get : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> 'a opt
  val set : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k * 'a -> ('x, 'y, 'z, 'a) t
  val del : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k -> ('x, 'y, 'z, 'a) t
  val upd : ('x, 'y, 'z, 'a) t * ('x, 'y, 'z) k * ('a -> 'a) -> ('x, 'y, 'z, 'a) t
end

functor MkMap(M : MkMap) : Map = struct
  open M
  fun get mx = Some(get_ mx) handle NotFound => None
  fun has mx = case get mx of Some _ => true | None => false
  fun set(m, x, v) = adj(m, x, fn _ => Some v)
  fun del(m, x) = adj(m, x, fn _ => None)
  fun upd(m, x, f) = adj(m, x, fn mv => MonOpt.map(f, mv))
end

(* Map for keys k representable as A.rep *)
functor MapRep(
  structure A : Rep
  structure M : MkMap where type ('x, 'y, 'z) k = ('x, 'y, 'z) A.rep
) : Map = MkMap(
  type ('x, 'y, 'z) k = ('x, 'y, 'z) A.t
  type ('x, 'y, 'z, 'a) t = ('x, 'y, 'z, 'a) M.t
  val emp = M.emp
  fun get_(m, x) = M.get_(m, A.rep x)
  fun adj(m, x, f) = M.adj(m, A.rep x, f)
)

(* ---------- 'Data-structural boot-strapping' for tries ---------- *)

structure MapUnit : Map = MkMap(
  type ('x, 'y, 'z) k = unit
  type ('x, 'y, 'z, 'a) t = 'a opt
  val emp = None
  fun get_(Some v, _) = v
    | get_(None, _) = raise NotFound
  fun adj(v, _, f) = f v
)

functor MapProd(structure A : MkMap; structure B : MkMap) : Map = MkMap(
  type ('x, 'y, 'z) k = ('x, 'y, 'z) A.k * ('x, 'y, 'z) B.k
  type ('x, 'y, 'z, 'a) t = ('x, 'y, 'z, ('x, 'y, 'z, 'a) B.t) A.t
  val emp = A.emp
  fun get_(m, (x, y)) = B.get_(A.get_(m, x), y)
  fun adj(m, (x, y), f) =
    A.adj(m, x,
     fn None => Some(B.adj(B.emp, y, f))
      | Some m => Some(B.adj(m, y, f)))
)

functor MapSum(structure A : MkMap; structure B : MkMap) : Map = MkMap(
  type ('x, 'y, 'z) k = (('x, 'y, 'z) A.k, ('x, 'y, 'z) B.k) sum
  type ('x, 'y, 'z, 'a) t = ('x, 'y, 'z, 'a) A.t * ('x, 'y, 'z, 'a) B.t
  val emp = (A.emp, B.emp)
  fun get_((m, _), Inl x) = A.get_(m, x)
    | get_((_, m), Inr x) = B.get_(m, x)
  fun adj((ma, mb), Inl x, f) = (A.adj(ma, x, f), mb)
    | adj((ma, mb), Inr x, f) = (ma, B.adj(mb, x, f))
)

functor MapLList(A : MkMap) : Map = MkMap(
  type ('x, 'y, 'z) k = ('x, 'y, 'z) A.k LList.t
  datatype ('x, 'y, 'z, 'a) t = M of 'a opt * ('x, 'y, 'z, ('x, 'y, 'z, 'a) t) A.t
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
)

functor MapOpt(A' : MkMap) : Map = MapRep(
  structure A = struct
    type ('x, 'y, 'z) t = ('x, 'y, 'z) A'.k opt
    type ('x, 'y, 'z) rep = (unit, ('x, 'y, 'z) A'.k) sum
    fun rep None = Inl()
      | rep(Some v) = Inr v
  end
  structure M = MapSum(structure A = MapUnit; structure B = A')
)

functor MapTree(
  structure T : Tree
  (* A map for one "layer" of the tree-like structure *)
  structure M : MkMap where type ('x, 'y, 'z) k = ('x, 'y, 'z) T.rep
) : Map = MkMap(
  structure L = MapLList(MapOpt(MapRep(structure A = T; structure M = M)))
  structure LL = LList

  type ('x, 'y, 'z) k = ('x, 'y, 'z) T.t
  datatype ('x, 'y, 'z, 'a) t = M of ('x, 'y, 'z, 'a opt * ('x, 'y, 'z, 'a) t) L.t

  fun smush xs =
    let open MonLList in
      bind(xs,
       fn Some x => LL.cons(None, map(Some, T.subs x))
        | None => LL.emp)
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
      case LL.go(smush xs) & r
      of None & Some(v, m) => Some(f v, m)
       | None & None => Some(f None, M L.emp)
       | Some(x, xs) & Some(v, m) => Some(v, adj_l(m, LL.cons(x, xs), f))
       | Some(x, xs) & None => Some(None, adj_l(emp, LL.cons(x, xs), f))))
  fun adj(m, x, f) = adj_l(m, LL.cons(Some x, LL.emp), f)
)

(* ---------- Maps for common types ---------- *)

structure MapBool : Map = MapRep(
  structure A = struct
    type ('x, 'y, 'z) t = bool
    type ('x, 'y, 'z) rep = (unit, unit) sum
    fun rep p = if p then Inl() else Inr()
  end
  structure M = MapSum(structure A = MapUnit; structure B = MapUnit)
)

functor MapList(A : MkMap) : Map = MapTree(
  structure T = struct
    type ('x, 'y, 'z) t = ('x, 'y, 'z) A.k list
    type ('x, 'y, 'z) rep = ('x, 'y, 'z) A.k opt
    val subs = TreeList.subs
    val rep = TreeList.rep
  end
  structure M = MapOpt(A)
)

(* Slow int map for now *)
structure MapInt : Map = MapTree(
  structure T = struct
    type ('x, 'y, 'z) t = int
    type ('x, 'y, 'z) rep = bool
    fun subs 0 = LList.emp
      | subs n = LList.cons(n div 2, LList.emp)
    fun rep n = case n mod 2 of 1 => true | _ => false
  end
  structure M = MapBool
)

(* -------------------- Tests -------------------- *)

structure Tests = struct
  exception Chk
  fun chk(x, y) : unit = if x = y then () else raise Chk
  structure CPSTests = struct
    structure C = MonCPS
    fun product[] = C.ret 1
      | product(0::xs) = C.shift(fn _ => 0)
      | product(x::xs) = C.map(fn y => x*y, product xs)
    val _ = chk(12, C.run(product[2, 2, 3]))
    val _ = chk(0, C.run(product[1, 2, 0, 3]))
    val _ = chk(0, C.run(C.map(fn x => x + 3, product[1, 2, 0, 3])))
    val _ = chk(3, C.run(C.map(fn x => x + 3, C.reset(product [1, 2, 0, 3]))))
    fun find_zero[] = C.ret false
      | find_zero(0::_) = C.shift(fn _ => true)
      | find_zero(_::xs) = find_zero xs
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
  structure ListTrie = struct
    structure M = MapList(MapUnit)
    val _ = chk(None, M.get(M.emp, []))
    val _ = chk(Some 3, M.get(M.set(M.emp, [], 3), []))
    val _ =
      let val xs = [(), (), ()] in
        chk(Some 4, M.get(M.set(M.set(M.emp, xs, 4), [], 3), xs));
        chk(Some 3, M.get(M.set(M.set(M.emp, xs, 4), xs, 3), xs))
      end
    structure M = MapList(MapProd(structure A = MapInt; structure B = MapBool))
    val _ = chk(None, M.get(M.emp, []))
    val _ = chk(Some 3, M.get(M.set(M.emp, [], 3), []))
    val _ =
      let
        val xs = [(1, true), (2, false), (3, false)]
        val ys = [(1, true), (2, false), (4, false)]
      in
        chk(Some 4, M.get(M.set(M.set(M.emp, xs, 4), [], 3), xs));
        chk(Some 3, M.get(M.set(M.set(M.emp, xs, 4), xs, 3), xs));
        chk(Some 3, M.get(M.set(M.set(M.emp, xs, 4), ys, 3), ys));
        chk(None, M.get(M.set(M.set(M.emp, xs, 4), xs, 3), ys))
      end
  end
  structure LCTrie = struct
    structure LC = struct
      datatype term = Var of int | Lam of term | App of term * term
    end
    structure M = MapTree(
      structure T = struct
        open LC
        type ('x, 'y, 'z) t = term
        type ('x, 'y, 'z) rep = (int, bool) sum
        fun subs(Var _) = LList.emp
          | subs(Lam e) = LList.cons(e, LList.emp)
          | subs(App(e1, e2)) = LList.cons(e1, LList.cons(e2, LList.emp))
        fun rep(Var i) = Inl i
          | rep(Lam _) = Inr true
          | rep(App _) = Inr false
      end
      structure M = MapSum(structure A = MapInt; structure B = MapBool)
    )
    val _ =
      let
        open LC
        val i = Lam(Var 0)
        val k = Lam(Lam(Var 1))
        val s = Lam(Lam(Lam(App(App(Var 2, Var 0), App(Var 1, Var 0)))))
        val b = Lam(Lam(Lam(App(Var 2, App(Var 1, Var 0)))))
      in
        chk(Some 3, M.get(M.set(M.emp, b, 3), b));
        chk(Some 2, M.get(M.set(M.set(M.set(M.emp, k, 2), i, 0), b, 3), k));
        chk(None, M.get(M.set(M.set(M.set(M.emp, k, 2), i, 0), b, 3), s))
      end
  end
end
