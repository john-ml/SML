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

functor TOrdLattice(M : TOrd) : Lattice = let
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

(* -------------------- Tests -------------------- *)

structure Tests = struct
  exception Chk
  fun chk(x, y) = if x = y then () else raise Chk
  structure C = MonCPS
  fun product[] = C.ret 1
    | product(0 :: xs) = C.shift(fn _ => 0)
    | product(x :: xs) = C.bind(product xs, fn y => C.ret(x*y))
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
end
