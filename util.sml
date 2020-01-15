datatype 'a opt = None | Some of 'a
datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
datatype cmp = Lt | Eq | Gt

(* -------------------- Fixpoint type -------------------- *)

signature Functor = sig
  type 'a f
  val map : ('a -> 'b) * 'a f -> 'b f
end

signature Fix = sig
  include Functor
  datatype t = Fix of t f
  val fold : ('a f -> 'a) * t -> 'a
end

functor Fix(M : Functor) : Fix = struct
  open M
  datatype t = Fix of t f
  fun fold(g, Fix fx) = g(map(fn x => fold(g, x), fx))
end

(* -------------------- Semigroup and friends -------------------- *)

signature Semigroup = sig
  type t
  val dot : t * t -> t
end

signature Monoid = sig
  include Semigroup
  val e : t
end

signature Group = sig
  include Semigroup
  val e : t
  val inv : t -> t
end

(* -------------------- Orded types -------------------- *)

signature Ord = sig
  type t
  val le : t * t -> bool
  val lt : t * t -> bool
  val eq : t * t -> bool
  val ne : t * t -> bool
  val ge : t * t -> bool
  val gt : t * t -> bool
end

signature MkOrd = sig
  type t
  val le : t * t -> bool
  val eq : t * t -> bool
end

functor MkOrd(M : MkOrd) : Ord = struct
  open M
  fun ne(x, y) = not(eq(x, y))
  fun lt(x, y) = le(x, y) andalso ne(x, y)
  fun gt(x, y) = not(le(x, y))
  fun ge(x, y) = not(lt(x, y))
end

(* -------------------- Partial orders -------------------- *)

signature PartialOrd = sig
  include Ord
  val cmp : t * t -> cmp opt
end

signature MkPartialOrd = sig
  type t
  val cmp : t * t -> cmp opt
end

functor MkPartialOrd(M : MkPartialOrd) : PartialOrd = struct
  open M
  fun le(x, y) = case cmp(x, y) of Some(Lt) => true | Some(Eq) => true | _ => false
  fun lt(x, y) = case cmp(x, y) of Some(Lt) => true | _ => false
  fun eq(x, y) = case cmp(x, y) of Some(Eq) => true | _ => false
  fun ne(x, y) = case cmp(x, y) of Some(Lt) => true | Some(Gt) => true | _ => false
  fun ge(x, y) = case cmp(x, y) of Some(Gt) => true | Some(Eq) => true | _ => false
  fun gt(x, y) = case cmp(x, y) of Some(Gt) => true | _ => false
end

(* -------------------- Total orders -------------------- *)

signature TotalOrd = sig
  include Ord
  val cmp : t * t -> cmp
end

signature MkTotalOrd = sig
  type t
  val cmp : t * t -> cmp
end

functor MkTotalOrd(M : MkTotalOrd) : TotalOrd = struct
  open M
  fun le(x, y) = case cmp(x, y) of Lt => true | Eq => true | _ => false
  fun lt(x, y) = case cmp(x, y) of Lt => true | _ => false
  fun eq(x, y) = case cmp(x, y) of Eq => true | _ => false
  fun ne(x, y) = case cmp(x, y) of Lt => true | Gt => true | _ => false
  fun ge(x, y) = case cmp(x, y) of Gt => true | Eq => true | _ => false
  fun gt(x, y) = case cmp(x, y) of Gt => true | _ => false
end

functor MkOrdProd(structure A : MkTotalOrd; structure B : MkTotalOrd) : TotalOrd = MkTotalOrd(struct
  type t = A.t * B.t
  fun cmp((x1, y1), (x2, y2)) =
    case A.cmp(x1, x2)
    of Eq => B.cmp(y1, y2)
     | c => c
end)

functor MkOrdSum(structure A : MkTotalOrd; structure B : MkTotalOrd) : TotalOrd = MkTotalOrd(struct
  type t = (A.t, B.t) sum
  fun cmp(Inl x1, Inl x2) = A.cmp(x1, x2)
    | cmp(Inr y1, Inr y2) = B.cmp(y1, y2)
    | cmp(Inl _, Inr _) = Lt
    | cmp(Inr _, Inl _) = Gt
end)

(* TODO
functor MkOrdFix(structure F : Fix) : TotalOrd = MkTotalOrd(struct
  type t = F.t
  fun cmp(F.Fix fx, F.Fix fy) = Eq
end) *)

(* -------------------- Lattices -------------------- *)

signature Semilattice = sig
  include PartialOrd
  val join : t * t -> t
end

signature Lattice = sig
  include Semilattice
  val meet : t * t -> t
end
