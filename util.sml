

datatype 'a opt = None | Some of 'a
datatype ('a, 'b) sum = Inl of 'a | Inr of 'b

signature TYPE = sig type t end

signature FUNCTOR = sig
  type 'a t
  val map : ('a -> 'b) * 'a t -> 'b t
end

signature APPLICATIVE = sig
  include FUNCTOR
  val pure : 'a -> 'a t
  val ap : ('a -> 'b) t * 'a t -> 'b t
end

signature MONAD = sig
  include APPLICATIVE
  val bind : 'a t * ('a -> 'b t) -> 'b t
end

signature FMA_MIN = sig
  type 'a t
  val pure : 'a -> 'a t
  val bind : 'a t * ('a -> 'b t) -> 'b t
end

functor MkFunctor(M : FMA_MIN) : FUNCTOR = struct
  type 'a t = 'a M.t
  fun map(f, mx) = M.bind(mx, fn x => M.pure(f(x)))
end

functor MkApplicative(M : FMA_MIN) : APPLICATIVE = struct
  structure S = MkFunctor(M) open S
  val pure = M.pure
  fun ap(mf, mx) = M.bind(mf, fn f => map(f, mx))
end

functor MkMonad(M : FMA_MIN) : MONAD = struct
  structure S = MkApplicative(M) open S
  val bind = M.bind
end

structure ListFMA : FMA_MIN = struct
  type 'a t = 'a list
  fun pure(x) = [x]
  fun bind(xs, f) = List.concatMap f xs
end
structure ListMonad : MONAD = MkMonad(ListFMA)

structure OptFMA : FMA_MIN = struct
  type 'a t = 'a opt
  fun pure(x) = Some(x)
  fun bind(Some x, f) = f x
    | bind(None, _) = None
end
structure OptMonad : MONAD = MkMonad(OptFMA)

functor ErrFMA : FMA_MIN = struct
  type 'a t = 'a opt
  fun pure(x) = Some(x)
  fun bind(Some x, f) = f x
    | bind(None, _) = None
end
structure OptMonad : MONAD = MkMonad(OptFMA)
