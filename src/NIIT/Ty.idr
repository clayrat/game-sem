module NIIT.Ty

import Data.Fin
import Data.Vect
import Data.List.HasLength

import Perm

%default total

infixr 5 ~>

public export
data Ty : Type where
  V    : Ty
  (~>) : List Ty -> Ty -> Ty

infixl 5 :>

public export
data Ctx : Nat -> Type where
  Nil  : Ctx Z
  (:>) : Ctx n -> List Ty -> Ctx (S n)

public export
Empty : (n : Nat) -> Ctx n
Empty  Z    = []
Empty (S n) = Empty n :> []

public export
zip : Ctx n -> Ctx n -> Ctx n
zip  []         []        = []
zip (g1 :> s1) (g2 :> s2) = (zip g1 g2) :> (s1 ++ s2)

public export
data HasLengths : Ctx n -> Vect n Nat -> Type where
  NilHL  : HasLengths [] []
  ConsHL : HasLengths cx ns -> HasLength xs n -> HasLengths (cx :> xs) (n::ns)

-- TODO https://github.com/idris-lang/Idris2/issues/1258
export
hlAppend : HasLength xs m -> HasLength ys n -> HasLength (xs ++ ys) (m + n)
hlAppend Z ys = ys
hlAppend (S xs) ys = S (hlAppend xs ys)

export
emptyHL : {n : Nat} -> HasLengths (Empty n) (replicate n Z)
emptyHL {n=Z}   = NilHL
emptyHL {n=S n} = ConsHL emptyHL Z

export
zipHL : {0 cx1, cx2 : Ctx n} -> HasLengths cx1 ns1 -> HasLengths cx2 ns2 -> HasLengths (zip cx1 cx2) (zipWith (+) ns1 ns2)
zipHL  NilHL           NilHL          = NilHL
zipHL (ConsHL hl1 h1) (ConsHL hl2 h2) = ConsHL (zipHL hl1 hl2) (hlAppend h1 h2)

public export
data PermCtx : Ctx n -> Ctx n -> Type where
  NilP : PermCtx [] []
  SnP  : PermCtx g1 g2 -> Perm s1 s2 -> PermCtx (g1 :> s1) (g2 :> s2)

export
permCtxRefl : {ns : Vect n Nat} -> {0 g : Ctx n} -> {0 hl : HasLengths g ns} -> PermCtx g g
permCtxRefl {ns=[]}    {hl=NilHL}       = NilP
permCtxRefl {ns=n::ns} {hl=ConsHL hl p} = SnP (permCtxRefl {hl}) (permRefl {p})

public export
data ElemT : Ctx n -> Fin n -> Ty -> Type where
  Zero : {n : Nat} -> ElemT ((Empty n) :> [t]) FZ t
  Suc  : ElemT g i t -> ElemT (g :> []) (FS i) t
