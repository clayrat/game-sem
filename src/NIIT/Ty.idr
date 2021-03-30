module NIIT.Ty

import Data.Fin
import Perm

%default total

infixr 5 ~>

public export
data Ty : Type where
  V : Ty
  (~>) : List Ty -> Ty -> Ty

infixl 5 :>

public export
data Ctx : Nat -> Type where
  Nil : Ctx Z
  (:>)  : Ctx n -> List Ty -> Ctx (S n)

public export
Empty : (n : Nat) -> Ctx n
Empty  Z    = []
Empty (S n) = Empty n :> []

public export
zip : Ctx n -> Ctx n -> Ctx n
zip  []         []        = []
zip (g1 :> s1) (g2 :> s2) = (zip g1 g2) :> (s1 ++ s2)

public export
data PermCtx : Ctx n -> Ctx n -> Type where
  NilP : PermCtx [] []
  SnP  : PermCtx g1 g2 -> Perm s1 s2 -> PermCtx (g1 :> s1) (g2 :> s2)

export
permCtxRefl : {g : Ctx n} -> PermCtx g g
permCtxRefl {g=[]}   = NilP
permCtxRefl {g=g:>s} = SnP permCtxRefl permRefl

public export
data ElemT : Ctx n -> Fin n -> Ty -> Type where
  Zero : {n : Nat} -> ElemT ((Empty n) :> [t]) FZ t
  Suc  : ElemT g i t -> ElemT (g :> []) (FS i) t
