module Perm

import Data.List.HasLength

%default total

public export
data Perm : List a -> List a -> Type where
  Nil  : Perm [] []
  Skip : Perm l1 l2 -> Perm (x::l1) (x::l2)
  Swap : Perm (x::y::l) (y::x::l)
  Trans : Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3

export
permRefl : {n : Nat} -> {0 l : List a} -> {0 p : HasLength l n} -> Perm l l
permRefl {n=Z}   {p=Z}   = Nil
permRefl {n=S n} {p=S p} = Skip $ permRefl {p}
