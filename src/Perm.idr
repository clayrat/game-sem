module Perm

%default total

public export
data Perm : List a -> List a -> Type where
  Nil  : Perm [] []
  Skip : Perm l1 l2 -> Perm (x::l1) (x::l2)
  Swap : Perm (x::y::l) (y::x::l)
  Trans : Perm l1 l2 -> Perm l2 l3 -> Perm l1 l3

export
permRefl : {l : List a} -> Perm l l
permRefl {l=[]}   = Nil
permRefl {l=x::l} = Skip permRefl
