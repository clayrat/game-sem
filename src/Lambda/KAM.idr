module Lambda.KAM

import Data.Fin
import Lambda.Term

%default total

mutual
  public export
  data Env : Nat -> Type where
    Nil  : Env Z
    (::) : Clos -> Env n -> Env (S n)

  public export
  data Clos : Type where
    Cl : Term n -> Env n -> Clos

public export
Stack : Type
Stack = List Clos

public export
record State where
  constructor St
  clo : Clos
  stk : Stack

public export
init : Term 0 -> State
init t = St (Cl t []) []

public export
data Step : State -> State -> Type where
  Grab : Step (St (Cl (Var  FZ   ) (Cl t e0::e))     s ) (St (Cl  t           e0)          s )
  Skip : Step (St (Cl (Var (FS x)) (      _::e))     s ) (St (Cl (Var x)      e )          s )
  Push : Step (St (Cl (App t u   )           e )     s ) (St (Cl  t           e ) (Cl u e::s))
  Pop  : Step (St (Cl (Lam t     )           e ) (c::s)) (St (Cl  t       (c::e))          s )

deterministic : Step p q -> Step p r -> q = r
deterministic Grab Grab = Refl
deterministic Skip Skip = Refl
deterministic Push Push = Refl
deterministic Pop  Pop  = Refl

data Reduces : Nat -> State -> Type where
  Stop :                            Reduces  Z    (St (Cl (Lam t) e) [])
  More : Step p q -> Reduces n q -> Reduces (S n)  p

reducesDet : Reduces m p -> Reduces n p -> m = n
reducesDet  Stop         Stop        = Refl
reducesDet (More s1 r1) (More s2 r2) = cong S $ reducesDet r1 (rewrite deterministic s1 s2 in r2)
