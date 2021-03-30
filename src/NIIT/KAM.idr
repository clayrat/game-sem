module NIIT.KAM

import Data.Nat
import Data.Fin
import Perm
import Lambda.Term
import Lambda.KAM
import NIIT.Ty
import NIIT.Term

%default total

mutual
  data EnvT : Env n -> Ctx n -> Type where
    Nil  : EnvT [] []
    (::) : ClaT c s -> EnvT e g -> EnvT (c::e) (g:>s)

  data CloT : Clos -> Ty -> Type where
    ClT : TermT g u t -> EnvT e g -> CloT (Cl u e) t

  data ClaT : Clos -> List Ty -> Type where
    NilC  : ClaT c []
    ConsC : CloT c t -> ClaT c s -> ClaT c (t::s)

mutual
  sizeEnv : EnvT e g -> Nat
  sizeEnv []     = 0
  sizeEnv (c::d) = sizeCla c + sizeEnv d

  sizeClo : CloT c t -> Nat
  sizeClo (ClT t e) = sizeTerm t + sizeEnv e

  sizeCla : ClaT c s -> Nat
  sizeCla  NilC        = 0
  sizeCla (ConsC c cc) = sizeClo c + sizeCla cc

data StackT : Stack -> Ty -> Ty -> Type where
  Mt  : StackT [] t t
  Arg : ClaT c s -> StackT p t1 t2 -> StackT (c::p) (s ~> t1) t2

sizeStack : StackT p t1 t2 -> Nat
sizeStack  Mt       = 0
sizeStack (Arg c p) = sizeCla c + sizeStack p

data StateT : State -> Ty -> Type where
  StT : CloT c t1 -> StackT p t1 t -> StateT (St c p) t

sizeState : StateT p t -> Nat
sizeState (StT c p) = sizeClo c + sizeStack p

initT : TermT [] u t -> StateT (KAM.init u) t
initT d = StT (ClT d []) Mt

initTSize : (d : TermT [] u t) -> sizeState (initT d) = sizeTerm d
initTSize d = rewrite plusZeroRightNeutral (sizeTerm d) in
              plusZeroRightNeutral (sizeTerm d)
