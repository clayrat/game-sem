module NIIT.Lemmas

import Data.Nat
import Data.Fin
import Nat
import Perm
import Lambda.Term
import Lambda.KAM
import NIIT.Ty
import NIIT.Term
import NIIT.KAM

%default total

subjectReduction : Step p q -> StateT p t -> StateT q t
subjectReduction Grab (StT (ClT (VarT  Zero)   (ConsC c NilC::_))        k ) = StT c k
subjectReduction Skip (StT (ClT (VarT (Suc x))            (_::e))        k ) = StT (ClT (VarT x) e) k
subjectReduction Push (StT (ClT (AppT t a p)                  e )        k ) = StT (ClT t (fst $ envSplit $ permuteEnv p e))
                                                                                   (Arg (mkCla (snd $ envSplit $ permuteEnv p e) a) k)
subjectReduction Pop  (StT (ClT (LamT t)                      e ) (Arg c k)) = StT (ClT t (c::e)) k

sizeSR : (pq : Step p q) -> (st : StateT p t) -> sizeState st = S (sizeState (subjectReduction pq st))
sizeSR Grab (StT (ClT {n=S n} (VarT  Zero)           (ConsC c NilC::e))        k ) =
  rewrite envEmpty {n} e in
  rewrite plusZeroRightNeutral (sizeClo c) in
  rewrite plusZeroRightNeutral (sizeClo c) in
  Refl
sizeSR Skip (StT (ClT         (VarT (Suc x))                    (c::e))        k ) =
  rewrite claEmpty c in Refl
sizeSR Push (StT (ClT {n}     (AppT {g1} {g2} t a p)                e )        k ) =
  rewrite permuteEnvSize p e in
  rewrite envSplitSize {n} {g1} {g2} (permuteEnv p e) in
  rewrite interchange (sizeTerm t) (sizeAux a) (sizeEnv $ fst $ envSplit {n} {g1} {g2} $ permuteEnv p e)
                                               (sizeEnv $ snd $ envSplit {n} {g1} {g2} $ permuteEnv p e) in
  rewrite sizeMkCla (snd $ envSplit {n} {g1} {g2} $ permuteEnv p e) a in
  cong S $ sym $ plusAssociative (sizeTerm t + sizeEnv (fst $ envSplit {n} {g1} {g2} $ permuteEnv p e))
                                 (sizeCla $ mkCla (snd $ envSplit {n} {g1} {g2} $ permuteEnv p e) a)
                                 (sizeStack k)
sizeSR Pop  (StT (ClT (LamT t)                      e ) (Arg c k)) =
  rewrite sym $ plusAssociative (sizeTerm t) (sizeEnv e) (sizeCla c + sizeStack k) in
  rewrite plusAssociative (sizeEnv e) (sizeCla c) (sizeStack k) in
  rewrite plusCommutative (sizeEnv e) (sizeCla c) in
  cong S $ plusAssociative (sizeTerm t) (sizeCla c + sizeEnv e) (sizeStack k)

claJoin : {s1 : List Ty} -> ClaT c s1 -> ClaT c s2 -> ClaT c (s1 ++ s2)
claJoin {s1=[]}     NilC        c2 = c2
claJoin {s1=t::s1} (ConsC c c1) c2 = ConsC c $ claJoin c1 c2
