module NIIT.Lemmas

import Data.Nat
import Data.Fin
import Data.Vect
import Data.DPair
import Data.List.HasLength

import Nat
import Perm

import Lambda.Term
import Lambda.KAM

import NIIT.Ty
import NIIT.Term
import NIIT.KAM

%default total

subjRed : Step p q -> StateT p t -> StateT q t
subjRed Grab (StT (ClT                  (VarT  Zero)           (ConsC c NilC::_))             k ) = StT c k
subjRed Skip (StT (ClT {hl=ConsHL hl _} (VarT (Suc x))                    (_::e))             k ) = StT (ClT {hl} (VarT x) e) k
subjRed Push (StT (ClT                  (AppT {hl} {p1} t a p)                e )             k ) = StT (ClT {hl} t (fst $ envSplit {hl} $ permuteEnv p e))
                                                                                                        (Arg {p1} (mkCla {p1} (snd $ envSplit {hl} $ permuteEnv p e) a) k)
subjRed Pop  (StT (ClT {hl}             (LamT t)                              e ) (Arg {p1} c k)) = StT (ClT {hl= ConsHL hl p1} t (c::e)) k

sizeSR : (pq : Step p q) -> (st : StateT p t) -> sizeState st = S (sizeState (subjRed pq st))
sizeSR Grab (StT (ClT {n=S n}          (VarT  Zero)                (ConsC c NilC::e))        k ) =
  rewrite envEmpty {n} e in
  rewrite plusZeroRightNeutral (sizeClo c) in
  rewrite plusZeroRightNeutral (sizeClo c) in
  Refl
sizeSR Skip (StT (ClT {hl=ConsHL hl _} (VarT (Suc x))                         (c::e))        k ) =
  rewrite claEmpty c in
  Refl
sizeSR Push (StT (ClT                  (AppT {hl} {p1} {g2} t a p)                e )        k ) =
  rewrite permuteEnvSize p e in
  rewrite envSplitSize {hl} {g2} (permuteEnv p e) in
  rewrite interchange (sizeTerm t) (sizeAux a) (sizeEnv $ fst $ envSplit {hl} {g2} $ permuteEnv p e)
                                               (sizeEnv $ snd $ envSplit {hl} {g2} $ permuteEnv p e) in
  rewrite sizeMkCla (snd $ envSplit {hl} {g2} $ permuteEnv p e) a in
  cong S $ sym $ plusAssociative (sizeTerm t + sizeEnv (fst $ envSplit {hl} {g2} $ permuteEnv p e))
                                 (sizeCla $ mkCla (snd $ envSplit {hl} {g2} $ permuteEnv p e) a)
                                 (sizeStack k)
sizeSR Pop  (StT (ClT                  (LamT t)                                   e ) (Arg c k)) =
  rewrite sym $ plusAssociative (sizeTerm t) (sizeEnv e) (sizeCla c + sizeStack k) in
  rewrite plusAssociative (sizeEnv e) (sizeCla c) (sizeStack k) in
  rewrite plusCommutative (sizeEnv e) (sizeCla c) in
  cong S $ plusAssociative (sizeTerm t) (sizeCla c + sizeEnv e) (sizeStack k)

claJoin : ClaT c s1 -> ClaT c s2 -> ClaT c (s1 ++ s2)
claJoin  NilC        c2 = c2
claJoin (ConsC c c1) c2 = ConsC c $ claJoin c1 c2

envJoin : EnvT e g1 -> EnvT e g2 -> EnvT e (zip g1 g2)
envJoin []       []       = []
envJoin (c1::e1) (c2::e2) = claJoin c1 c2 :: envJoin e1 e2

envEmpty : {n : Nat} -> {0 e : Env n} -> EnvT e (Empty n)
envEmpty {n=Z}   {e=[]}   = []
envEmpty {n=S n} {e=c::e} = NilC :: envEmpty

unMkCla : {n : Nat} -> {0 e : Env n} -> {0 u : Term n} ->
          ClaT (Cl u e) s -> Exists (\g => (Subset (Vect n Nat) (HasLengths g), EnvT e g, AuxT g u s))
unMkCla  NilC                               = Evidence (Empty n) (Element (replicate n Z) emptyHL, envEmpty, NilA)
unMkCla (ConsC (ClT {g} {ns} {hl} u0 e0) c) = let Evidence g1 (Element ns1 hl1, e1, a1) = unMkCla c
                                                  0 hl2 = zipHL hl hl1
                                               in
                                              Evidence (zip g g1) (Element (zipWith (+) ns ns1) hl2, envJoin e0 e1, ConsA {hl} u0 (permCtxRefl {hl=hl2}) a1)

subjExp : Step p q -> StateT q t -> StateT p t
subjExp (Grab {z}) (StT  c                    k) = StT (ClT {hl = ConsHL emptyHL (S Z)} (VarT Zero)    (ConsC c NilC :: (envEmpty {n=z}))) k
subjExp  Skip      (StT (ClT {hl} (VarT x) e) k) = StT (ClT {hl = ConsHL hl Z}          (VarT $ Suc x) (NilC         :: e               )) k
subjExp  Push      (StT  c                    k) = ?wat
subjExp  Pop       (StT  c                    k) = ?wat4