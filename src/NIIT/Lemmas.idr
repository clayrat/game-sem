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
  rewrite envEmptySize {n} e in
  rewrite plusZeroRightNeutral (sizeClo c) in
  rewrite plusZeroRightNeutral (sizeClo c) in
  Refl
sizeSR Skip (StT (ClT {hl=ConsHL hl _} (VarT (Suc x))                         (c::e))        k ) =
  rewrite claEmptySize c in
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

subjExp : Step p q -> StateT q t -> StateT p t
subjExp (Grab {z}) (StT  c                                           k ) = StT (ClT {hl=ConsHL emptyHL (S Z)} (VarT Zero)    (ConsC c NilC::envEmpty {n=z}))             k
subjExp  Skip      (StT (ClT {hl} (VarT x)           e )             k ) = StT (ClT {hl=ConsHL hl Z}          (VarT $ Suc x) (NilC        ::e             ))             k
subjExp  Push      (StT (ClT {hl} t                  e ) (Arg {p1} c k)) = let Evidence g1 (Element ns1 hl1, e1, a1) = unMkCla c
                                                                               0 hl2 = zipHL hl hl1
                                                                            in
                                                                           StT (ClT {hl=hl2} (AppT {hl} {p1} t a1 (permCtxRefl {hl=hl2})) (envJoin e e1))                k
subjExp  Pop       (StT (ClT {hl=ConsHL hl p1} t (c::e))             k ) = StT (ClT {hl} (LamT t) e)                                                         (Arg {p1} c k)

progress : (d : StateT p V) -> Not (sizeState d = 0) -> Exists (Step p)
progress (StT {p} (ClT          (VarT Zero)        (ConsC (ClT {u} {e} _ _) NilC::_))       _ ) _  = Evidence (St (Cl  u      e )          p ) Grab
progress (StT {p} (ClT {e=_::e} (VarT (Suc {i} _))                            (_::_))       _ ) _  = Evidence (St (Cl (Var i) e )          p ) Skip
progress (StT {p} (ClT {e} (AppT {u} {v} _ _ _)                                   _)        _ ) _  = Evidence (St (Cl  u      e ) (Cl v e::p)) Push
progress (StT {p=c::p} (ClT {e} {u=Lam u} (LamT _)                                _) (Arg _ _)) _  = Evidence (St (Cl  u  (c::e))          p ) Pop
progress (StT     (ClT ValT                                                       e)       Mt ) nz = absurd $ replace {p= \x=>Not (x+0=0)} (envEmptySize e) nz Refl

soundness : (d : TermT [] t V) -> Reduces (sizeTerm d) (St (Cl t []) [])
soundness d = rewrite sym $ initTSize d in
              run (initT d) (sizeState (initT d)) Refl
  where
  final : (d : StateT p V) -> sizeState d = 0 -> Reduces 0 p
  final (StT (ClT (VarT Zero)    _) _ ) sz = absurd sz
  final (StT (ClT (VarT (Suc _)) _) _ ) sz = absurd sz
  final (StT (ClT (AppT _ _ _)   _) _ ) sz = absurd sz
  final (StT (ClT (LamT _)       _) _ ) sz = absurd sz
  final (StT (ClT  ValT          _) Mt) _  = Stop

  run : (d : StateT p V) -> (k : Nat) -> sizeState d = k -> Reduces k p
  run d  Z    sz = final d sz
  run d (S k) sz = let Evidence q st = progress d (rewrite sz in absurd) in
                   More st (run (subjRed st d) k (succInjective (sizeState $ subjRed st d) k $
                                                  trans (sym $ sizeSR st d) sz))

completeness : Reduces n (St (Cl t []) []) -> (d : TermT [] t V ** sizeTerm d = n)
completeness r = let d = extract $ stateTyped r in
                 (d ** reducesDet (soundness d) r)
  where
  extract : StateT (St (Cl t []) []) V -> TermT [] t V
  extract (StT (ClT t []) Mt) = t

  stateTyped : Reduces k p -> StateT p V
  stateTyped  Stop       = StT (ClT {hl=emptyHL} ValT envEmpty) Mt
  stateTyped (More st r) = subjExp st (stateTyped r)
