module NIIT.KAM

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

%default total

mutual
  public export
  data EnvT : Env n -> Ctx n -> Type where
    Nil  : EnvT [] []
    (::) : ClaT c s -> EnvT e g -> EnvT (c::e) (g:>s)

  public export
  data CloT : Clos -> Ty -> Type where
    ClT : {n : Nat} -> {0 e : Env n} -> {0 u : Term n} ->
          {ns : Vect n Nat} -> {0 g : Ctx n} -> {0 hl : HasLengths g ns} ->
          TermT g u t -> EnvT e g -> CloT (Cl u e) t

  public export
  data ClaT : Clos -> List Ty -> Type where
    NilC  : ClaT c []
    ConsC : CloT c t -> ClaT c s -> ClaT c (t::s)

mutual
  public export
  sizeEnv : EnvT e g -> Nat
  sizeEnv []     = 0
  sizeEnv (c::d) = sizeCla c + sizeEnv d

  public export
  sizeClo : CloT c t -> Nat
  sizeClo (ClT t e) = sizeTerm t + sizeEnv e

  public export
  sizeCla : ClaT c s -> Nat
  sizeCla  NilC        = 0
  sizeCla (ConsC c cc) = sizeClo c + sizeCla cc

public export
data StackT : Stack -> Ty -> Ty -> Type where
  Mt  : StackT [] t t
  Arg : {n1 : Nat} -> {0 s : List Ty} -> {0 p1 : HasLength s n1} ->
        ClaT c s -> StackT p t1 t2 -> StackT (c::p) (s ~> t1) t2

public export
sizeStack : StackT p t1 t2 -> Nat
sizeStack  Mt       = 0
sizeStack (Arg c p) = sizeCla c + sizeStack p

public export
data StateT : State -> Ty -> Type where
  StT : {0 p : Stack} ->
        CloT c t1 -> StackT p t1 t -> StateT (St c p) t

public export
sizeState : StateT p t -> Nat
sizeState (StT c p) = sizeClo c + sizeStack p

export
initT : TermT [] u t -> StateT (KAM.init u) t
initT d = StT (ClT {hl=NilHL} d []) Mt

export
initTSize : (d : TermT [] u t) -> sizeState (initT d) = sizeTerm d
initTSize d = rewrite plusZeroRightNeutral (sizeTerm d) in
              plusZeroRightNeutral (sizeTerm d)

permuteCla : Perm s2 s1 -> ClaT c s1 -> ClaT c s2
permuteCla  Nil                          d   = d
permuteCla (Skip p)             (ConsC c d)  = ConsC c $ permuteCla p d
permuteCla  Swap       (ConsC b (ConsC c d)) = ConsC c $ ConsC b d
permuteCla (Trans p q)                   d   = permuteCla p (permuteCla q d)

permuteClaSize : (p : Perm s2 s1) -> (d : ClaT c s1) -> sizeCla d = sizeCla (KAM.permuteCla p d)
permuteClaSize  Nil                          d   = Refl
permuteClaSize (Skip p)             (ConsC c d)  = cong (plus (sizeClo c)) $ permuteClaSize p d
permuteClaSize  Swap       (ConsC b (ConsC c d)) = rewrite plusAssociative (sizeClo b) (sizeClo c) (sizeCla d) in
                                                   rewrite plusCommutative (sizeClo b) (sizeClo c) in
                                                   sym $ plusAssociative (sizeClo c) (sizeClo b) (sizeCla d)
permuteClaSize (Trans p q)                   d   = rewrite permuteClaSize q d in
                                                   permuteClaSize p (permuteCla q d)

export
permuteEnv : PermCtx g2 g1 -> EnvT e g1 -> EnvT e g2
permuteEnv  NilP      []    = []
permuteEnv (SnP d p) (c::e) = permuteCla p c :: permuteEnv d e

export
permuteEnvSize : (p : PermCtx g2 g1) -> (d : EnvT e g1) -> sizeEnv d = sizeEnv (permuteEnv p d)
permuteEnvSize  NilP     []     = Refl
permuteEnvSize (SnP d p) (c::e) = rewrite permuteClaSize p c in
                                  rewrite permuteEnvSize d e in
                                  Refl

claSplit : {n1 : Nat} -> {0 s1 : List Ty} -> {0 p : HasLength s1 n1} ->
           ClaT c (s1 ++ s2) -> (ClaT c s1, ClaT c s2)
claSplit {n1=Z}    {p=Z}            d  = (NilC, d)
claSplit {n1=S n1} {p=S p} (ConsC c d) = (ConsC c (fst $ claSplit {p} d),snd $ claSplit {p} d)
-- `let (d1,d2) = claSplit d in (ConsC c d1,d2)` blocks reduction in the second case below
-- TODO file a bug

claSplitSize : {n1 : Nat} -> {0 s1 : List Ty} -> {0 s2 : List Ty} -> {0 p : HasLength s1 n1} ->
               (d : ClaT c (s1 ++ s2)) -> sizeCla d = sizeCla (fst $ KAM.claSplit {p} {s2} d) + sizeCla (snd $ KAM.claSplit {p} {s2} d)
claSplitSize {n1=Z}    {p=Z}            d  = Refl
claSplitSize {n1=S n1} {p=S p} (ConsC c d) = rewrite sym $ plusAssociative (sizeClo c) (sizeCla (fst $ claSplit {p} {s2} d)) (sizeCla (snd $ claSplit {p} {s2} d)) in
                                             cong (plus (sizeClo c)) $ claSplitSize {p} d

export
envSplit : {n : Nat} -> {0 e : Env n} -> {ns : Vect n Nat} -> {0 g1 : Ctx n} -> {0 g2 : Ctx n} -> {0 hl : HasLengths g1 ns} ->
           EnvT e (zip g1 g2) -> (EnvT e g1,EnvT e g2)
envSplit {n=Z}   {ns=[]}     {g2=[]}     {hl=NilHL}       []     = ([], [])
envSplit {n=S n} {ns=n1::ns} {g2=g2:>x2} {hl=ConsHL hl p} (c::d) =
  (fst (claSplit {p} c)::fst (envSplit {hl} d),snd (claSplit {p} c)::snd (envSplit {hl} d))
--  let (c1,c2) = claSplit c
--      (d1,d2) = envSplit d
--    in
--  (c1::d1,c2::d2)

export
envSplitSize : {n : Nat} -> {0 e : Env n} -> {ns : Vect n Nat} -> {0 g1 : Ctx n} -> {0 g2 : Ctx n} -> {0 hl : HasLengths g1 ns} ->
               (d : EnvT e (zip g1 g2)) -> sizeEnv d = sizeEnv (fst $ envSplit {hl} {g2} d) + sizeEnv (snd $ envSplit {hl} {g2} d)
envSplitSize {n=Z}   {ns=[]}     {g2=[]}     {hl=NilHL}       []     = Refl
envSplitSize {n=S n} {ns=n1::ns} {g2=g2:>x2} {hl=ConsHL hl p} (c::d) = rewrite claSplitSize {p} {s2=x2} c in
                                                                       rewrite envSplitSize {hl} {g2} d in
                                                                       interchange (sizeCla $ fst $ claSplit c) (sizeCla $ snd $ claSplit c)
                                                                                   (sizeEnv $ fst $ envSplit d) (sizeEnv $ snd $ envSplit d)

claJoin : ClaT c s1 -> ClaT c s2 -> ClaT c (s1++s2)
claJoin  NilC        c2 = c2
claJoin (ConsC c c1) c2 = ConsC c $ claJoin c1 c2

export
envJoin : EnvT e g1 -> EnvT e g2 -> EnvT e (zip g1 g2)
envJoin []       []       = []
envJoin (c1::e1) (c2::e2) = claJoin c1 c2 :: envJoin e1 e2

export
envEmpty : {n : Nat} -> {0 e : Env n} -> EnvT e (Empty n)
envEmpty {n=Z}   {e=[]}   = []
envEmpty {n=S n} {e=c::e} = NilC :: envEmpty

export
claEmptySize : (d : ClaT c []) -> sizeCla d = 0
claEmptySize NilC = Refl

export
envEmptySize : (d : EnvT e (Empty n)) -> sizeEnv d = 0
envEmptySize []     = Refl
envEmptySize (c::d) = rewrite claEmptySize c in
                      envEmptySize d

export
mkCla : {n1 : Nat} -> {0 s : List Ty} -> {0 p1 : HasLength s n1} ->
        {n : Nat} -> {0 g : Ctx n} -> {0 e : Env n} -> {0 u : Term n} ->
        EnvT e g -> AuxT g u s -> ClaT (Cl u e) s
mkCla {n1=Z}   {p1=Z}    d  NilA         = NilC
mkCla {n1=S n} {p1=S p1} d (ConsA {hl} x p a) = ConsC (ClT {hl} x (fst $ envSplit {hl} $ permuteEnv p d))
                                                      (mkCla {p1} (snd $ envSplit {hl} $ permuteEnv p d) a)

export
sizeMkCla : {n1 : Nat} -> {0 s : List Ty} -> {0 p1 : HasLength s n1} ->
            {n : Nat} -> {0 g : Ctx n} -> {0 e : Env n} -> {0 u : Term n} ->
            (d : EnvT e g) -> (a : AuxT g u s) -> sizeAux a + sizeEnv d = sizeCla (mkCla {p1} d a)
sizeMkCla {n1=Z}   {p1=Z}    d  NilA                   = envEmptySize d
sizeMkCla {n1=S n} {p1=S p1} d (ConsA {hl} {g2} x p a) = rewrite permuteEnvSize p d in
                                                         rewrite envSplitSize {hl} {g2} (permuteEnv p d) in
                                                         rewrite interchange (sizeTerm x) (sizeAux a) (sizeEnv $ fst $ envSplit {hl} {g2} $ permuteEnv p d)
                                                                                                      (sizeEnv $ snd $ envSplit {hl} {g2} $ permuteEnv p d) in
                                                         rewrite sizeMkCla (snd $ envSplit {hl} {g2} $ permuteEnv p d) a in
                                                         Refl

export
unMkCla : {n : Nat} -> {0 e : Env n} -> {0 u : Term n} ->
          ClaT (Cl u e) s -> Exists (\g => (Subset (Vect n Nat) (HasLengths g), EnvT e g, AuxT g u s))
unMkCla  NilC                               = Evidence (Empty n) (Element (replicate n Z) emptyHL, envEmpty, NilA)
unMkCla (ConsC (ClT {g} {ns} {hl} u0 e0) c) = let Evidence g1 (Element ns1 hl1, e1, a1) = unMkCla c
                                                  0 hl2 = zipHL hl hl1
                                               in
                                              Evidence (zip g g1) (Element (zipWith (+) ns ns1) hl2, envJoin e0 e1, ConsA {hl} u0 (permCtxRefl {hl=hl2}) a1)
