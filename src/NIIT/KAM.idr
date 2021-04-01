module NIIT.KAM

import Data.Nat
import Data.Fin
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
    ClT : {n : Nat} -> {0 e : Env n} -> {0 g : Ctx n} -> {0 u : Term n} ->
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
  Arg : ClaT c s -> StackT p t1 t2 -> StackT (c::p) (s ~> t1) t2

public export
sizeStack : StackT p t1 t2 -> Nat
sizeStack  Mt       = 0
sizeStack (Arg c p) = sizeCla c + sizeStack p

public export
data StateT : State -> Ty -> Type where
  StT : CloT c t1 -> StackT p t1 t -> StateT (St c p) t

public export
sizeState : StateT p t -> Nat
sizeState (StT c p) = sizeClo c + sizeStack p

initT : TermT [] u t -> StateT (KAM.init u) t
initT d = StT (ClT d []) Mt

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

-- here and after we don't really need the full contexts at runtime, just their lengths
claSplit : {s1 : List Ty} ->
           ClaT c (s1 ++ s2) -> (ClaT c s1, ClaT c s2)
claSplit {s1=[]}             d  = (NilC, d)
claSplit {s1=x::s1} (ConsC c d) = (ConsC c (fst $ claSplit d),snd $ claSplit d)
-- `let (d1,d2) = claSplit d in (ConsC c d1,d2)` blocks reduction in the second case below
-- TODO file a bug

claSplitSize : {s1 : List Ty} -> {0 s2 : List Ty} ->
               (d : ClaT c (s1 ++ s2)) -> sizeCla d = sizeCla (fst $ KAM.claSplit {s1} {s2} d) + sizeCla (snd $ KAM.claSplit {s1} {s2} d)
claSplitSize {s1=[]}             d  = Refl
claSplitSize {s1=x::s1} (ConsC c d) = rewrite sym $ plusAssociative (sizeClo c) (sizeCla (fst $ claSplit {s1} {s2} d)) (sizeCla (snd $ claSplit {s1} {s2} d)) in
                                      cong (plus (sizeClo c)) $ claSplitSize {s1} d

export
envSplit : {n : Nat} -> {0 e : Env n} -> {g1 : Ctx n} -> {0 g2 : Ctx n} ->
           EnvT e (zip g1 g2) -> (EnvT e g1,EnvT e g2)
envSplit {n=Z}   {g1=[]}     {g2=[]}     []     = ([], [])
envSplit {n=S n} {g1=g1:>x1} {g2=g2:>x2} (c::d) =
  (fst (claSplit c)::fst (envSplit d),snd (claSplit c)::snd (envSplit d))
--  let (c1,c2) = claSplit c
--      (d1,d2) = envSplit d
--    in
--  (c1::d1,c2::d2)

export
envSplitSize : {n : Nat} -> {0 e : Env n} -> {g1 : Ctx n} -> {0 g2 : Ctx n} ->
               (d : EnvT e (zip g1 g2)) -> sizeEnv d = sizeEnv (fst $ envSplit {g1} {g2} d) + sizeEnv (snd $ envSplit {g1} {g2} d)
envSplitSize {n=Z}   {g1=[]}     {g2=[]}     []     = Refl
envSplitSize {n=S n} {g1=g1:>x1} {g2=g2:>x2} (c::d) = rewrite claSplitSize {s1=x1} {s2=x2} c in
                                                      rewrite envSplitSize {g1} {g2} d in
                                                      interchange (sizeCla $ fst $ claSplit c) (sizeCla $ snd $ claSplit c)
                                                                  (sizeEnv $ fst $ envSplit d) (sizeEnv $ snd $ envSplit d)

export
claEmpty : (d : ClaT c []) -> sizeCla d = 0
claEmpty NilC = Refl

export
envEmpty : {n : Nat} -> {0 e : Env n} -> (d : EnvT e (Empty n)) -> sizeEnv d = 0
envEmpty []     = Refl
envEmpty (c::d) = rewrite claEmpty c in
                  envEmpty d

export
mkCla : {s : List Ty} -> {n : Nat} -> {0 g : Ctx n} -> {0 e : Env n} -> {0 u : Term n} ->
        EnvT e g -> AuxT g u s -> ClaT (Cl u e) s
mkCla {s=[]}   d  NilA         = NilC
mkCla {s=t::s} d (ConsA x p a) = ConsC (ClT x (fst $ envSplit $ permuteEnv p d))
                                       (mkCla (snd $ envSplit $ permuteEnv p d) a)

export
sizeMkCla : {s : List Ty} -> {n : Nat} -> {0 g : Ctx n} -> {0 e : Env n} -> {0 u : Term n} ->
            (d : EnvT e g) -> (a : AuxT g u s) -> sizeAux a + sizeEnv d = sizeCla (mkCla d a)
sizeMkCla {s=[]}   d  NilA                   = envEmpty d
sizeMkCla {s=t::s} d (ConsA {g1} {g2} x p a) = rewrite permuteEnvSize p d in
                                               rewrite envSplitSize {n} {g1} {g2} (permuteEnv p d) in
                                               rewrite interchange (sizeTerm x) (sizeAux a) (sizeEnv $ fst $ envSplit {n} {g1} {g2} $ permuteEnv p d)
                                                                                            (sizeEnv $ snd $ envSplit {n} {g1} {g2} $ permuteEnv p d) in
                                               rewrite sizeMkCla (snd $ envSplit {n} {g1} {g2} $ permuteEnv p d) a in
                                               Refl
