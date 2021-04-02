module NIIT.Term

import Data.Fin
import Data.Vect
import Data.List.HasLength

import Perm

import Lambda.Term

import NIIT.Ty

%default total

mutual
  public export
  data TermT : Ctx n -> Term n -> Ty -> Type where
    VarT : ElemT g i t -> TermT g (Var i) t
    LamT : TermT (g:>s) u t -> TermT g (Lam u) (s ~> t)
    AppT : {n : Nat} -> {0 u, v : Term n} ->
           {ns : Vect n Nat} -> {0 g, g1, g2 : Ctx n} -> {0 hl : HasLengths g1 ns} ->
           {n1 : Nat} -> {0 s : List Ty} -> {0 p1 : HasLength s n1} ->
           TermT g1 u (s ~> t) -> AuxT g2 v s -> PermCtx (zip g1 g2) g -> TermT g (App u v) t
    ValT : {n : Nat} -> {0 t : Term (S n)} ->
           TermT (Empty n) (Lam t) V

  public export
  data AuxT : Ctx n -> Term n -> List Ty -> Type where
    NilA  : {n : Nat} -> {0 t : Term n} ->
            AuxT (Empty n) t []
    ConsA : {ns : Vect n Nat} -> {0 g1 : Ctx n} -> {0 hl : HasLengths g1 ns} ->
            TermT g1 u t -> PermCtx (zip g1 g2) g -> AuxT g2 u s -> AuxT g u (t::s)

App1 : {n : Nat} -> {0 g1, g2 : Ctx n} ->
       {ns1 : Vect n Nat} -> {auto 0 hl1 : HasLengths g1 ns1} ->
       {ns2 : Vect n Nat} -> {auto 0 hl2 : HasLengths g2 ns2} ->
       {0 u, v : Term n} -> {0 t1 : Ty} ->
       TermT g1 u ([t1] ~> t2) -> TermT g2 v t1 -> TermT (zip g1 (zip g2 (Empty n))) (App u v) t2
App1 s t = AppT {hl=hl1} {n1=1} {p1=S Z} s (ConsA {hl=hl2} t (permCtxRefl {hl=zipHL hl2 emptyHL}) NilA) (permCtxRefl {hl=zipHL hl1 $ zipHL hl2 emptyHL})

Test1 : Term 0
Test1 = Lam $ Lam $ App V1 V0

Test2 : Term 0
Test2 = Lam $ Lam $ App V1 $ App V1 V0

ex1 : TermT [] Test1 ([[V] ~> V] ~> [V] ~> V)
ex1 = LamT $ LamT $ App1 -- {g1 = Nil :> [[V] ~> V] :> [] }
                         -- {g2 = Nil :> []         :> [V]}
                        {ns1=[0,1]}
                        {ns2=[1,0]}
                        (VarT $ Suc Zero)
                        (VarT Zero)

ex2 : TermT [] Test2 ([[V] ~> V, [V] ~> V] ~> [V] ~> V)
ex2 = LamT $ LamT $ App1 -- {g1 = Nil :> [[V] ~> V] :> [] }
                         -- {g2 = Nil :> [[V] ~> V] :> [V]}
                         {ns1=[0,1]}
                         {ns2=[1,1]}
                         (VarT $ Suc Zero) $
                    App1 -- {g1 = Nil :> [[V] ~> V] :> [] }
                         -- {g2 = Nil :> []         :> [V]}
                         {ns1=[0,1]}
                         {ns2=[1,0]}
                         (VarT $ Suc Zero)
                         (VarT Zero)

public export
sizeEl : ElemT g u t -> Nat
sizeEl  Zero    = 1
sizeEl (Suc el) = S $ sizeEl el

mutual
  public export
  sizeTerm : TermT g u t -> Nat
  sizeTerm (VarT el)    = sizeEl el
  sizeTerm (LamT t)     = S $ sizeTerm t
  sizeTerm (AppT t a _) = 1 + sizeTerm t + sizeAux a
  sizeTerm  ValT        = 0

  public export
  sizeAux : AuxT g u s -> Nat
  sizeAux  NilA          = 0
  sizeAux (ConsA d _ ds) = sizeTerm d + sizeAux ds
