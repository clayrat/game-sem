module NIIT.Term

import Data.Fin
import Perm
import Lambda.Term
import NIIT.Ty

%default total

mutual
  public export
  data TermT : Ctx n -> Term n -> Ty -> Type where
    VarT : ElemT g i t -> TermT g (Var i) t
    LamT : TermT (g:>s) u t -> TermT g (Lam u) (s ~> t)
    AppT : {s : List Ty} -> {g1 : Ctx n} ->
           TermT g1 u (s ~> t) -> AuxT g2 v s -> PermCtx (zip g1 g2) g -> TermT g (App u v) t
    ValT : {n : Nat} -> {0 t : Term (S n)} ->
           TermT (Empty n) (Lam t) V

  public export
  data AuxT : Ctx n -> Term n -> List Ty -> Type where
    NilA  : {n : Nat} -> {0 t : Term n} ->
            AuxT (Empty n) t []
    ConsA : {g1 : Ctx n} ->
            TermT g1 u t -> PermCtx (zip g1 g2) g -> AuxT g2 u s -> AuxT g u (t::s)

App1 : {n : Nat} -> {g1, g2 : Ctx n} -> {0 u, v : Term n} -> {t1 : Ty} ->
       TermT g1 u ([t1] ~> t2) -> TermT g2 v t1 -> TermT (zip g1 (zip g2 (Empty n))) (App u v) t2
App1 s t = AppT s (ConsA t permCtxRefl NilA) permCtxRefl

Test1 : Term 0
Test1 = Lam $ Lam $ App V1 V0

Test2 : Term 0
Test2 = Lam $ Lam $ App V1 $ App V1 V0

ex1 : TermT [] Test1 ([[V] ~> V] ~> [V] ~> V)
ex1 = LamT $ LamT $ App1 -- {g1 = Nil :> [[V] ~> V] :> [] }
                         -- {g2 = Nil :> []         :> [V]}
                        (VarT $ Suc Zero)
                        (VarT Zero)

ex2 : TermT [] Test2 ([[V] ~> V, [V] ~> V] ~> [V] ~> V)
ex2 = LamT $ LamT $ App1 -- {g1 = Nil :> [[V] ~> V] :> [] }
                         -- {g2 = Nil :> [[V] ~> V] :> [V]}
                         (VarT $ Suc Zero) $
                    App1 -- {g1 = Nil :> [[V] ~> V] :> [] }
                         -- {g2 = Nil :> []         :> [V]}
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
  sizeAux NilA           = 0
  sizeAux (ConsA d _ ds) = sizeTerm d + sizeAux ds
