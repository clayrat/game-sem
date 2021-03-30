module Lambda.Term

import Data.Fin

%default total

public export
data Term : Nat -> Type where
  Var : Fin n -> Term n
  Lam : Term (S n) -> Term n
  App : Term n -> Term n -> Term n

-- convenience

public export
V0 : Term (S n)
V0 = Var FZ

public export
V1 : Term (2+n)
V1 = Var $ FS FZ

public export
V2 : Term (3+n)
V2 = Var $ FS $ FS FZ

public export
V3 : Term (4+n)
V3 = Var $ FS $ FS $ FS FZ
