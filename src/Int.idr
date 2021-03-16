module Int

import Data.Either

%default covering

total
assocEither : Either (Either a b) c -> Either a (Either b c)
assocEither (Left (Left x))  = Left x
assocEither (Left (Right x)) = Right $ Left x
assocEither (Right x)        = Right $ Right x

total
unassocEither : Either a (Either b c) -> Either (Either a b) c
unassocEither (Left x)          = Left $ Left x
unassocEither (Right (Left x))  = Left $ Right x
unassocEither (Right (Right x)) = Right x

-- resumptions

data Rsm i o = R (i -> (o, Rsm i o))

id : Rsm i i
id = R \x => (x, id)

comp : Rsm a b -> Rsm b c -> Rsm a c
comp (R f) (R g) = R \x => let
                             (y, f') = f x
                             (z, g') = g y
                            in
                           (z, comp f' g')

-- tensor ~ sum type
par : Rsm a b -> Rsm c d -> Rsm (Either a c) (Either b d)
par (R f) (R g) = R \case
    Left  x => let (y, f') = f x in (Left y, par f' (R g))
    Right x => let (y, g') = g x in (Right y, par (R f) g')

trace : Rsm (Either a b) (Either c b) -> Rsm a c
trace f = R $ \a => loop f (Left a)
  where
  loop : Rsm (Either a b) (Either c b) -> Either a b -> (c, Rsm a c)
  loop (R f) v = case f v of
                   (Left  c, f') => (c, trace f')
                   (Right b, f') => loop f' (Right b)

sym : Rsm (Either a b) (Either b a)
sym = R \x => (mirror x, sym)

rho : Rsm (Either a Void) a
rho = R \case
           Left  a => (a, rho)
           Right v => void v

rho' : Rsm a (Either a Void)
rho' = R \x => (Left x, rho')

lambda : Rsm (Either Void a) a
lambda = comp sym rho

lambda' : Rsm a (Either Void a)
lambda' = comp rho' sym

alpha : Rsm (Either (Either a b) c) (Either a (Either b c))
alpha = R \v => (assocEither v, alpha)

alpha' : Rsm (Either a (Either b c)) (Either (Either a b) c)
alpha' = R \v => (unassocEither v, alpha')

-- Int/G(Rsm)

data GMap : (Type, Type) -> (Type, Type) -> Type where
  G : Rsm (Either ap bm) (Either am bp) -> GMap (ap,am) (bp,bm)

gid : GMap (a,b) (a,b)
gid = G sym

assoc : Rsm (Either (Either a d) (Either b c))
            (Either (Either a b) (Either c d))
assoc = R \case
             Left  (Left x)  => (Left  $ Left  x, assoc)
             Left  (Right x) => (Right $ Right x, assoc)
             Right (Left x)  => (Left  $ Right x, assoc)
             Right (Right x) => (Right $ Left  x, assoc)

assoc' : Rsm (Either (Either a c) (Either b d))
             (Either (Either a d) (Either b c))
assoc' = R \case
             Left  (Left x)  => (Left  $ Left  x, assoc')
             Left  (Right x) => (Right $ Right x, assoc')
             Right (Left x)  => (Right $ Left  x, assoc')
             Right (Right x) => (Left  $ Right x, assoc')

assocR : Rsm (Either (Either a d) (Either b c))
             (Either (Either a b) (Either d c))
assocR = comp assoc (par id sym)

assocR' : Rsm (Either (Either a c) (Either b d))
              (Either (Either a b) (Either c d))
assocR' = comp assoc' assoc

gcomp : GMap (a,b) (c,d) -> GMap (c,d) (e,f) -> GMap (a,b) (e,f)
gcomp (G f) (G g) = G $ trace (assoc `comp` ((par f g) `comp` assoc'))

total
Ten : (Type, Type) -> (Type, Type) -> (Type, Type)
Ten (ap,am) (bp,bm) = (Either ap bp, Either am bm)

gpar : GMap (a,b) (c,d) -> GMap (e,f) (g,h) -> GMap (Ten (a,b) (e,f)) (Ten (c,d) (g,h))
gpar (G f) (G g) = G $ assocR `comp` ((par f g) `comp` assocR')

total
Dual : (Type, Type) -> (Type,Type)
Dual (a,b) = (b,a)

dualize : GMap (a,b) (c,d) -> GMap (Dual (c,d)) (Dual (a,b))
dualize (G (R f)) = G $ dual f
  where
  dual : (Either a d -> (Either b c, Rsm (Either a d) (Either b c))) -> Rsm (Either d a) (Either c b)
  dual f = R \v => let (v',_) = f (mirror v) in (mirror v', dual f)

total
Exp : (Type, Type) -> (Type, Type) -> (Type, Type)
Exp (ap,am) (bp,bm) = Ten (Dual (ap,am)) (bp,bm)

curry : GMap (Ten (ap,am) (bp,bm)) (cp,cm) -> GMap (ap,am) (Exp (bp,bm) (cp,cm))
curry (G r) = G $ cur r
  where
  cur : Rsm (Either (Either ap bp) cm) (Either (Either am bm) cp) -> Rsm (Either ap (Either bp cm)) (Either am (Either bm cp))
  cur (R f) = R \v => let (v', f') = f $ unassocEither v in (assocEither v', cur f')

uncurry : GMap (ap,am) (Exp (bp,bm) (cp,cm)) -> GMap (Ten (ap,am) (bp,bm)) (cp,cm)
uncurry (G r) = G $ uncur r
  where
  uncur : Rsm (Either ap (Either bp cm)) (Either am (Either bm cp)) -> Rsm (Either (Either ap bp) cm) (Either (Either am bm) cp)
  uncur (R f) = R \v => let (v',f') = f $ assocEither v in (unassocEither v', uncur f')
