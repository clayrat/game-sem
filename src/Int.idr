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
Tn : Type -> Type -> Type
Tn = Either

par : Rsm a b -> Rsm c d -> Rsm (Tn a c) (Tn b d)
par (R f) (R g) = R \case
    Left  x => let (y, f') = f x in (Left y, par f' (R g))
    Right x => let (y, g') = g x in (Right y, par (R f) g')

trace : Rsm (Tn a b) (Tn c b) -> Rsm a c
trace f = R $ \a => loop f (Left a)
  where
  loop : Rsm (Tn a b) (Tn c b) -> Tn a b -> (c, Rsm a c)
  loop (R f) v = case f v of
                   (Left  c, f') => (c, trace f')
                   (Right b, f') => loop f' (Right b)

sym : Rsm (Tn a b) (Tn b a)
sym = R \x => (mirror x, sym)

rho : Rsm (Tn a Void) a
rho = R \case
           Left  a => (a, rho)
           Right v => void v

rho' : Rsm a (Tn a Void)
rho' = R \x => (Left x, rho')

lambda : Rsm (Tn Void a) a
lambda = comp sym rho

lambda' : Rsm a (Tn Void a)
lambda' = comp rho' sym

alpha : Rsm (Tn (Tn a b) c) (Tn a (Tn b c))
alpha = R \v => (assocEither v, alpha)

alpha' : Rsm (Tn a (Tn b c)) (Tn (Tn a b) c)
alpha' = R \v => (unassocEither v, alpha')

shuffle : Rsm (Tn (Tn a d) (Tn b c))
              (Tn (Tn a b) (Tn c d))
shuffle = R \case
               Left  (Left x)  => (Left  $ Left  x, shuffle)
               Left  (Right x) => (Right $ Right x, shuffle)
               Right (Left x)  => (Left  $ Right x, shuffle)
               Right (Right x) => (Right $ Left  x, shuffle)

shuffle' : Rsm (Tn (Tn a d) (Tn b c))
               (Tn (Tn a c) (Tn b d))
shuffle' = comp (par id sym) shuffle

shuffleR : Rsm (Tn (Tn a d) (Tn b c))
               (Tn (Tn a b) (Tn d c))
shuffleR = comp shuffle (par id sym)

-- Int/G(Rsm)

data GMap : (Type, Type) -> (Type, Type) -> Type where
  G : Rsm (Tn ap bm) (Tn am bp) -> GMap (ap,am) (bp,bm)

gid : GMap (a,b) (a,b)
gid = G sym

gcomp : GMap (a,b) (c,d) -> GMap (c,d) (e,f) -> GMap (a,b) (e,f)
gcomp (G f) (G g) = G $ trace (shuffle `comp` ((par f g) `comp` shuffle'))

total
Ten : (Type, Type) -> (Type, Type) -> (Type, Type)
Ten (ap,am) (bp,bm) = (Tn ap bp, Tn am bm)

gpar : GMap (a,b) (c,d) -> GMap (e,f) (g,h) -> GMap (Ten (a,b) (e,f)) (Ten (c,d) (g,h))
gpar (G f) (G g) = G $ shuffleR `comp` ((par f g) `comp` shuffleR)

total
Dual : (Type, Type) -> (Type,Type)
Dual (a,b) = (b,a)

dualize : GMap (a,b) (c,d) -> GMap (Dual (c,d)) (Dual (a,b))
dualize (G (R f)) = G $ dual f
  where
  dual : (Tn a d -> (Tn b c, Rsm (Tn a d) (Tn b c))) -> Rsm (Tn d a) (Tn c b)
  dual f = R \v => let (v',_) = f (mirror v) in (mirror v', dual f)

total
Exp : (Type, Type) -> (Type, Type) -> (Type, Type)
Exp (ap,am) (bp,bm) = Ten (Dual (ap,am)) (bp,bm)

curry : GMap (Ten (ap,am) (bp,bm)) (cp,cm) -> GMap (ap,am) (Exp (bp,bm) (cp,cm))
curry (G r) = G $ cur r
  where
  cur : Rsm (Tn (Tn ap bp) cm) (Tn (Tn am bm) cp) -> Rsm (Tn ap (Tn bp cm)) (Tn am (Tn bm cp))
  cur (R f) = R \v => let (v', f') = f $ unassocEither v in (assocEither v', cur f')

uncurry : GMap (ap,am) (Exp (bp,bm) (cp,cm)) -> GMap (Ten (ap,am) (bp,bm)) (cp,cm)
uncurry (G r) = G $ uncur r
  where
  uncur : Rsm (Tn ap (Tn bp cm)) (Tn am (Tn bm cp)) -> Rsm (Tn (Tn ap bp) cm) (Tn (Tn am bm) cp)
  uncur (R f) = R \v => let (v',f') = f $ assocEither v in (unassocEither v', uncur f')
