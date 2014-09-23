module Alacarte

import Language.Reflection
import Language.Reflection.Utils



infixl 9 :+:
infixl 8 :<:
infixl 8 :=:

%default total

data (:+:) : (Type -> Type) -> (Type -> Type) -> Type -> Type  where
  Inl : f a -> (:+:) f g a
  Inr : g a -> (:+:) f g a


instance (Functor f, Functor g) => Functor (f :+: g) where
  map f (Inl x) = Inl (map f x)
  map f (Inr x) = Inr (map f x)

record (:<:) : (Type -> Type) -> (Type -> Type) -> Type where
  MkSub : (injMethod : (a: Type) -> f a -> g a) -> f :<: g

here : f :<: f
here = MkSub (\ _ => id)

left : (f :<: g1) -> f :<: (g1 :+: g2)
left (MkSub inj) = MkSub (\ a => Inl . inj a)

right : (f :<: g2) -> f :<: (g1 :+: g2)
right (MkSub inj) = MkSub (\ a => Inr . inj a)

split : (f1 :<: g) -> (f2 :<: g) -> (f1 :+: f2) :<: g
split (MkSub inj1) (MkSub inj2) = MkSub inj
      where inj a (Inl x) = inj1 a x
            inj a (Inr x) = inj2 a x

findLtPrf : TT -> TT -> Maybe TT
findLtPrf `(~f1 :+: ~f2) g = do l <- findLtPrf f1 g
                                r <- findLtPrf f2 g
                                return `(split {f1=~f1} {g=~g} {f2=~f2} ~l ~r)
findLtPrf f `(~a :+: ~b) = case (findLtPrf f a, findLtPrf f b) of
                             (Just l, _) => Just `(left {f=~f} {g1=~a} {g2=~b} ~l)
                             (_, Just r) => Just `(right {f=~f} {g1=~a} {g2=~b} ~r)
                             _           => Nothing
findLtPrf f1 f2 = if f1 == f2 then Just `(here {f=~f1}) else Nothing
findLtPrf _ _ = Nothing

isGoal : TT -> TT -> TT -> Bool
isGoal f g `(~f' :<: ~g') = f' == f && g' == g
isGoal _ _ _ = False

findInCtxt : TT -> TT -> List (TTName, Binder TT) -> Maybe TT
findInCtxt f g (x :: r) = case x of
           (n, PVar t) => if isGoal f g t then Just (P Bound n t)
                          else findInCtxt f g r
           _ => findInCtxt f g r
findInCtxt f g [] = Nothing


seeSig : List (TTName, Binder TT) -> TT -> Tactic
seeSig ctxt `(~x :<: ~y) = case findInCtxt x y ctxt of
       Just prf => Exact prf
       Nothing => case findLtPrf x y of
               Just prf  => Exact prf
               Nothing   => Fail [TextPart "not found prf"]
seeSig ctxt g = Fail [TextPart "not the right goal", TermPart g]



syntax [f] "<" [g] "," [t] = (Functor f, Functor g) => 
       {default tactics {applyTactic seeSig ; solve }  S : f :<: g} -> t

inj : f < g, f a ->  g a
inj x {S = MkSub inj'} {a = a} = inj' a x

data Fix : (Type -> Type) -> Type where
  In : f (Fix f) -> Fix f
  

%default partial

fold : Functor f => (f a -> a) -> Fix f -> a
fold f (In x) = f (map (fold f) x)

%default total
    
inject : f < g, f (Fix g) -> Fix g
inject x = In (inj x)



data F a = MkF a a

data H a = MkH a

data G a = MkG a

instance Functor F where  
    map f (MkF x y) = MkF (f x) (f y)

instance Functor H where  
    map f (MkH x) = MkH (f x)



-- smart constructor for F
iF : F < g, Fix g -> Fix g -> Fix g
iF x y = inject {f=F} (MkF x y)

test : F a -> (F :+: H) a
test = inj

tacticTest1 : F :<: F
tacticTest1 = proof applyTactic seeSig

-- tacticTest1' : F :<: F
-- tacticTest1' = proof search

tacticTest2 : F :<: (F :+: H)
tacticTest2 = proof applyTactic seeSig

-- tacticTest2' : F :<: (F :+: H)
-- tacticTest2' = proof search

tacticTest3 : (F :+: H) :<: (H :+: F)
tacticTest3 = proof applyTactic seeSig

-- For this, Idris's proof search breaks down
-- tacticTest3' : (F :+: H) :<: (H :+: F)
-- tacticTest3' = proof search

tacticTest4 : (F :+: H) :<: (H :+: G :+: F)
tacticTest4 = proof applyTactic seeSig

