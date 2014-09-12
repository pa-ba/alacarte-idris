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


record (:<:) : (Type -> Type) -> (Type -> Type) -> Type where
  MkSub : (inj : (a: Type) -> f a -> g a) -> f :<: g

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

inj : {default tactics {applyTactic seeSig ; solve }  S : f :<: g} -> f a -> g a
inj {S = MkSub inj'} {a = a} = inj' a


data F a = MkF a a

data H a = MkH a

data G a = MkG a

data Fix : (Type -> Type) -> Type where
  In : f (Fix f) -> Fix f
  
inject : {default tactics {applyTactic seeSig ; solve }  S : f :<: g} -> f (Fix g) -> Fix g
inject {f=f} {g=g} = In . inj {f=f} {g = g}

-- smart constructor for F
iF : {default tactics {applyTactic seeSig ; solve }  S : F :<: g} -> Fix g -> Fix g -> Fix g
iF {S=S} x y = inject {S = S} (MkF x y)

test : F a -> (F :+: H) a
test x = inj {f=F} {g = F:+:H } x

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

