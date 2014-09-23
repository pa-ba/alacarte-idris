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
  MkSub : (injMethod : (a: Type) -> f a -> g a) ->
          (prjMethod : (a: Type) -> g a -> Maybe (f a)) ->
          f :<: g

here : f :<: f
here = MkSub (\ _ => id) (\ _ => Just)

left : (f :<: g1) -> f :<: (g1 :+: g2)
left (MkSub inj prj) = MkSub 
     (\ a => Inl . inj a) 
     (\ a, x => case x of
                 Inl x' => prj a x'
                 Inr x' => Nothing)

right : (f :<: g2) -> f :<: (g1 :+: g2)
right (MkSub inj prj) = MkSub 
      (\ a => Inr . inj a)
      (\ a, x => case x of
                 Inl x => Nothing
                 Inr x => prj a x)

split : (f1 :<: g) -> (f2 :<: g) -> (f1 :+: f2) :<: g
split (MkSub inj1 prj1) (MkSub inj2 prj2) = MkSub inj prj
      where inj a (Inl x) = inj1 a x
            inj a (Inr x) = inj2 a x
            prj a x = map Inl (prj1 a x) <|> map Inr (prj2 a x)

findSub : TT -> TT -> Maybe TT
findSub f g = if f == g then Just `(here {f=~f}) 
                else case g of
                `(~a :+: ~b) => case (findSub f a, findSub f b) of
                             (Just l, _) => Just `(left {f=~f} {g1=~a} {g2=~b} ~l)
                             (_, Just r) => Just `(right {f=~f} {g1=~a} {g2=~b} ~r)
                             _           => next f
                _  => next f
  where next : TT -> Maybe TT
        next `(~f1 :+: ~f2) = do l <- findSub f1 g
                                 r <- findSub f2 g
                                 return `(split {f1=~f1} {g=~g} {f2=~f2} ~l ~r)
        next _ = Nothing

isGoal : TT -> TT -> TT -> Bool
isGoal f g `(~f' :<: ~g') = f' == f && g' == g
isGoal _ _ _ = False

findInCtxt : TT -> TT -> List (TTName, Binder TT) -> Maybe TT
findInCtxt f g (x :: r) = case x of
           (n, PVar t) => if isGoal f g t then Just (P Bound n t)
                          else findInCtxt f g r
           _ => findInCtxt f g r
findInCtxt f g [] = Nothing


tacticSub : List (TTName, Binder TT) -> TT -> Tactic
tacticSub ctxt `(~x :<: ~y) = case findInCtxt x y ctxt of
       Just prf => Exact prf
       Nothing => case findSub x y of
               Just prf  => Exact prf
               Nothing   => Fail [TextPart "not found prf"]
tacticSub ctxt g = Fail [TextPart "not the right goal", TermPart g]



syntax [f] "<" [g] "," [t] = (Functor f, Functor g) => 
       {default tactics {applyTactic tacticSub ; solve }  S : f :<: g} -> t

inj : f < g, f a ->  g a
inj x {S = S} {a = a} = injMethod S a x

prj : f < g, g a -> Maybe (f a)
prj x {S = S} {a = a} = prjMethod S a x


data Fix : (Type -> Type) -> Type where
  In : f (Fix f) -> Fix f
  

%default partial

fold : Functor f => (f a -> a) -> Fix f -> a
fold f (In x) = f (map (fold f) x)

%default total

inject : f < g, f (Fix g) -> Fix g
inject x = In (inj x)

