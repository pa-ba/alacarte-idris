module Alacarte

import Language.Reflection
import Language.Reflection.Utils



infixl 9 :+:
infixl 8 :<:
infixl 8 :=:

%language ErrorReflection

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



-- weaker equality on TT
eqTT : TT -> TT -> Bool
eqTT (P Bound n1 _) (P Bound n2 _) = n1 == n2
eqTT x y = x == y

findInCtxt : TT -> TT -> List (TTName, TT, TT) -> Maybe TT
findInCtxt f g ((n,f',g') :: r) = if eqTT f f' && eqTT g g' 
                                  then Just (P Bound n `(~f :<: ~g))
                                  else findInCtxt f g r
findInCtxt f g [] = Nothing


findSub : TT -> TT -> List (TTName, TT, TT) -> Either TT TT
findSub f g ctxt = if eqTT f g then Right `(here {f=~f}) 
                   else case findInCtxt f g ctxt of
                     Just t => Right t
                     Nothing => case g of
                        `(~a :+: ~b) => case (findSub f a ctxt, findSub f b ctxt) of
                             (Right l, _) => Right `(left {f=~f} {g1=~a} {g2=~b} ~l)
                             (_, Right r) => Right `(right {f=~f} {g1=~a} {g2=~b} ~r)
                             _           => next f
                        _  => next f
  where next : TT -> Either TT TT
        next `(~f1 :+: ~f2) = do l <- findSub f1 g ctxt
                                 r <- findSub f2 g ctxt
                                 return `(split {f1=~f1} {g=~g} {f2=~f2} ~l ~r)
        next f = Left f

sigList : TT -> List TT
sigList `(~f :+: ~g) = sigList f ++ sigList g
sigList f = [f]


hasDupl' : List TT -> Maybe TT
hasDupl' [] = Nothing
hasDupl'  (x::xs) = if elem x xs then Just x else hasDupl' xs

hasDupl : TT -> Maybe TT
hasDupl = hasDupl' . sigList

fromBinder : Binder TT -> TT
fromBinder (Lam x) = x
fromBinder (Pi x y) = y
fromBinder (Let x y) = y
fromBinder (NLet x y) = y
fromBinder (Hole x) = x
fromBinder (GHole x) = x
fromBinder (Guess x y) = y
fromBinder (PVar x) = x
fromBinder (PVTy x) = x

getGoals : (TTName, Binder TT) -> Maybe (TTName, TT, TT)
getGoals (n, t) = case fromBinder t of
                    `(~f :<: ~g) => Just (n, f, g)
                    _              => Nothing

tacticSub : List (TTName, Binder TT) -> TT -> Tactic
tacticSub ctxt `(~x :<: ~y) = 
          case hasDupl x of
            Just x' => Fail [TermPart x', TextPart "occurs twice in", TermPart x]
            _ => case hasDupl y of
                   Just y' => Fail [TermPart y', TextPart "occurs twice in", TermPart y]
                   _ => case findSub x y (mapMaybe getGoals ctxt) of
                          Right prf  => Exact prf
                          Left f => Fail [TermPart f, TextPart "does not occur in", TermPart y]
tacticSub ctxt g = Fail [TermPart g, TextPart "is not a goal of the form f :<: g"]


syntax [f] "<" [g] "," [t] = (Functor f, Functor g) => 
       {default tactics {applyTactic tacticSub ; solve }  S : f :<: g} -> t

%error_handler
subErr : ErrorHandler
subErr (CantSolveGoal g ctxt) = case g of
       `(~x :<: ~y) => case tacticSub [] g of
                            Fail err => Just [TextPart "Cannot derive", TermPart g, SubReport err]
                            _ => Nothing
       _ => Nothing
subErr _ = Nothing

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

