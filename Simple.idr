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


data (:<:) : (Type -> Type) -> (Type -> Type) -> Type where
     Here : f :<: f
     Left : f :<: g1 -> f :<: (g1 :+: g2)
     Right : f :<: g2 -> f :<: (g1 :+: g2)
     Split : f1 :<: g -> f2 :<: g -> (f1 :+: f2) :<: g


findLtPrf : TT -> TT -> Maybe TT
findLtPrf `(~f1 :+: ~f2) g = do l <- findLtPrf f1 g
                                r <- findLtPrf f2 g
                                return `(Split {f1=~f1} {g=~g} {f2=~f2} ~l ~r)
findLtPrf f `(~a :+: ~b) = case (findLtPrf f a, findLtPrf f b) of
                             (Just l, _) => Just `(Left {f=~f} {g1=~a} {g2=~b} ~l)
                             (_, Just r) => Just `(Right {f=~f} {g1=~a} {g2=~b} ~r)
                             _           => Nothing
findLtPrf f1 f2 = if f1 == f2 then Just `(Here {f=~f1}) else Nothing
findLtPrf _ _ = Nothing

seeSig : List (TTName, Binder TT) -> TT -> Tactic
seeSig ctxt `(~x :<: ~y) with (findLtPrf x y)
  | Just prf  = Exact prf
  | Nothing   = Fail [TextPart "not found prf"]
seeSig ctxt g = Fail [TextPart "not the right goal", TermPart g]

inj : {default tactics {applyTactic seeSig ; solve }  S : f :<: g} -> f a -> g a
inj {S = Here} f = f
inj {S = Left l} f = Inl (inj {S = l} f)
inj {S = Right r} f = Inr (inj {S = r} f)
inj {S = Split l r} (Inl x) = inj {S=l} x
inj {S = Split l r} (Inr x) = inj {S=r} x


data F a = MkF a

data H a = MkH a

data G a = MkG a

test : F a -> (F :+: H) a
test x = inj {f=F} {g = F:+:H } x

tacticTest1 : F :<: F
tacticTest1 = proof applyTactic seeSig

tacticTest1' : F :<: F
tacticTest1' = proof search

tacticTest2 : F :<: (F :+: H)
tacticTest2 = proof applyTactic seeSig

tacticTest2' : F :<: (F :+: H)
tacticTest2' = proof search

tacticTest3 : (F :+: H) :<: (H :+: F)
tacticTest3 = proof applyTactic seeSig

-- For this, Idris's proof search breaks down
-- tacticTest3' : (F :+: H) :<: (H :+: F)
-- tacticTest3' = proof search

tacticTest4 : (F :+: H) :<: (H :+: G :+: F)
tacticTest4 = proof applyTactic seeSig

