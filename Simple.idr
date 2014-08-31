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

findSigSimp : (n : Nat) -> Tactic
findSigSimp Z = Solve
findSigSimp (S n)  = GoalType ":<:" 
        (Try (Refine "Here" `Seq` Solve)
             (Try (Refine "Left" `Seq` (Solve `Seq` findSigSimp n))
                  (Refine "Right" `Seq` (Solve `Seq` findSigSimp n))
                       ))
-- findSigSimp (S n)  = GoalType ":<:" 
--         (try [seq [Refine "Here",  Solve],
--               seq [Refine "Left",  Solve, findSigSimp n],
--               seq [Refine "Right", Solve, findSigSimp n],
--               seq [Refine "Split", Solve, findSigSimp n, Solve, findSigSimp n]])
                  
findSig : (n : Nat) -> List (TTName, Binder TT) -> TT -> Tactic
findSig n c g = findSigSimp n



-- destsig : tt -> maybe (tt,tt)
-- destsig (app (app (p _ (ns (un ":+:") ["alacarte"]) _ ) f) g) = just (f,g)
-- destsig _ = nothing


-- subsume : tt -> tt -> tt
-- subsume f g = app (app (p (tcon 0 0) (ns (un ":<:") ["alacarte"]) (ttype (uvar 0))) f) g

-- plus : tt -> tt -> tt
-- plus f g = app (app (p (tcon 15 3) (ns (un ":+:") ["alacarte"]) (ttype (uvar 1))) f) g


-- thisns : list string
-- thisns = ["alacarte"]

-- here : tt -> tt
-- here f = p (dcon 0 0) (ns (un "here") thisns) (subsume f f)

-- arr : TT -> TT -> TT
-- arr s t = Bind (UN "__pi_arg2") (Pi s) t

-- left : TT -> TT -> TT -> TT
-- left f g1 g2 = P (DCon 0 0) (NS (UN "Left") thisNS) (subsume f g1 `arr` subsume f (plus g1 g2))


-- searchSig : (n : Nat) -> TT -> TT -> Maybe Tactic
-- searchSig (S n) f g = if f == g 
--         then Just $ Refine "Here" `Seq` Solve
--         else case destSig g of
--              Just (g1, g2) => 
--                   case (searchSig n f g1, searchSig n f g2) of
--                        (Just t, _) => Just (Refine "Left" `Seq` (Solve `Seq` t))
--                        (_, Just t) => Just (Refine "Right" `Seq` (Solve `Seq` t))
--                        _ => Nothing
--              _ => Nothing
--   where split : Maybe Tactic
--         split = case destSig f of
--                   Just (f1, f2) => 
--                     case (searchSig n f1 g, searchSig n f2 g) of
--                       (Just t1, Just t2) => Just (Refine "Split" `Seq` 
--                                               (Solve `Seq` (t1 `Seq` (Solve `Seq` t2))))
--                       _ => Nothing
--                   _ => Nothing
-- searchSig _ _ _ = Nothing



-- findSig : List (TTName, Binder TT) -> TT -> Tactic
-- findSig c (App (App (P _ (NS (UN ":<:") ["Alacarte"]) _) f) g) =
--         case searchSig 5 f g of
--              Just n => n
--              Nothing => Solve
-- findSig _ _ = Solve


-- findSig' : (n : Nat) -> List (TTName, Binder TT) -> TT -> Tactic
-- findSig' n c (App (App (P nt (NS (UN ":<:") ["Alacarte"]) ty) f) g) =
--          case destSig g of
--               Just (g1, g2) => Exact $ App (left f g1 g2) (here f)
--               Nothing => Solve
-- findSig' _ _ _ = Solve


-- findSig'' : List (TTName, Binder TT) -> TT -> Tactic
-- findSig'' _ _ = Refine "Here" `Seq` Solve


inj : {default tactics { applyTactic findSig 5; solve } S : f :<: g} -> f a -> g a
inj {S = Here} f = f
inj {S = Left l} f = Inl (inj {S = l} f)
inj {S = Right r} f = Inr (inj {S = r} f)
inj {S = Split l r} (Inl x) = inj {S=l} x
inj {S = Split l r} (Inr x) = inj {S=r} x


data F a = MkF a
data G a = MkG a
data H a = MkH a

FGH : Type -> Type
FGH = F :+: G :+: H

FH : Type -> Type
FH = F :+: H

test : F a -> (F :+: H) a
test = inj
