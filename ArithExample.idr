module ArithExample

import Dict

data Val a = Lit Int

data Add a = Plus a a

data Mul a = Times a a

instance Functor Val where  
    map _ (Lit x) = Lit x

instance Functor Add where  
    map f (Plus x y) = Plus (f x) (f y)

instance Functor Mul where  
    map f (Times x y) = Times (f x) (f y)

lit : Val :<: f, Int -> Fix f
lit x = inject (Lit x)

plus : Add :<: f, Fix f -> Fix f -> Fix f
plus x y = inject (Plus x y)

times : Mul :<: f, Fix f -> Fix f -> Fix f
times x y = inject (Times x y)


expr1 : Fix (Val :+: Add :+: Mul)
expr1 = times (plus (lit 1) (lit 2)) (lit 3)

class EvalAlg (f : Type -> Type) where
  evalAlg : f Int -> Int

instance (EvalAlg f1, EvalAlg f2) => EvalAlg (f1 :+: f2) where
    evalAlg (Inl x) = evalAlg x
    evalAlg (Inr x) = evalAlg x

eval : (Functor f, EvalAlg f) => Fix f -> Int
eval = fold evalAlg

instance EvalAlg Val where
  evalAlg (Lit l) = l

instance EvalAlg Add where
  evalAlg (Plus x y) = x + y

instance EvalAlg Mul where
  evalAlg (Times x y) = x * y

eval1 : Int
eval1 = eval expr1

data Neg a = Negate a

instance Functor Neg where  
    map f (Negate x) = Negate (f x)


class DesugAlg (f : Type -> Type) (g : Type -> Type) where
  desugAlg : f (Fix g) -> Fix g

instance (DesugAlg f1 g, DesugAlg f2 g) => DesugAlg (f1 :+: f2) g where
    desugAlg (Inl x) = desugAlg x
    desugAlg (Inr x) = desugAlg x

desug : (Functor f, DesugAlg f g) => Fix f -> Fix g
desug = fold desugAlg


instance (Functor g, Val :<: g, Mul :<: g) => DesugAlg Neg g where
  desugAlg (Negate x) = times (lit (-1)) x
