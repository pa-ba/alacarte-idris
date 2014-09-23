module Example

import Dict


data F a = MkF a a

data H a = MkH a

data G a = MkG a

instance Functor F where  
    map f (MkF x y) = MkF (f x) (f y)

instance Functor H where  
    map f (MkH x) = MkH (f x)

instance Functor G where  
    map f (MkG x) = MkG (f x)



-- smart constructor for F
iF : F < g, Fix g -> Fix g -> Fix g
iF x y = inject {f=F} (MkF x y)



test : F a -> (F :+: H) a
test = inj

tacticTest1 : F a -> (F :+: H) a
tacticTest1 = inj


tacticTest2 : F a -> (F :+: H) a
tacticTest2 = inj


tacticTest3 : (F :+: H) a -> (H :+: F) a
tacticTest3 = inj

tacticTest4 : (F :+: H) a -> (H :+: G :+: F) a
tacticTest4 = inj


testAmb : (F) a -> (F :+: F) a
testAmb = inj
