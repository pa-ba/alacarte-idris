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
iF x y = inject (MkF x y)



test1 : F a -> (F :+: H) a
test1 = inj

test2 : Functor g => g a -> g a
test2 = inj


test3 : g < h, (F :+: g) a -> (F :+: h) a
test3 = inj

test7 : g < g', h < h', (h :+: g) a -> (g' :+: h') a
test7 = inj


test4 : F a -> (F :+: H) a
test4 = inj


test5 : (F :+: H) a -> (H :+: F) a
test5 = inj

test6 : (F :+: H) a -> (H :+: G :+: F) a
test6 = inj

