module Example

import Dict


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
