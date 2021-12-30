module UAE3 where


data UAE = V V
    | Dev Nv
    | Succ (UAE)
    | Pred (UAE)
    | Iszero (UAE)
    | Ifthenelse UAE UAE UAE
    deriving (Show,Eq)

data V = T
    | F
    | Wrong
    deriving (Show,Eq)


data Nv = Zero
        | SSucc (Nv)
    deriving (Show,Eq)





bsos :: UAE -> UAE
-----------------------------(V Wrong) cases
bsos (V Wrong)                      = (V Wrong)
bsos (Succ (V Wrong))               = (V Wrong)
bsos (Pred (V Wrong))               = (V Wrong)
bsos (Ifthenelse (V Wrong) _ _)     = (V Wrong)
bsos (Ifthenelse _ (V Wrong) _)     = (V Wrong)
bsos (Ifthenelse _ _ (V Wrong))     = (V Wrong)
bsos (Iszero (V Wrong))             = (V Wrong)
bsos (Pred (Iszero a))              = (V Wrong)
bsos (Pred (V T))                   = (V Wrong)
bsos (Pred (V F))                   = (V Wrong)
bsos (Succ (Iszero a))              = (V Wrong)
bsos (Succ (V T))                   = (V Wrong)
bsos (Succ (V F))                   = (V Wrong)
bsos (Iszero (V T))                 = (V Wrong)
bsos (Iszero (V F))                 = (V Wrong)
bsos (Ifthenelse (Dev v) a1 a2)     = (V Wrong)
bsos (Ifthenelse (Succ a) a2 a3)    = (V Wrong)
bsos (Ifthenelse (Pred a) a2 a3)    = (V Wrong)
bsos (Ifthenelse (Iszero a) a2 a3)  = (V Wrong)

bsos (Dev nv)                       = Dev nv
bsos (Ifthenelse a1 a2 a3)
    | a1 == (V T)                   = a2
    | a1 == (V F)                   = a3

bsos (Pred (Dev Zero))              = Dev Zero
bsos (Pred(Dev (SSucc nv)))         = Dev nv
bsos (Iszero (Dev Zero))            = V T
bsos (Iszero (Succ(a)))             = V F
bsos (Dev Zero)                     = Dev Zero
bsos (Dev (SSucc a))                = Dev (SSucc a)
bsos (Succ (Dev nv))                = Dev (SSucc nv)


bsos (V T)                          = (V T)
bsos (V F)                          = (V F)

bsos (Pred t)                       = bsos (Pred (bsos t))
bsos (Iszero t)                     = bsos (Iszero (bsos t))
bsos (Succ t)                       = bsos (Succ (bsos t))






test :: UAE
test = Pred $ Succ $ Succ $ Succ $ Pred $ Pred $ Succ $ Succ $ Succ $ Dev Zero

test2 :: UAE
test2 = Pred $ Succ $ Succ $ Dev Zero

test3 = Iszero (V T)

test4 = Pred (Succ (Succ (Succ (Iszero (Pred (Succ (Succ (Succ (Dev Zero)))))))))

test5 = Ifthenelse (Succ (Pred (Succ (V T)))) (V F) (V T)

a = Succ $ Succ $ Dev Zero

tt = Ifthenelse (V T) (V F) (V T)
tt2 = Ifthenelse (V T) (tt) (a)