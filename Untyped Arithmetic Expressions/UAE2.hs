module UAE2 where


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



ssos :: UAE -> UAE
-----------------------------(V Wrong) cases

ssos (V Wrong)                      = (V Wrong)
ssos (Succ (V Wrong))               = (V Wrong)
ssos (Pred (V Wrong))               = (V Wrong)
ssos (Ifthenelse (V Wrong) _ _)     = (V Wrong)
ssos (Ifthenelse _ (V Wrong) _)     = (V Wrong)
ssos (Ifthenelse _ _ (V Wrong))     = (V Wrong)
ssos (Iszero (V Wrong))             = (V Wrong)
ssos (Pred (Iszero a))              = (V Wrong)
ssos (Pred (V T))                   = (V Wrong)
ssos (Pred (V F))                   = (V Wrong)
ssos (Succ (Iszero a))              = (V Wrong)
ssos (Succ (V T))                   = (V Wrong)
ssos (Succ (V F))                   = (V Wrong)
ssos (Iszero (V T))                 = (V Wrong)
ssos (Iszero (V F))                 = (V Wrong)
ssos (Ifthenelse (Dev v) a1 a2)     = (V Wrong)
ssos (Ifthenelse (Succ a) a2 a3)    = (V Wrong)
ssos (Ifthenelse (Pred a) a2 a3)    = (V Wrong)
ssos (Ifthenelse (Iszero a) a2 a3)  = (V Wrong)


ssos (Pred(Dev Zero))               = Dev Zero
ssos (Pred(Succ(a)))                = a
ssos (Pred (Dev (SSucc a)))         = Dev a
ssos (Iszero (Dev Zero))            = V T
ssos (Iszero (Succ(a)))             = V F
ssos (Dev Zero)                     = Dev Zero
ssos (Dev (SSucc a))                = Dev (SSucc a)
ssos (Ifthenelse (V T) a2 a3)       = a2
ssos (Ifthenelse (V F) a2 a3)       = a3


ssos (V T)                          = (V T)
ssos (V F)                          = (V F)
ssos (Succ (Dev a))                 = Dev (SSucc a)

ssos (Pred a)                       = Pred (ssos a)
ssos (Iszero a)                     = Iszero (ssos a)
ssos (Succ a)                       = Succ (ssos a)
ssos (Ifthenelse a1 a2 a3)          = Ifthenelse (ssos a1) (ssos a2) (ssos a3)


eval :: UAE -> UAE
eval (V T)                          = (V T)
eval (V F)                          = (V F)
eval (Dev Zero)                     = Dev Zero

----------------------------

eval (Pred a)                       = ssos (Pred (eval a))
eval (Succ a)                       = ssos (Succ (eval a))
eval (Iszero a)                     = ssos (Iszero (eval a))
eval (Ifthenelse a1 a2 a3)          = ssos (Ifthenelse (eval a1) (eval a2) (eval a3))



test :: UAE
test = Pred $ Succ $ Succ $ Succ $ Pred $ Pred $ Succ $ Succ $ Succ $ Dev Zero

test2 :: UAE
test2 = Pred $ Succ $ Succ $ Dev Zero

test3 = Iszero (V T)

test4'' = Succ (Succ (Iszero (Dev Zero)))

test4' = Pred $Succ $Succ (Succ (Iszero (Dev Zero)))

test4 = Pred (Succ (Succ (Succ (Iszero (Pred (Succ (Succ (Succ (Dev Zero)))))))))

test5 = Ifthenelse (Succ (Pred (Succ (V T)))) (V F) (V T)

a = Succ $ Succ $ Dev Zero