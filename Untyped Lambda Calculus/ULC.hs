module UCL where
import Data.List


data Lambda = Var Var
    | Lamb Var Lambda
    | App Lambda Lambda
    deriving(Show,Eq)

data Var = A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
    deriving(Show,Eq)


--fV would show all the free variables that have nothing to do with the main part
fV :: Lambda -> [Var]
fV (Var v)                      = [v]
fV (Lamb a v)                   = ((\\) (fV v) [a])
fV (App l1 l2)                  = ((union) (fV l1) (fV l2))


--relabel just rename the variabels
relabel :: Lambda -> Var -> Var -> Lambda
relabel (Var a)  b new             = if a == b then Var new else Var a
relabel (Lamb a l)  b new          = if a == b then Lamb new l else Lamb a l
relabel (App l1 l2) b new          = App (relabel l1 b new) (relabel l2 b new)

--Here is the substitution steps
sub :: Lambda -> Var -> Lambda -> Lambda
sub (Var b) v lam                      = if v == b then (lam) else (Var b)
sub (Lamb a l1) v lam              
    | a == v                                        = Lamb a l1
    | v /= a && not (elem (a) (fV lam))         = Lamb a (sub l1 v lam)
    | otherwise                                     = sub (relabel (Lamb a l1) a new) v lam where
                                                            new = head([A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z] \\ a) where
                                                                a = union (fV lam) [v]
sub (App l1 l2) v lam                        = App (sub l1 v lam) (sub l2 v lam)

--relabel de bu fen jiu jia yi ge condition, kan kan Var t shi bu shi he `a` yi yang, ran hou jiu random qu ti huan

--isNF would find out if the lambda is in normal form or not
isNF :: Lambda -> Bool
isNF (Var a)                    = True
isNF (Lamb _ _)                 = True
isNF (App l1@(Lamb _ _) l2)     = False 
isNF (App l1 l2)                = (isNF l1) && (isNF l2)


--The small step evaluation
ssos :: Lambda -> Lambda
ssos (Var a)                                        = Var a
ssos (Lamb a b)                                     = Lamb a b
ssos (App l1@(Lamb t1 lam) l2)                      = if (isNF l2) then sub lam t1 l2 else App (Lamb t1 lam) (ssos l2)
ssos (App l1 l2)
    | not (isNF l1)                                 = App (ssos l1) l2
    | not (isNF l2)                                 = App l1 (ssos l2)
    | otherwise                                     = App l1 l2



--Evaluation, recurse the ssos step
eval :: Lambda -> Lambda
--eval (Lamb a (Lamb b c))                            = if a == b then (Lamb b c) else (Lamb a (Lamb b c))
eval lam
    | isNF lam              = lam
    | otherwise             = eval (ssos lam)





test1 = Var O
test2 = Lamb (A) (Var B)
test2_1 = Lamb A (Var A)
test3 = Lamb (B) (test2)
test4 = App test2 (Lamb X (Var X))
test4_1 = App test2_1 (Lamb X (Var X))
test5 = Lamb (Y) (Lamb X (Var X))
test5_1 = Lamb Z (Lamb Y (Lamb X (Var X)))
test6 = App test4_1 (Lamb A (Var A))