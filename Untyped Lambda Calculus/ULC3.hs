module ULC3 where

import Data.List

-- q1
data Var = A | B | C | D | E | F | G | H | I | J | K | L | M 
        | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
        deriving (Show, Eq)

data Term = Var Var
        | Lambda Var Term
        | Apply Term Term
        deriving (Show, Eq)

-- q2
fv :: Term -> [Var]
fv (Var x) = [x]
fv (Lambda x t) = (fv t) \\ [x]
fv (Apply t1 t2) = (fv t1)`union`(fv t2)

--q3
allvar :: Term -> [Var]
allvar (Var x) = [x]
allvar (Lambda x t) = (allvar t)`union`[x]
allvar (Apply t1 t2) = (allvar t1)`union`(allvar t2)

relabel :: Term -> Var -> Var -> Term
relabel t x y = if x`elem`((allvar t)\\(fv t)) && y`notElem`(allvar t)
                then rl t x y
                else t

rl :: Term -> Var -> Var -> Term
rl (Var v) x y = if v == x then Var y else Var v
rl (Lambda v t) x y = if v == x 
                        then Lambda y (rl t x y) 
                        else Lambda v (rl t x y)
rl (Apply t1 t2) x y = Apply (rl t1 x y) (rl t2 x y)

-- q4
sub :: Term -> Var -> Term -> Term
sub (Var y) x s = if y == x then s else Var y
sub (Lambda y t) x s = if y == x
                        then Lambda y t
                        else if y`notElem`(fv s) 
                                then Lambda y (sub t x s)
                                else let 
                                        variable = [A, B, C, D, E, F, G, H, I, J, K, L, M,
                                                N, O, P, Q, R, S, T, U, V, W, X, Y, Z]
                                        z = head (((variable\\(allvar t))\\[x])\\(fv s))
                                        new = relabel (Lambda y t) y z
                                        in sub new x s
sub (Apply t1 t2) x s = Apply (sub t1 x s) (sub t2 x s)

-- q5
isNF :: Term -> Bool
isNF (Val Z) = True
isNF (Var _) = True
isNF (Lambda _ _) = True
isNF (Apply (Lambda _ _) t2) = False
isNF (Apply t1 t2) = (isNF t1) && (isNF t2)

-- q6
ssos :: Term -> Term
ssos (Var v) = Var v
ssos (Lambda x t) = Lambda x t
ssos (Apply (Lambda x t) v) = if (isNF v) 
                              then sub t x v 
                              else Apply (Lambda x t) (ssos v)
ssos (Apply t1 t2) = if not (isNF t1)
                    then Apply (ssos t1) t2
                    else if (isNF t2)
                        then Apply t1 t2
                        else Apply t1 (ssos t2)

-- q7
eval :: Term -> Term
eval t = if (t == (ssos t))
        then t
        else eval (ssos t)

-- q8
tru :: Term
tru = Lambda T (Lambda F (Var T))

fls :: Term
fls = Lambda T (Lambda F (Var F))

lnot :: Term -> Term
lnot b = eval(Apply (Apply b fls) tru)

land :: Term -> Term -> Term
land b c = eval(Apply (Apply b c) fls)

lor :: Term -> Term -> Term
lor b c = eval(Apply (Apply b tru) c)

-- q9 a
nsum :: Term -> Term -> Term
nsum m n = eval(Apply (Apply (Lambda M (Lambda N (Lambda S (Lambda Z (Apply (Apply (Var M) (Var S)) (Apply (Apply (Var N) (Var S)) (Var Z))))))) m) n)

-- q9 b
ntimes :: Term -> Term -> Term
ntimes m n = eval(Apply (Apply (Lambda M (Lambda N (Apply (Apply (Var M) (Lambda L (Lambda S (Lambda Z (Apply (Apply (Var N) (Var S)) (Apply (Apply (Var L) (Var S)) (Var Z))))))) c0))) m) n)

-- q9 c
pair :: Term
pair = Lambda F (Lambda S (Lambda B (Apply (Apply (Var B) (Var F)) (Var S))))

pfst :: Term
pfst = Lambda P (Apply (Var P) tru)

psnd :: Term
psnd = Lambda P (Apply (Var P) fls)

zz :: Term
zz = Lambda B (Apply (Apply (Var B) c0) c0)

ss :: Term
ss = Lambda P (Apply (Apply pair (Apply psnd (Var P))) (Apply (Lambda N (Lambda S (Lambda Z (Apply (Apply c1 (Var S)) (Apply (Apply (Var N) (Var S)) (Var Z)))))) (Apply psnd (Var P))))

npred :: Term -> Term
npred c = eval(Apply (Lambda M (Apply pfst (Apply (Apply (Var M) ss) zz))) c)

-- 0,1,2,3 for test
c0 :: Term
c0 = Lambda S (Lambda Z (Var Z))

c1 :: Term
c1 = Lambda S (Lambda Z (Apply (Var S) (Var Z)))

c2 :: Term
c2 = Lambda S (Lambda Z (Apply (Var S) (Apply (Var S) (Var Z))))

c3 :: Term
c3 = Lambda S (Lambda Z (Apply (Var S) (Apply (Var S) (Apply (Var S) (Var Z)))))