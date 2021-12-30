module Gany9 where

import Data.List
import Debug.Trace
import Data.Maybe

data T = App T T
       | If T T T 
       | Succ T
       | Pred T
       | IsZero T
       | Val V
       | Let Label T T
       | Seq T T
       | Alloc T
       | DeRef T
       | Assign T T 
  deriving (Show, Eq)
  
data V = Tru | Fls | Z | SuccNV V | UnitV | Location Loc | Var Label | L Label Type T deriving(Show, Eq)
  
data Label = A | C | D | E | F | G | H | I | J | K 
    | M | O | P | Q | R | S | U | W | X | Y  
    deriving (Show, Eq)
    
data Loc = L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9
    deriving (Show, Eq)

data Type = BOOL | NAT | Unit | Arrow Type Type | Ref Type deriving (Show, Eq)

type Gamma = [(Label, Type)] 

type Mu = [(Loc, V)]

freeVars :: T -> [Label] 
freeVars (Val Z)                                                                                = []
freeVars (Val (Var lab))                                                                        = [lab]
freeVars (Val (L label _ t))                                                                    = (freeVars t) \\ [label]
freeVars (App t1 t2)                                                                            = (freeVars t1)`union`(freeVars t2)
freeVars (Succ t)                                                                               = freeVars t
freeVars (Pred t)                                                                               = freeVars t
freeVars (IsZero t)                                                                             = freeVars t
freeVars (If t1 t2 t3)                                                                          = (freeVars t1)`union`(freeVars t2)`union`(freeVars t3)
freeVars (Seq t1 t2)                                                                            = (freeVars t1)`union`(freeVars t2)
freeVars (Let label t1 t2)                                                                      = ((freeVars t1)`union`(freeVars t2)) \\ [label]



allvar :: T -> [Label]
allvar (Val (Var x))                                                                            = [x]
allvar (Val (L lab typ t))                                                                      = (allvar t)`union`[lab]
allvar (App t1 t2)                                                                              = (allvar t1)`union`(allvar t2)
allvar (Succ t)                                                                                 = allvar t
allvar (Pred t)                                                                                 = allvar t
allvar (IsZero t)                                                                               = allvar t
allvar (If t1 t2 t3)                                                                            = (allvar t1)`union`(allvar t2)`union`(allvar t3)
allvar (Let label t1 t2)                                                                        = (allvar t1)`union`(allvar t2)`union`[label]
allvar (Seq t1 t2)                                                                              = (allvar t1)`union`(allvar t2)


relabel :: T -> Label -> Label -> T 
relabel t lab1 lab2 = if lab1`elem`((allvar t)\\(freeVars t)) && lab2`notElem`(allvar t)
                then rl t lab1 lab2
                else t

rl :: T -> Label -> Label -> T
rl (Val (Var v)) x y = if v == x then Val (Var y) else Val (Var v)
rl (Val (L v typ t)) x y = if v == x 
                         then Val (L y  typ (rl t x y))
                         else Val (L v  typ (rl t x y))
rl (App t1 t2) x y = App (rl t1 x y) (rl t2 x y)



sub :: T -> Label -> T -> T 
sub (Val (Var y)) lab s                                                                         = if y == lab then s else Val (Var y)
sub (Val (L lab typ t)) x s = if lab == x
                        then Val (L lab typ t)
                        else if lab`notElem`(freeVars s) 
                                then Val (L lab typ (sub t x s))
                                else let 
                                        variable = [A, C, D, E, F, G, H, I, J, K, M,
                                                 O, P, Q, R, S, U, W, X, Y]
                                        z = head (((variable\\(allvar t))\\[x])\\(freeVars s))
                                        new = relabel (Val (L lab typ t)) lab z
                                        in sub new x s
sub (App t1 t2) x s                                                                             = App (sub t1 x s) (sub t2 x s)
sub (Succ t) x s                                                                                = Succ (sub t x s)
sub (Pred t) x s                                                                                = Pred (sub t x s)
sub (IsZero t) x s                                                                              = IsZero (sub t x s)
sub (If t1 t2 t3) x s                                                                           = If (sub t1 x s) (sub t2 x s) (sub t3 x s)

isNF :: T -> Bool
isNF (Val (Var _))                                                                              = True
isNF (Val (L _ _ _))                                                                            = True
isNF (Val Z)                                                                                    = True 
isNF (App t1 t2)                                                                                = (isNF t1) && (isNF t2)
isNF (App (Val (L _ _ _)) t2)                                                                   = False
isNF _                                                                                          = False


ssos :: (T, Mu) -> (T, Mu)
--one step rule for bool part
ssos (Val Tru,a)                                                                                = (Val Tru,a)
ssos (Val Fls,a)                                                                                = (Val Fls,a)
ssos (If (Val Tru) t2 t3, a)                                                                    = (t2,a)
ssos (If (Val Fls) t2 t3, a)                                                                    = (t3,a)
ssos (If t1 t2 t3, a)                                                                           = ((If (eval t1) t2 t3), a)

--one step rule for Nv part
ssos (Val (SuccNV t),a)                                                                         = (Val (SuccNV t),a)
ssos (Val Tru,a)                                                                                = (Val Tru,a)
ssos (Val Fls,a)                                                                                = (Val Fls,a)
ssos (Val Z,a)                                                                                  = (Val Z,a)
ssos (Succ (Val nv),a)                                                                          = (Val (SuccNV nv),a)
ssos (Pred (Val Z), a)                                                                          = (Val Z,a)
ssos (Pred (Succ nv),a)                                                                         = (nv,a)
ssos (Pred (Val (SuccNV nv)),a)                                                                 = (Val nv,a)
ssos (IsZero (Val Z),a)                                                                         = ((Val Tru),a)
ssos ((IsZero (Val (SuccNV Z))),a)                                                              = (Val Fls,a)
ssos (IsZero (Succ nv), a)                                                                      = ((Val Fls),a)
ssos ((Succ t),a)                                                                               = (Succ (eval t),a)
ssos (Pred t, a)                                                                                = (Pred (eval t),a)
ssos (IsZero t, a)                                                                              = (IsZero (eval t),a)

--one step rule for Lambda part
ssos (Val (Var lab),a)                                                                          = (Val (Var lab),a)
ssos (Val (L lab typ t),a)                                                                      = (Val (L lab typ t),a)
ssos (App (Val (L x typ t)) (Val v), a)                                                         = (sub t x (Val v), a) 
ssos (App (Val (L lab typ t)) v,a)                                                              = if (isNF v) then ((sub t lab v),a) else ssos (App (Val (L lab typ t)) (eval v),a)
ssos (App t1 t2,a) = if not (isNF t1)
                    then (App (eval t1) t2,a)
                    else if (isNF t2)
                        then (App t1 t2,a)
                        else (App t1 (eval t2),a)


--One step rule for unit type
ssos ((Val UnitV),a)                                                                            = (Val UnitV,a)


--one step rule for Let binding part
ssos ((Let lab (Val v) t),a)                                                                    = ((sub t lab (Val v)),a)
ssos ((Let lab v t),a)                                                                          = (Let lab (eval v) t,a)

--one step rule for sequencing part
ssos ((Seq (Val UnitV) t2),a)                                                                   = (t2,a)
ssos ((Seq t1 t2),a)                                                                            = ((Seq (eval t1) t2),a)






typeaux :: Gamma -> [Label]
typeaux ((l, _):gamma)                                                                          = [l]++typeaux(gamma)
typeaux []                                                                                      = []





typeCheck :: Gamma -> T -> Maybe Type
--type rule for bool
typeCheck _ (Val Tru)                                                                          = Just BOOL
typeCheck _ (Val Fls)                                                                          = Just BOOL
typeCheck gamma (If t1 t2 t3)                                                                  = if ((typeCheck gamma (eval t1)) == Just BOOL && (typeCheck gamma (eval t2)) == (typeCheck gamma (eval t3))) then (typeCheck gamma (eval t2)) else Nothing


--type rule for Nat
typeCheck _ (Val Z)                                                                            = Just NAT
typeCheck gamma (Succ t1)                                                                      = if (typeCheck gamma (eval t1)) == Just NAT then Just NAT else Nothing
typeCheck gamma (Val (SuccNV t1))                                                              = if (typeCheck gamma (eval (Val t1))) == Just NAT then Just NAT else Nothing
typeCheck gamma (Pred t1)                                                                      = if (typeCheck gamma (eval t1)) == Just NAT then Just NAT else Nothing
typeCheck gamma (IsZero t1)                                                                    = if (typeCheck gamma (eval t1)) == Just NAT then Just BOOL else Nothing

--type rule for Lambda
typeCheck [] (Val (Var y))                                                                      = Nothing
typeCheck [] (Val (L x1 typ1 y1))                                                               = typeCheck [(x1,typ1)] y1
typeCheck [] (App x1 y1)                                                                        = typeCheck [] x1
typeCheck gamma (Val (Var y))                                                                   = if y `elem` lst then Just (snd (gamma!!fromJust(func))) else Nothing where lst = map fst gamma
                                                                                                                                                                             func = elemIndex y lst
typeCheck gamma (Val (L x1 typ1 y1))                                                            = typeCheck (gamma++[(x1,typ1)]) y1 
typeCheck gamma (App x1 y1)                                                                     = case (typeCheck gamma x1) of 
    Just (Arrow typ1 typ2)                                                                      -> if (typeCheck gamma y1 == Just typ1) then Just typ2 else Nothing
    _                                                                                           -> Nothing
--type rule for Unit as Unit type has only typing rule
typeCheck [] (Val UnitV)                                                                        = Just Unit

--type rule for Let binding
typeCheck gamma (Let x1 t1 t2)                                                                  = if x1 `notElem` typeaux(gamma) then Just (fromJust (typeCheck ((x1,typ):gamma) t2)) else Nothing
                                                                                                    where typ = fromJust (typeCheck gamma t1)


--type rule for Sequencing
typeCheck [] (Seq t1 t2)                                                                        = if t1 == (Val UnitV) then typeCheck [] t2 else Nothing
typeCheck gamma (Seq t1 t2)                                                                     = if t1 == (Val UnitV) then typeCheck gamma t2 else Nothing



eval :: T -> T 
eval t 
    | ssos(t,[]) == (t,[]) = t
    | otherwise = eval (fst(ssos(t, [])))

run :: T -> T
run t                                                                                           = if typeCheck [] t == Nothing then error "Error! Typechecking Failed!" else eval t 




--nonsense

