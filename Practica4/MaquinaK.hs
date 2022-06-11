{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Practica4.MaquinaK where
import Data.List
import Data.Maybe
-----------------------------------------------------------
--      Lenguajes de Programación y sus Paradigmas       --
-----------------------------------------------------------
--                      Práctica 4                       --
-----------------------------------------------------------
--Integrantes:                                           --
--1. Bernal Márquez Erick                       317042522--
--2. Deloya Andrade Ana Valeria                 317277582--
--3. Villegas Barrón César                      314002033--
-----------------------------------------------------------

--------------------------------------
--      Extensión del lenguaje      --
--------------------------------------
type Identifier = String
data Expr = V Identifier | I Int | B Bool
            | Fn Identifier Expr
            | Succ Expr | Pred Expr
            | Add Expr Expr | Mul Expr Expr
            | Not Expr | Iszero Expr
            | And Expr Expr | Or Expr Expr
            | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
            | If Expr Expr Expr
            | Let Identifier Expr Expr
            | L Int
            | Alloc Expr
            | Dref Expr
            | Assig Expr Expr
            | Void
            | Seq Expr Expr
            | While Expr Expr
            | App Expr Expr 
            | Raise Expr 
            | Handle Expr Identifier Expr deriving(Eq, Show)


data Frame = AddFL Expr | AddFR Expr
            | MulFL Expr | MulFR Expr
            | SuccF | PredF 
            | AndFL Expr | AndFR Expr
            | OrFL Expr | OrFR Expr
            | NotF | IsZeroF
            | LtFL Expr | LtFR Expr
            | GtFL Expr | GtFR Expr
            | EqFL Expr | EqFR Expr
            | IfF Expr Expr
            | LetM Identifier Expr
            | AppFL Expr | AppFR Expr
            | RaiseF 
            | HandleF Identifier Expr


instance Show Frame where 
    show e = case e of
        (AddFL a) -> "Add("++show a++")" 
        (AddFR a) -> "Add("++show a++")" 
        (MulFL a) -> "Mul("++show a++")" 
        (MulFR a) -> "Mul("++show a++")" 
        (SuccF) -> "Succ()"
        (PredF) -> "Pred()" 
        (AndFL a) -> "And("++show a++")" 
        (AndFR a) -> "And("++show a++")"
        (OrFL a) -> "Or("++show a++")"
        (OrFR a) -> "Or("++show a++")"
        (NotF) -> "Not()"
        (IsZeroF) -> "IsZero()"
        (LtFL a) -> "Lt("++show a++")"
        (GtFL a) -> "Gt("++show a++")"
        (LtFR a) -> "Lt("++show a++")"
        (GtFR a) -> "Gt("++show a++")"
        (EqFL a) -> "Eq("++show a++")"
        (EqFR a) -> "Eq("++show a++")"
        (IfF a b) -> "If("++show a++", "++show b++")"
        (LetM a b) -> "LetM("++show a++", "++show b++")"
        (AppFL a) -> "Eq("++show a++")"
        (AppFR a) -> "Eq("++show a++")"
        RaiseF -> "Raise()"
        (HandleF a b) -> "Handle("++show a++", "++show b++")"


-- 5. Extender la funcion frVars 
frVars :: Expr -> [Identifier]
frVars (V i)  = [i]
frVars (I n)  = []
frVars (B b)  = []
frVars (Fn x e) = filter (/= x) (frVars e)
frVars (Succ b)  = frVars b
frVars (Pred p)  = frVars p
frVars (Add a b) = frVars a `union` frVars b
frVars (Mul a b) = frVars a `union` frVars b
frVars (Not p) = frVars p
frVars (Iszero i) = frVars i
frVars (And p q) = frVars p `union` frVars q
frVars (Or p q)  = frVars p `union` frVars q
frVars (Lt p q) = frVars p `union` frVars q
frVars (Gt p q) = frVars p `union` frVars q
frVars (Eq p q) = frVars p `union` frVars q
frVars (If a b c) = frVars a `union` frVars b `union` frVars c
frVars (Let x a b) = frVars a `union` filter (/=x) (frVars b)
frVars (L i) = []
frVars (Alloc e) = frVars e
frVars (Dref e) = frVars e
frVars (Assig a b) = frVars a `union` frVars b
frVars Void = []
frVars (Seq a b) = frVars a `union` frVars b
frVars (While a b) = frVars a `union` frVars b
frVars (App a b) = frVars a `union` frVars b
frVars (Raise a) = frVars a
frVars (Handle a x c) = frVars a `union` filter (/=x) (frVars c)


-- 5. Extender la funcion subst
type Substitution = (Identifier, Expr)
subst :: Expr -> Substitution -> Expr
subst (V x) (id, e) | x == id = e
                    | otherwise = V x
subst (I n) _ = I n
subst (B b) _ = B b
subst (Fn x e) s |              x == fst s = error "Se hará una sustitución en una variable ligada, busca una alfa equivalencia de tu expresión Fn"
                 | x `elem` frVars (snd s) = error "La expresion a sustituir tiene una variable con el mismo nombre que una ligada a una expresión Fn, busca una alfa equivalencia"
                 |               otherwise = Fn x (subst e s)
subst (Succ c) s = Succ (subst c s)
subst (Pred p) s = Pred (subst p s)
subst (Add a b) s = Add (subst a s) (subst b s)
subst (Mul a b) s = Mul (subst a s) (subst b s)
subst (Not b) s = Not (subst b s)
subst (Iszero a) s = Iszero (subst a s)
subst (And p q) s = And (subst p s) (subst q s)
subst (Or p q) s = Or (subst p s) (subst q s)
subst (Lt p q) s = Lt (subst p s) (subst q s)
subst (Gt p q) s = Gt (subst p s) (subst q s)
subst (Eq p q) s = Eq (subst p s) (subst q s)
subst (If c a b) s = If (subst c s) (subst a s) (subst b s)
subst (Let x e1 e2) (y,e) |            x == y = error "Se hará una sustitución en una variable ligada, busca una alfa equivalencia de una expresión Let"
                          | x `elem` frVars e = error "La expresion a sustituir tiene una variable con el mismo nombre que una ligada a una expresión Let, busca una alfa equivalencia"
                          |         otherwise = Let x (subst e1 (y,e)) (subst e2 (y,e))
subst (L i) s = L i
subst (Alloc a) s = Alloc (subst a s)
subst (Dref a) s = Dref (subst a s)
subst Void s = error "No se puede sustituir algo vacio"
subst (Assig a b) s = Assig (subst a s) (subst b s)
subst (Seq a b) s = Seq (subst a s) (subst b s)
subst (While a b) s = While (subst a s) (subst b s)
subst (App a b) s = App (subst a s) (subst b s)
subst (Raise a) s = Raise (subst a s)
--subst (Handle a x b) s = Mmmm xd


-- Defincion de pila de marcos
data Stack = Empty | S Frame Stack


--Definicion de los estados
data State = E Stack Expr
            | R Stack Expr
            | P Stack Expr


-- Re implementa esta función para que dado un estado, devuelva un paso de transicion,
-- es decir, eval1 s = s’ si y sólo si s →_k s’
eval1 :: State -> State
eval1 (E s (I n)) = R s (I n)
eval1 (E s (B b)) = R s (B b)
eval1 (E s (V v)) = R s (V v)

-- Extiende esta función para que dado un estado, aplica la funcion de transicion
-- hasta llegar a un estado bloqueado, es decir, evals s = s’ si y sólo si s →∗_k s’ 
-- y s’ esta bloqueado o la pila esta vacia.
evals :: State -> State 
evals = error "D:"


-- Extiende esta función para que dada una expresión, devuelva la evaluación de un programa 
--tal que evale e = e’ syss e→∗_k e’, e’ es un valor devuelto a una pila vacia. En caso de que e’
--no sea un valor cuando la pila quede vacia o se llegue a un estado bloqueado deberá 
--mostrar un mensaje de error particular del operador que lo causó. 
{- NOTA: aunque en esta funcion no es visible la evaluacion
debe hacerse utilizando la maquina K. Hint: utiliza la funcion evals.-}
evale :: Expr -> Expr 
evale = error "D:"


