{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module Practica3.MiniC where
import Data.List
import Data.Maybe
-----------------------------------------------------------
--      Lenguajes de Programación y sus Paradigmas       --  
-----------------------------------------------------------            
--                      Práctica 3                       --
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
            | App Expr Expr deriving (Eq, Show)

-- alias para direcciones de memoria
type Address = Int

--Alias para valores
type Value = Expr
type Cell = (Address, Value)
type Memory = [Cell]
--[(Adre, Val), (Adre, Val), (Adre, Val),...]

-------------------
--    Memoria    --
-------------------

{-En toda esta sección de la práctica se usará la función auxiliar revMemo la cual verifica si una memoria está corrupta
 (es decir, revMemo verifica si existen dos celdas cuya primera entrada es la misma):-}
revMemo :: Memory -> Memory
revMemo [] = []
revMemo m = if fst (head m) `elem` map fst (tail m) then error "Corrupted Memory" else head m : revMemo (tail m)

--Implementa las sigientes funciones y las definiciones anteriores en un módulo llamado Memory:

--1. newAdress. Dada una nueva de memoria, genera una nueva direccion de memoria que no esté contenida en esta

{-Primero recordemos la función auxiliar minFree utilizada en la Práctica 2, esta función recibe una lista de números naturales
 y regresa el mínimo número natural de la lista que no está en ella, requiere de la función auxiliar minFrom y 
 la lista que reciba no debe tener elementos repetidos pues se cicla.-}
type Nat = Int

minFree :: [Nat] -> Nat
minFree xs = minFrom 0 (length xs,xs)

minFrom :: Nat -> (Int,[Nat]) -> Nat
minFrom a (n,xs)
 | n == 0     = a
 | m == b-a   = minFrom b (n - m, vs)
 | otherwise  = minFrom a (m, us)
 where (us, vs) = partition (< b) xs
       b = a + 1 + div n 2
       m = length us

--Así podemos definir newAdress como:

newAddress :: Memory -> Expr
newAddress [] = L 0
newAddress m = L (minFree (map fst (revMemo m)))

{-Ejemplos:

                                     newAddress [] = L0
                  newAddress [(0,B False),(2,I 9)] = L1
           newAddress [(0,I 21),(1,Void),(2,I 12)] = L3
newAddress [(0,I 21),(1,Void),(2,I 12),(1,B True)] = Error: Corrupted Memory
-}

--2. acces. Dada una dirección de memoria, devuelve el valor contenido en la celda con tal
-- dirección, en caso de no encontrarla debe devolver Nothing.
access :: Address -> Memory -> Maybe Value
access _ [] = Nothing
access i m = if null ([x | x <- revMemo m, fst x == i]) 
                then Nothing 
                    else Just (snd (head [x | x <- revMemo m, fst x == i]))

{-Ejemplos:

                                      access 3 [] = Nothing
                 access 1 [(0,B False ),(2, I 9)] = Nothing
            access 2 [(0,I 21),(2,I 12),(1,Void)] = Just (I 12)
access 2 [(0,I 21),(0,B False),(3,Void),(2,I 12)] = Exception : Corrupted memory.
-}

-- Dada una celda de memoria, actualiza el valor de esta misma en la memoria. En
-- caso de no existir debe devolver Nothing.
update :: Cell -> Memory -> Maybe Memory
update (i,valor) [] = case valor of B False -> Nothing
                                    B True  -> Nothing
                                    I n     -> Nothing
                                    Fn a b  -> Nothing
                                    valor   -> error "Memory can only store values"
update (i,valor) m  = case valor of B False -> Just ([x | x <- revMemo m, i /= fst x] ++ [(i,B False)])
                                    B True  -> Just ([x | x <- revMemo m, i /= fst x] ++ [(i,B True)])
                                    I n     -> Just ([x | x <- revMemo m, i /= fst x] ++ [(i,I n)])
                                    Fn a b  -> Just ([x | x <- revMemo m, i /= fst x] ++ [(i,Fn a b)])      
                                    valor   -> error "Memory can only store values"                           

{-Ejemplos:
                                  update (3,B True) [] = Nothing
        update (0,Succ (V "x")) [(0,B False),(2, I 9)] = Exception : Memory can only store values
update (0,Fn "x" (V "x")) [(0,I 21),(1,Void),(2,I 12)] = [(0,Fn "x" (V "x")),(1,Void),(2,I 12)]
       update (2, I 14) [(0,I 21),(2, Void),(2, I 12)] = Exception : Corrupted memory
       update (2, I 14) [(0,I 13),(1,B True),(2,I 25)] = Just [(0,I 13),(1,B True),(2,I 14)]
-}

--------------------------------     -----------------------
--    Ejecución Secuencial    --  y  --    Ciclo While    --
--------------------------------     -----------------------

{-Se añadieron los constructores: 

                                  | Void
                                  | Seq Expr Expr
                                  | While Expr Expr
al tipo de dato Expr
-}

--------------------------------------------
--    Reimplementación de la semántica    --
--------------------------------------------

-- Lo mismo que en la practica 1 solo que extendida
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


type Substitution = (Identifier, Expr)
-- Lo mismo que en la primer practica pero extendido
subst :: Expr -> Substitution -> Expr
subst (V x) (id, e)
    | x == id = e
    | otherwise = V x
subst (I n) _ = I n
subst (B b) _ = B b
--subst (Fn a b) e
--  | a == y = Fn a e
--  | (a /= y) && notElem (V a) (frVars es) = Fn a (subst e s)
--  | (a /= y) && elem (V a) (frVars es) = Fn (incVar a) (subst e s)
--  | otherwise = Fn a e
-- Me confundió xd
--subst (Fn v e1) (y,e)
--    | elem v (frVars e) && (v == y) = Fn y (subst e1 (y, e))
-- | notElem x (frVars e) && (x /= y) = Fn x (subst e1 (y, e))
--    | otherwise = error "Substitution not in free variables."
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

subst (Let x e1 e2) (y, e) --la idea era la misma para fn xd
    | notElem x (frVars e) && (x == y) = Let y (subst e1 (y, e)) (subst e2 (y, e))
    | notElem x (frVars e) && (x /= y) = Let x (subst e1 (y, e)) (subst e2 (y, e))
    | otherwise = error "No c puede."

subst (L i) s = L i
subst (Alloc a) s = Alloc (subst a s)
subst (Dref a) s = Dref (subst a s)
subst Void s = error "No se puede sustituir algo vacio"
subst (Assig a b) s = Assig (subst a s) (subst b s)
subst (Seq a b) s = Seq (subst a s) (subst b s)
subst (While a b) s = While (subst a s) (subst b s)
subst (App a b) s = App (subst a s) (subst b s)

-- Re implementa esta función para que dada una memoria y una expresión, devuelva
--la reducción a un paso, es decir, eval1 (m, e) = (m’, e’) si y sólo si <m, e> → <m’,e’>
{-data Expr = V Identifier | I Int | B Bool
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
            | App Expr Expr deriving (Eq, Show)
-}
eval1 :: (Memory, Expr) -> (Memory, Expr)
eval1 (m, V x) = (m, V x)
eval1 (m, I n) = (m, I n)
eval1 (m, B b) = (m, B b)
--fn
eval1 (m, Succ (Pred (I n))) = (m, I n)
eval1 (m, Succ (I n)) = (m, I (n+1))
--eval1 (m, Succ a) = (m, Succ (eval1 (m, a)))


-- Extiende esta función para que dada una memoria y una expresión, devuelve la
-- expresión hasta que la reducción quede bloqueada, es decir, evals (m, e) = (m’, e’) si y sólo si <m, e> →
-- <m’, e’> y e’ esta bloqueado.
evals :: (Memory, Expr) -> (Memory, Expr)
evals = error "D:"


--Extiende esta función para que dada una expresión, devuelva la evaluación de un
--programa tal que evale e = e’ syss e →e’ y e’ e un valor. En caso de que e’ no sea un valor deberá mostrar
--un mensaje de error particular del operador que lo causó.
evale :: Expr -> Expr
evale = error "D:"



-----------------------------------
--stack ghci src/Practica3.MiniC.hs
-----------------------------------
