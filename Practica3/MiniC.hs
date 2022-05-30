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

--Alias para direcciones de memoria
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
 (es decir, revMemo verifica si existen dos celdas con dos primeras entradas iguales).-}
revMemo :: Memory -> Memory
revMemo [] = []
revMemo m = if fst (head m) `elem` map fst (tail m) then error "Corrupted Memory" else head m : revMemo (tail m)

--Implementa las sigientes funciones y las definiciones anteriores en un módulo llamado Memory:

--1. newAdress. Dada una nueva de memoria, genera una nueva direccion de memoria que no esté contenida en esta.

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
newAddress [(0,I 21),(1,Void),(2,I 12),(1,B True)] = Exception: Corrupted Memory
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
access 2 [(0,I 21),(0,B False),(3,Void),(2,I 12)] = Exception: Corrupted memory.
-}

--3. update. Dada una celda de memoria, actualiza el valor de esta misma en la memoria. En
--caso de no existir debe devolver Nothing.
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
        update (0,Succ (V "x")) [(0,B False),(2, I 9)] = Exception: Memory can only store values
update (0,Fn "x" (V "x")) [(0,I 21),(1,Void),(2,I 12)] = [(0,Fn "x" (V "x")),(1,Void),(2,I 12)]
       update (2, I 14) [(0,I 21),(2, Void),(2, I 12)] = Exception: Corrupted memory
       update (2, I 14) [(0,I 13),(1,B True),(2,I 25)] = Just [(0,I 13),(1,B True),(2,I 14)]
-}

--------------------------------     -----------------------
--    Ejecución Secuencial    --  y  --    Ciclo While    --
--------------------------------     -----------------------

{-Se añadieron los constructores: 

                                  | Void
                                  | Seq Expr Expr
                                  | While Expr Expr
al tipo de dato Expr.
-}

--------------------------------------------
--    Reimplementación de la semántica    --
--------------------------------------------

--1. frVars. Extiende esta función para las nuevas expresiones. 
--Lo mismo que en la practica 1 solo que extendida.

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

{-Ejemplos:
              frVars (Add (V "x") (I 5)) = ["x"]
frVars (Assig (L 2) (Add (I 0) (V "z"))) = ["z"]
-}

--2. subst. Extiende esta función para las nuevas expresiones.
-- Lo mismo que en la primer practica pero extendido

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

{-Ejemplos:
                   subst (Add (V "x") (I 5)) ("x",I 10) = Add (I 10) (I 5)
  subst (Let "x" (I 1) (V "x")) ("y",Add (V "x") (I 5)) = Let "x1" (I 1) (V "x1") -- se busca alfa equivalencias
  subst (Assig (L 2) (Add (I 0) (V "z"))) ("z",B False) = (Assig (L 2) (Add (I 0) (B False)))
-}

--3. eval1. Re implementa esta función para que dada una memoria y una expresión, devuelva la reducción a un paso,
--es decir, eval1 (m, e) = (m’, e’) si y sólo si <m, e> → <m’,e’>

--Primero consideremos la función auxiliar loC la cual solamente recibe un lugar de memoria y regresa el entero 
--perteneciente a dicho lugar (se usará para la definicón de 'eval1' para expresiones tipo Alloc):
loC :: Expr -> Address
loC (L i) = i
loC e = error "loC está definida únicamente para lugares de memeoria"

{-Vemos que implementar la función eval1 :: (Memory, Expr) -> (Memory, Expr) es similar a lo que se hizo en la primera práctica solo 
 que esta vez se debe tomar en cuenta la memoria y las nuevas expresiones. Teniendo en cuenta las definiciones de la sección 5.1 de las
 Notas de Clase 9 y la sección 1.2 de las Notas de Clase 6 podemos definir eval1 como:-}
eval1 :: (Memory, Expr) -> (Memory, Expr)
-- V String
eval1 (m,V x) = error "No se pueden evaluar expresiones con variables libres"
-- I Int
eval1 (m,I n) = (m,I n)
-- B Bool
eval1 (m,B b) = (m,B b)
-- Fn Identifier Expr
eval1 (m,Fn x e) = (m,Fn x e) --Término bloqueado (las funciones son valores)
-- Succ Expr
eval1 (m,Succ (I n)) = (m,I (n+1))
eval1 (m,Succ (B b)) = (m,Succ (B b)) --Término bloqueado
eval1 (m,Succ e) = (fst (eval1 (m,e)), Succ (snd (eval1 (m,e))))
-- Pred Expr
eval1 (m,Pred (I n)) = (m,I (n-1))
eval1 (m,Pred (B b)) = (m,Pred (B b)) --Término bloqueado
eval1 (m,Pred e) = (fst (eval1 (m,e)),Pred (snd (eval1 (m,e))))
-- Add Expr Expr
eval1 (l,Add (I n) (I m)) = (l,I (n+m))
eval1 (m,Add (B b) (I n)) = (m,Add (B b) (I n)) --Término bloqueado
eval1 (m,Add (I n) (B b)) = (m,Add (I n) (B b)) --Término bloqueado
eval1 (m,Add (B b) (B c)) = (m,Add (B b) (B c)) --Término bloqueado
eval1 (m,Add (I n) e2) = (fst (eval1 (m,e2)),Add (I n) (snd (eval1 (m,e2))))
eval1 (m,Add (B b) e2) = (fst (eval1 (m,e2)),Add (B b) (snd (eval1 (m,e2)))) --Término que será bloqueado
eval1 (m,Add e1 e2) = (fst (eval1 (m,e1)),Add (snd (eval1 (m,e1))) e2)
-- Mul Expr Expr
eval1 (l,Mul (I n) (I m)) = (l,I (n*m))
eval1 (m,Mul (B b) (I n)) = (m,Mul (B b) (I n)) --Término bloqueado
eval1 (m,Mul (I n) (B b)) = (m,Mul (I n) (B b)) --Término bloqueado
eval1 (m,Mul (B b) (B c)) = (m,Mul (B b) (B c)) --Término bloqueado
eval1 (m,Mul (I n) e2) = (fst (eval1 (m,e2)),Mul (I n) (snd (eval1 (m,e2))))
eval1 (m,Mul (B b) e2) = (fst (eval1 (m,e2)),Mul (B b) (snd (eval1 (m,e2)))) --Término que será bloqueado
eval1 (m,Mul e1 e2) = (fst (eval1 (m,e2)),Mul (snd (eval1 (m,e1))) e2)
-- Not Expr
eval1 (m,Not (B False)) = (m,B True)
eval1 (m,Not (B True)) = (m,B False)
eval1 (m,Not (I n)) = (m,Not (I n)) --Término bloqueado
eval1 (m,Not e) = (fst (eval1 (m,e)),Not (snd (eval1 (m,e))))
-- Iszero Expr
eval1 (m,Iszero (I 0)) = (m,B True)
eval1 (m,Iszero (I n)) = (m,B False)
eval1 (m,Iszero (B b)) = (m,Iszero (B b)) --Término bloqueado
eval1 (m,Iszero e) = (fst (eval1 (m,e)),Iszero (snd (eval1 (m,e))))
-- And Expr Expr
eval1 (m,And (B True) (B True)) = (m,B True)
eval1 (m,And (B False) (B b)) = (m,B False)
eval1 (m,And (B b) (B False)) = (m,B False)
eval1 (m,And (B b) (I n)) = (m,And (B b) (I n)) --Término bloqueado
eval1 (m,And (B b) e2) = (fst (eval1 (m,e2)),And (B b) (snd (eval1 (m,e2))))
eval1 (m,And (I n) (B b)) = (m,And (I n) (B b)) --Término bloqueado
eval1 (l,And (I n) (I m)) = (l,And (I n) (I m)) --Término bloqueado
eval1 (m,And (I n) e2) = (fst (eval1 (m,e2)),And (I n) (snd (eval1 (m,e2))))  --Término que será bloqueado
eval1 (m,And e1 e2) = (fst (eval1 (m,e1)),And (snd (eval1 (m,e1))) e2)
-- Or Expr Expr 
eval1 (m,Or (B True) (B b)) = (m,B True)
eval1 (m,Or (B b) (B True)) = (m,B True)
eval1 (m,Or (B False) (B False)) = (m,B False)
eval1 (m,Or (B b) (I n)) = (m,Or (B b) (I n)) --Término bloqueado
eval1 (m,Or (B b) e2) = (fst (eval1 (m,e2)),Or (B b) (snd (eval1 (m,e2))))
eval1 (m,Or (I n) (B b)) = (m,Or (I n) (B b)) --Término bloqueado
eval1 (l,Or (I n) (I m)) = (l,Or (I n) (I m)) --Término bloqueado
eval1 (m,Or (I n) e2) = (fst (eval1 (m,e2)),Or (I n) (snd (eval1 (m,e2)))) --Término que será bloqueado
eval1 (m,Or e1 e2) = (fst (eval1 (m,e1)),Or (snd (eval1 (m,e1))) e2)
-- Gt Expr Expr
eval1 (l,Gt (I n) (I m)) =  (l,if n - m > 0 then B True else B False)
eval1 (m,Gt (I n) (B b)) = (m,Gt (I n) (B b)) --Término bloqueado
eval1 (m,Gt (B b) (I n)) = (m,Gt (B b) (I n)) --Término bloqueado
eval1 (m,Gt (B b) e2 ) = (fst (eval1 (m,e2)),Gt (B b) (snd (eval1 (m,e2)))) --Término que será bloqueado
eval1 (m,Gt (I n) e2 ) = (fst (eval1 (m,e2)),Gt (I n) (snd (eval1 (m,e2))))
eval1 (m,Gt e1 e2 ) = (fst (eval1 (m,e1)),Gt (snd (eval1 (m,e1))) e2)
-- Lt Expr Expr 
eval1 (l,Lt (I n) (I m)) =  (l,if n - m < 0 then B True else B False)
eval1 (m,Lt (I n) (B b)) = (m,Lt (I n) (B b)) --Término bloqueado
eval1 (m,Lt (B b) (I n)) = (m,Lt (B b) (I n)) --Término bloqueado
eval1 (m,Lt (B b) e2) = (fst (eval1 (m,e2)),Lt (B b) (snd (eval1 (m,e2)))) --Término que será bloqueado
eval1 (m,Lt (I n) e2) = (fst (eval1 (m,e2)),Lt (I n) (snd (eval1 (m,e2))))
eval1 (m,Lt e1 e2) = (fst (eval1 (m,e1)),Lt (snd (eval1 (m,e1))) e2)
-- Eq Expr Expr 
eval1 (l,Eq (I n) (I m)) =  (l,if n - m == 0 then B True else B False)
eval1 (m,Eq (I n) (B b)) = (m,Eq (I n) (B b)) --Término bloqueado
eval1 (m,Eq (B b) (I n)) = (m,Eq (B b) (I n)) --Término bloqueado
eval1 (m,Eq (B b) e2) = (fst (eval1 (m,e2)),Eq (B b) (snd (eval1 (m,e2)))) --Término que será bloqueado
eval1 (m,Eq (I n) e2) = (fst (eval1 (m,e2)),Eq (I n) (snd (eval1 (m,e2))))
eval1 (m,Eq e1 e2) = (fst (eval1 (m,e1)),Eq (snd (eval1 (m,e1))) e2)
-- If Expr Expr Expr
eval1 (m,If (B True) e1 e2) = (m,e1)
eval1 (m,If (B False) e1 e2) = (m,e2)
eval1 (m,If (I n) e1 e2) = (m,If (I n) e1 e2) --Término bloqueado
eval1 (m,If e e1 e2) = (fst (eval1 (m,e)),If (snd (eval1 (m,e))) e1 e2)
-- Let String Expr Expr
eval1 (m,Let x (B b) e) = (m,subst e (x, B b))
eval1 (m,Let x (I n) e) = (m,subst e (x, I n))
eval1 (m,Let x (Fn y e) e1) = (m,subst e1 (x, Fn y e))
eval1 (m,Let x e1  e2) = (fst (eval1 (m,e1)),Let x (snd (eval1 (m,e1))) e2)
-- L Int
eval1 (m, L i) = (m,L i)
-- Alloc Expr
-- Una expresión de la forma ref v (Alloc v) donde v es valor, devuelve como valor la dirección simbólica de la celda que alojará a v, la cual se agrega a la memoria en uso:
eval1 (m,Alloc (I n))    = (m ++ [(loC (newAddress m), I n)], newAddress m)
eval1 (m,Alloc (B b))    = (m ++ [(loC (newAddress m), B b)], newAddress m)
eval1 (m,Alloc (Fn x e)) = (m ++ [(loC (newAddress m), Fn x e)], newAddress m)
eval1 (m,Alloc e)      = (fst (eval1 (m,e)), Alloc (snd (eval1 (m,e)))) --Para evaluar una expresión de la forma ref v (Alloc v) primero hay que reducir e hasta que sea un valor.
-- Dref Expr
-- Una recuperación ! (Dref L n) se evalua al valor almacenado en la celda con dirección de memoria "L n" el cual está dado por μ(L n).
eval1 (m, Dref (L n))    = (m, fromJust (access n m))
eval1 (m, Dref (I n))    = (m , I n) --Dred (!) solo se aplica a lugares de celda, por lo que Dref de un valor o es el mismo valor o es un error (por ejemplo !2 = 2 o !2 = error "el operador recuperación solo admite lugares de celda", preguntaré por telegram)
eval1 (m, Dref (B b))    = (m , B b)
eval1 (m, Dref (Fn x e)) = (m , Fn x e)
eval1 (m, Dref e)        = (fst (eval1 (m,e)), Dref (snd (eval1 (m,e))))
-- Assig Expr Expr
eval1 (m, Assig (L n) (L i))     = error "Se le dará un lugar de memoria a un lugar de memoria, algo anda mal D:"
eval1 (m, Assig (L n) (I i))     = (fromJust (update (n,I i) m),Void)   ----v----
eval1 (m, Assig (L n) (B True))  = (fromJust (update (n,B True) m),Void) ---v---
eval1 (m, Assig (L n) (B False)) = (fromJust (update (n,B False) m),Void) --v--
eval1 (m, Assig (L n) (Fn x e))  = (fromJust (update (n,Fn x e) m),Void) {-Una asignación (L n) := v (v es valor) causa un efecto en la memoria y devuelve un valor irrelevante () (Void). 
                                                                                               El efecto consiste en eliminar el valor almacenado en la celda cuya dirección es (L n),
                                                                                               guardando en su lugar el valor dado v.-}
eval1 (m, Assig (L n) e2)        = (fst (eval1 (m,e2)), Assig (L n) (snd (eval1 (m,e2)))) --Para evaluar una asignación (L n) := e2 primero es necesario reducir e2
eval1 (m, Assig e1 e2) = (fst (eval1 (m,e1)), Assig (snd (eval1 (m,e1))) e2) --Para evaluar una asignación e1 := e2 primero es necesario reducir e1.
-- Void
eval1 (m,Void) = (m,Void)
-- Seq Expr Expr
eval1 (m,Seq Void e2) = (m, e2)
eval1 (m,Seq e1 e2) = (fst (eval1 (m,e1)), Seq (snd (eval1 (m,e1))) e2)
--While Expr Expr
eval1 (m,While e1 e2) = (m,If e1 (Seq e2 (While e1 e2)) Void)
--App Expr Expr 
eval1 (m,App (Fn x e) (I i)) = (m, subst (Fn x e) (x, I i))
eval1 (m,App (Fn x e) (B True)) = (m, subst (Fn x e) (x, B True))
eval1 (m,App (Fn x e) (B False)) = (m, subst (Fn x e) (x, B False))
eval1 (m,App (Fn x e) (Fn y g))  = (m, subst (Fn x e) (x, Fn y g))
eval1 (m,App (I i) e2)     = (fst (eval1 (m,e2)), App (I i) (snd (eval1 (m,e2))))
eval1 (m,App (B True) e2)  = (fst (eval1 (m,e2)), App (B True) (snd (eval1 (m,e2))))
eval1 (m,App (B False) e2) = (fst (eval1 (m,e2)), App (B False) (snd (eval1 (m,e2))))
eval1 (m,App (Fn x e) e2)  = (fst (eval1 (m,e2)), App (Fn x e) (snd (eval1 (m,e2))))
eval1 (m,App e1 e2)        = (fst (eval1 (m,e1)), App (snd (eval1 (m,e1))) e2) --Las reglas para evaluar una expresión App se encuentran en las Notas de Clase 6 p.2
{-Ejemplos:

                   eval1 ([(0,B False)],(Add (I 1) (I 2))) = ([(0,B False)],I 3)
eval1 ([(0,B False)], (Let "x" (I 1) (Add (V "x") (I 2)))) = ([(0, B False)], Add (I 1) (I 2))
             eval1 ([(0 , B False)], Assig (L 0) (B True)) = ([(0 , B True)] , Void)
              eval1 ([], While (B True) (Add (I 1) (I 1))) = ([], If (B True) (Seq (Add (I 1) (I 1)) (While (B True) (Add (I 1) (I 1)))) Void)
-}

--4. evals. Extiende esta función para que dada una memoria y una expresión, devuelve la
-- expresión hasta que la reducción quede bloqueada, es decir, evals (m, e) = (m’, e’) si y sólo si <m, e> →
-- <m’, e’> y e’ esta bloqueado.
evals :: (Memory, Expr) -> (Memory, Expr)
-- Valores
evals (m,V x)  = eval1 (m,V x)
evals (m,I n)    = eval1 (m,I n)
evals (m,B b)    = eval1 (m,B b)
evals (m,Fn x e) = evals (m,Fn x e)
-- Operadore unarios
evals (m,Succ e)   = eval1 (fst (evals (m,e)), Succ (snd (evals (m,e))))
evals (m, Pred e)  = eval1 (fst (evals (m,e)), Pred (snd (evals (m,e))))
evals (m,Not e)    = eval1 (fst (evals (m,e)), Not (snd (evals (m,e))))
evals (m,Iszero e) = eval1 (fst (evals (m,e)), Iszero (snd (evals (m,e))))
-- Operadore binarios
evals (m,Add e1 e2) = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Add (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
evals (m,Mul e1 e2) = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Mul (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
evals (m,And e1 e2) = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), And (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
evals (m,Or e1 e2)  = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Or  (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
evals (m,Gt e1 e2)  = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Gt  (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
evals (m,Lt e1 e2)  = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Lt  (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
evals (m,Eq e1 e2)  = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Eq  (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
-- If Expr Expr Expr
evals (m,If e e1 e2) = eval1 (fst (evals (m,e)) `union` fst (evals (fst (evals (m,e)),e1)) `union` fst (evals (fst (evals (fst (evals (m,e)),e1)),e2)),
                                   If (snd (evals (m,e))) (snd (evals (fst (evals (m,e)),e1))) (snd (evals (fst (evals (fst (evals (m,e)),e1)),e2))))
-- Let String Expr Expr
evals (m,Let x (I i) e2) = evals (eval1 (m,Let x (I i) e2))
evals (m,Let x (B b) e2) = evals (eval1 (m,Let x (B b) e2))
evals (m,Let x (Fn y e) e2) = evals (eval1 (m,Let x (Fn y e) e2))
evals (m,Let x e1 e2) = evals (fst (evals (m,e1)), Let x (snd (evals (m,e1))) e2)
-- L Int
evals (m,L i) = eval1 (m,L i)
-- Alloc Expr
evals (m, Alloc e) = eval1 (fst (evals (m,e)), Alloc (snd (evals (m,e))))
-- Dref Expr
-- Una recuperación ! (Dref L n) se evalua al valor almacenado en la celda con dirección de memoria "L n" el cual está dado por μ(L n).
evals (m, Dref e) = eval1 (fst (evals (m,e)), Dref (snd (evals (m,e))))
-- Assig Expr Expr
evals (m, Assig e1 e2) = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)), Assig (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))
-- Void
evals (m,Void) = eval1 (m,Void)
-- Seq Expr Expr
evals (m, Seq e1 e2) = eval1 (fst (evals (m,e1)), Seq (snd (evals (m,e1))) e2)
--While Expr Expr
evals (m, While e1 e2) = (m,If e1 (Seq e2 (While e1 e2)) Void)
--App Expr Expr 
evals (m, App e1 e2) = eval1 (fst (evals (m,e1)) `union` fst (evals (fst (evals (m,e1)),e2)),App (snd (evals (m,e1))) (snd (evals (fst (evals (m,e1)),e2))))

{- Ejemplos:
evals ([],(Let "x" (Add (I 1) (I 2)) (Eq (V "x") (I 0)))) = ([],B False)
              evals ([],(Add (Mul (I 2) (I 6)) (B True))) = ([],Add (I 12) (B True))
    evals ([], Assig (Alloc (B False)) (Add (I 1) (I 9))) = ([(0,I 10)],Void)
-}

--5. evale. Extiende esta función para que dada una expresión, devuelva la evaluación de un
--programa tal que evale e = e’ syss e → e’ y e’ e un valor. En caso de que e’ no sea un valor deberá mostrar
--un mensaje de error particular del operador que lo causó.
evale :: Expr -> Expr
evale (V x) = V x
evale (I n) = I n
evale (B b) = B b
evale (Fn _ _)= error "No hay aplicaciones"
--evale (Fn e1 e1) = evals ?
evale (Succ (B b)) = error "Succ espera un numero"
--evale (Succ (I i)) = evals ?
evale (Pred (B b)) = error "Pred espera un numero"


evale (Add (B b) _) = error "Add espera dos numeros"
evale (Add _ (B b)) = error "Add espera dos numeros"
--evale (Add (I i) (I i2)) = evals (m, Add (I i) (I i2))?

evale (Mul (B b) _) = error "Mul espera dos numeros"
evale (Mul _ (B b)) = error "Mul espera dos numeros"
-- evale ?

evale (Not (I i)) = error "Not espera un booleano"

evale (Iszero (B b)) = error "isZero espera un numero"

evale (And (I i) _) = error "And espera dos booleanos"
evale (And _ (I i)) = error "And espera dos booleanos"

evale (Or (I i) _) = error "Or espera dos booleanos"
evale (Or _ (I i)) = error "Or espera dos booleanos"

evale (Lt (B b) _) = error "Lt espera dos numeros"
evale (Lt _ (B b)) = error "Lt espera dos numeros"

evale (Gt (B b) _) = error "Gt espera dos numeros"
evale (Gt _ (B b)) = error "Gt espera dos numeros"

evale (Eq (B b) _) = error "Gt espera dos numeros"
evale (Eq _ (B b)) = error "Gt espera dos numeros"

evale (If (I i) _ _) = error "If espera un booleano en el primer argumento"

evale (App e _) = error "App espera una funcion en el primer argumento"

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


-----------------------------------
--stack ghci src/Practica3.MiniC.hs
-----------------------------------
