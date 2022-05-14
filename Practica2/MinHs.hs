module Practica2.MinHs where

import Data.Ix
import Data.List

-----------------------------------------------------------
--      Lenguajes de Programación y sus Paradigmas       --  
-----------------------------------------------------------            
--                      Práctica 2                       --
-----------------------------------------------------------
--Integrantes:                                           --
--1. Bernal Márquez Erick                       317042522--
--2. Deloya Andrade Ana Valeria                 317277582-- 
--3. Villegas Barrón César                      314002033--
-----------------------------------------------------------

--------------------------------------
--      Extensión del lenguaje      --
--------------------------------------

-- 1. Crear un nuevo tipo de dato el cual representa la sintaxis abstracta para el lenguaje MinHs:
-- Para las variables
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
            | App Expr Expr deriving (Eq, Show)


----------------------------------------
--  Algoritmo de inferencia de tipos  --
----------------------------------------

-- Para las reglas de tipados:
type TIdentifier = Int

data Type = T TIdentifier
            | Integer | Boolean
            | Arrow Type Type deriving (Show, Eq)

-- Contexto al igual que en al anterior practica, para verificacion de tipos:
type Ctxt = [(Identifier, Type)]

-- Conjunto de restricciones
type Constraint = [(Type, Type)]

{-  1. (1 pt) Implementar la función tvars :: Type → [Identifier] la cual devuelve el conjunto
de variables de tipo.-}

--Primero utilizamos la siguiente función auxiliar para remover elementos duplicados:
myNub :: (Eq a) => [a] -> [a]
myNub (x:xs) = x : myNub (filter (/= x) xs)
myNub [] = []

--Así, definimos tvars como:
tvars :: Type -> [TIdentifier]
tvars Integer = []
tvars Boolean = []
tvars (T i) = [i]
tvars (Arrow t s) = myNub (tvars t ++ tvars s)

--Ejemplo: tvars t1 = [1,2], donde t1 se define como:
t1 :: Type
t1 = Arrow (T 1) (Arrow (T 2)  (T 1))   

--Ejemplo: tvars t2 = [], donde t1 se define como:
t2 :: Type
t2 = Arrow Integer (Arrow Boolean Integer) 

{- 2. (1 pt) Implementar la función fresh :: [Type] → Type la cual dado un conjunto de vari-
ables de tipo, obtiene una variable de tipo fresca, es decir, que no aparece en este conjunto.
Esta funcion es importante que se realice utilizando lo discutido durante el labo-
ratorio sobre el problema de MinFree.-}

--Primero definimos algunas funciones auxiliares:

{-minFree recibe una lista de números naturales y regresa el mínimo número natural de la lista
que no está en ella, requiere de la función auxiliar minFrom-}
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

{-freshAux recibe una lista de tipos Type y regresa la lista cuyos elementos son los enteros asociados
a cada tipo libre de la lista original sin repetición de elementos-}
freshAux :: [Type] -> [Int]
freshAux [] = []
freshAux x = tvars (head x) `union` freshAux (tail x)

--Ejemplo: freshAux l1 = [1,2,3,4,6], donde l1 se defnie como:
l1 :: [Type]
l1 = [T 1, Arrow (T 1) (T 2),T 2, T 3, T 4, Arrow (T 4) (Arrow (T 6)  (T 4)), Arrow Integer Boolean]

--Así podemos definir la función fresh de la siguiente forma:
fresh :: [Type] -> Type
fresh x = T (minFree (freshAux x))

--Ejemplo: fresh l2 = T 7, donde l2 se define como:
l2 :: [Type]
l2 = [T 0, T 1,T 2,T 3,T 5, Arrow (T 4) (Arrow (T 6)  (T 4))]

--Ejemplo: fresh l3 = T 4, donde l3 se define como:
l3 :: [Type]
l3 =  [T 0,T 1,T 2,T 3] 

--Ejemplo: fresh l4 = T 2, donde l4 se define como:
l4 :: [Type]
l4 =  [T 0,T 1,T 3,T 4]

{- 3. (1 pt) Implementar la función rest :: ( [ Type ] , Expr ) → ( [ Type ] , Ctxt , Type
, Constraint ) la cual dada una expresion, infiere su tipo implementando las reglas descritas
anteriormente. Devolviendo el contexto y el conjunto de restricciones donde es valido. Utiliza
el conjunto de variables de tipo para crear variables de tipo frecas durante la ejecucion.-}

rest :: ([Type],Expr) -> ([Type],Ctxt,Type,Constraint)
rest = error "D:"


--Ejemplos:
{-main > rest ( [] , Fn ”x” (V ”x” ) ) ⇒
( [ T0 ] , [ ] , T0 > T0 , [ ] )
main > rest ( [] , Add (V ”x” ) (V ”x” ) ) ⇒
( [ T0 , T1 ] , [ ( ”x” , T0 ) , ( ”x” , T1 ) ] , Integer , [ ( T0 , T1 ) , (T0 ,
Integer ) , (T1 , Integer ) ] )-}


-------------------------------------
--    Algoritmo de Unificación U   --
-------------------------------------

-- Definimos como una lista de duplas la substitucion en tipos.
type Substitution = [(TIdentifier,Type)]


{- 1. (1 pt) Implementar la función subst :: Type → Substitution → Type la cual aplica la
sustitucion a un tipo dado.
Ejemplos:
main > subst (T1 → (T2 → T1)) [(3 , T4) , (5 , T6)] ⇒ T1 → (T2 → T1)
main > subst (T1 → (T2 → T1)) [(1 , T2) , (2 , T3)] ⇒ T2 → (T3 → T2 )
-}
subst :: Type -> Substitution -> Type
--subst = error "D:"
subst (T t) s = case s of 
                [] -> T t
                ((x, y): sub) -> if x == t then y else subst (T t) sub
subst (Arrow t1 t2) s = Arrow (subst t1 s) (subst t2 s)
subst t s = t

{- 2. (1 pt) Implementar la función comp :: Substitution → Substitution → Substitution
la cual realiza la composicion de dos sustituciones.
Ejemplos:
main > comp [(1 , T2 → T3) , (4 , T5)] [( 2 , T6)] ⇒ [(1 , T6 → T3) , (4 , T5), (2 , T6)]
 -}
comp :: Substitution -> Substitution -> Substitution
comp s1 s2 = [(fst t', subst (snd t') s2) | t' <- s1] `union` 
             [(x,t) | (x,t) <- s2,  x `notElem` [y | (y, t) <- s1]] -- no c pk no jala con snd 

{- 3. (1 pt) Implementar la función unif :: Constraint → Substitution la cual obtiene el unifi-
cador mas general (μ). Pueden consultar la implementacion realizada durante el laboratorio.
-}
-- type Substitution = [(TIdentifier,Type)]
-- type Constraint = [(Type, Type)]
unif :: Constraint -> Substitution
unif [] = []
unif c = error "D:" 

------------- Inferencia de tipos -------------
{- 1. (1 pt) Implementar la función infer :: Expr > ( Ctxt , Type ) la cual dada una expre-
sion, infiere su tipo devolviendo el contexto donde es valido.
Ejemplos:
main > infer ( Let ”x” (B True) (And (V ”x” ) ( Let ”x” ( I 1 0 ) (Eq ( I 0 ) ( Succ
(V ”x” )))))) ⇒ ( [ ] , Boolean )
-}
infer :: Expr -> (Ctxt, Type)
infer = error "D:"






-----------------------------------
--stack ghci src/Practica2.Minhs.hs
-----------------------------------

