module Practica2.MinHs where

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
            | App Expr Expr


----------------------------------------
--  Algoritmo de inferencia de tipos  --
----------------------------------------

-- Para las reglas de tipados:
type TIdentifier = Int
data Type = T TIdentifier
            | Integer | Boolean
            | Arrow Type Type deriving (Eq)

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

--Ejemplos:
t1 :: Type
t1 = Arrow (T 1) (Arrow (T 2)  (T 1))   --main > tvars ( T1 → ( T2 → T1 ) ) ⇒ [1,2]

t2 :: Type
t2 = Arrow Integer (Arrow Boolean Integer) --main > tvars ( Integer → ( Boolean → Integer )) ⇒ []

{- 2. (1 pt) Implementar la función fresh :: [Type] → Type la cual dado un conjunto de vari-
ables de tipo, obtiene una variable de tipo fresca, es decir, que no aparece en este conjunto.
Esta funcion es importante que se realice utilizando lo discutido durante el labo-
ratorio sobre el problema de MinFree.-}

--aquí me quedé u:

fresh :: [Type] -> Type
fresh = error "D:"





--Ejemplos:
t3 :: [Type]
t3 =  [T 0,T 1,T 2,T 3] --main > fresh [T0 , T1 , T2 , T3] ⇒ T4
t4 :: [Type]
t4 =  [T 0,T 1,T 3,T 4] --main > fresh [T0 , T1 , T3 , T4] ⇒ T2


{- 3. (1 pt) Implementar la función rest :: ( [ Type ] , Expr ) → ( [ Type ] , Ctxt , Type
, Constraint ) la cual dada una expresion, infiere su tipo implementando las reglas descritas
anteriormente. Devolviendo el contexto y el conjunto de restricciones donde es valido. Utiliza
el conjunto de variables de tipo para crear variables de tipo frecas durante la ejecucion.
Ejemplos:
main > rest ( [] , Fn ”x” (V ”x” ) ) ⇒
( [ T0 ] , [ ] , T0 > T0 , [ ] )
main > rest ( [] , Add (V ”x” ) (V ”x” ) ) ⇒
( [ T0 , T1 ] , [ ( ”x” , T0 ) , ( ”x” , T1 ) ] , Integer , [ ( T0 , T1 ) , (T0 ,
Integer ) , (T1 , Integer ) ] )
-}
rest :: ([Type],Expr) -> ([Type],Ctxt,Type,Constraint)
rest = error "D:"


---------- Algoritmo de Unificación -----------

-- Definimos como una lista de duplas la substitucion en tipos.
type Substitution = [(TIdentifier,Type)]


{- 1. (1 pt) Implementar la función subst :: Type → Substitution → Type la cual aplica la
sustitucion a un tipo dado.
Ejemplos:
main > subst (T1 → (T2 → T1)) [(3 , T4) , (5 , T6)] ⇒ T1 → (T2 → T1)
main > subst (T1 → (T2 → T1)) [(1 , T2) , (2 , T3)] ⇒ T2 → (T3 → T2 )
-}
subst :: Type -> Substitution -> Type
subst = error "D:"



{- 2. (1 pt) Implementar la función comp :: Substitution → Substitution → Substitution
la cual realiza la composicion de dos sustituciones.
Ejemplos:
main > comp [(1 , T2 → T3) , (4 , T5)] [( 2 , T6)] ⇒ [(1 , T6 → T3) , (4 , T5), (2 , T6)]
 -}
comp :: Substitution -> Substitution -> Substitution
comp = error "D:"


{- 3. (1 pt) Implementar la función unif :: Constraint → Substitution la cual obtiene el unifi-
cador mas general (μ). Pueden consultar la implementacion realizada durante el laboratorio.
-}
unif :: Constraint -> Substitution
unif = error "D:"


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

