{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
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

{-  1. (1 pt) Implementar la función tvars :: Type → [TIdentifier] la cual devuelve el conjunto
de variables de tipo.-}

--Primero utilizamos la siguiente función auxiliar para remover elementos duplicados:
noDup :: (Eq a) => [a] -> [a]
noDup (x:xs) = x : noDup (filter (/= x) xs)
noDup [] = []

--Así, definimos tvars como:
tvars :: Type -> [TIdentifier]
tvars Integer = []
tvars Boolean = []
tvars (T i) = [i]
tvars (Arrow t s) = noDup (tvars t ++ tvars s)

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
fresh [] = T 0
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

{- 3. (1 pt) Implementar la función rest :: ( [ Type ] , Expr ) → ( [ Type ] , Ctxt , Type, Constraint ) 
la cual dada una expresion, infiere su tipo implementando las reglas descritas anteriormente. 
Devolviendo el contexto y el conjunto de restricciones donde es valido. Utiliza el conjunto de variables
 de tipo para crear variables de tipo frecas durante la ejecucion.-}

{-Primero definimos las funciónes auxiliares que proyectan los diferentes valores del vector
de cuatro entradas que toma el codominio de la función rest:-}
p1 :: ([Type],Ctxt,Type,Constraint) -> [Type]
p1 (a,b,c,d) = a 

p2 :: ([Type],Ctxt,Type,Constraint) -> Ctxt
p2 (a,b,c,d) = b 

p3 :: ([Type],Ctxt,Type,Constraint) -> Type
p3 (a,b,c,d) = c 

p4 :: ([Type],Ctxt,Type,Constraint) -> Constraint
p4 (a,b,c,d) = d

{-También definimos la función auxiliar restrS que modela el comportamiento del conjunto S definido en las reglas  de tipado 
para operadores  binarios, terciaros, así como para  experiones let y aplicaciones. Es decir, restrS recibe dos contextos y si
una variable aparece en ambos contextos entonces la función añade la restricción correspondiente de tipos-} 

restrS :: Ctxt -> Ctxt -> Constraint
restrS c1 c2 = [(s1,s2) | (a,s1) <- c1, (b,s2) <- c2, a == b] 

--Ejemplo: restrS r1 r2 = [(T 0,Arrow (T 3) (T 4))], y restrS r1 r3 = [] donde r1, r2 y r3 se definen como:
r1 :: Ctxt
r1 = [("x",T 0),("y", T 1)] 
r2 :: Ctxt
r2 = [("x",Arrow (T 3) (T 4)),("w", T 2)]
r3 :: Ctxt
r3 = [("z",T 10),("w", T 22)]

--Finalmente definmos la lista de restricciones redundantes:
redundantes :: Constraint
redundantes = [(Integer,Integer),(Boolean,Boolean)]

{-Teniendo en cuenta las funciones auxiliares p1, p2, p3, p4 y restrS podemos definir 
la función rest de la siguiente forma:-}
rest :: ([Type],Expr) -> ([Type],Ctxt,Type,Constraint)
--Tipado de variables
rest (l, V x) = (l ++ [fresh l],[(x,fresh l)],fresh l,[])
-- Tipado de constantes
rest (l, I n) = (l, [],Integer,[])
rest (l, B b) = (l, [],Boolean,[])
--Tipado de funciones
rest (l, Fn x e) = (l `union` p1 (rest (l, V x)) `union` p1 (rest (l,e)), --variables usadas
                   p2 (rest (l,e)) \\ [(x, p3 (rest (l, V x)))], --contexto de e
                   Arrow (p3 (rest (l, V x))) (p3 (rest (l,e))), --el tipo de Fn x e, es de la forma S -> T, donde T es el tipo de e y S es el tipo de la variable x
                   p4 (rest (l,e)) \\ redundantes) --restricciones de e
--Tipado de operadores unarios
--Función sucesor                   
rest (l, Succ e) = (l `union` p1 (rest (l,e)), --variables usadas
                   p2 (rest (l,e)), --contexto de e
                   Integer, --el tipo de Succ e es un entero
                   (p4 (rest (l,e)) `union` [(p3 (rest (l,e)),Integer)]) \\ redundantes) --restricciones de e más la petición de que el tipo de e sea entero
--Función predecesor
rest (l, Pred e) = (l  `union` p1 (rest (l,e)), --variables usadas
                   p2 (rest (l,e)), --contexto de e
                   Integer, --el tipo de Pred e es un entero
                   (p4 (rest (l,e)) `union` [(p3 (rest (l,e)),Integer)]) \\ redundantes) --restricciones de e más la petición de que el tipo de e sea entero
--Negación lógica                   
rest (l, Not e) = (l  `union` p1 (rest (l,e)), --variables usadas
                   p2 (rest (l,e)), --contexto de e
                   Boolean,--el tipo de Not e es un booleano
                   (p4 (rest (l,e)) `union` [(p3 (rest (l,e)),Boolean)]) \\ redundantes)  --restricciones de e más la petición de que el tipo de e sea booleano
--Verificador de igaualdad a cero                   
rest (l, Iszero e) = (l  `union` p1 (rest (l,e)), --variables usadas
                   p2 (rest (l,e)),  --contexto de e
                   Boolean, --el tipo de Iszero e es un booleano
                   (p4 (rest (l,e)) `union` [(p3 (rest (l,e)),Integer)]) \\ redundantes)  --restricciones de e más la petición de que el tipo de e sea booleano                
--Tipado de operadores binarios y terciarios:
--Suma
rest (l, Add e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        Integer, 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Integer),(p3 (rest (l++p1 (rest (l,e1)),e2)),Integer)]) \\ redundantes) --los tipos de e1 y e2 deben ser enteros
--Producto
rest (l, Mul e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        Integer, 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Integer),(p3 (rest (l++p1 (rest (l,e1)),e2)),Integer)]) \\ redundantes) --los tipos de e1 y e2 deben ser enteros
--Conjunción
rest (l, Or e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)),
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)),
                        Boolean,
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Boolean),(p3 (rest (l++p1 (rest (l,e1)),e2)),Boolean)]) \\ redundantes) --los tipos de e1 y e2 deben ser booleanos
--Disyunción
rest (l, And e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        Boolean, 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Boolean),(p3 (rest (l++p1 (rest (l,e1)),e2)),Boolean)]) \\ redundantes) --los tipos de e1 y e2 deben ser booleanos
--Menor que
rest (l, Lt e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        Boolean, 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Integer),(p3 (rest (l++p1 (rest (l,e1)),e2)),Integer)]) \\ redundantes) --los tipos de e1 y e2 deben ser enteros
--Mayor que
rest (l, Gt e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        Boolean, 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Integer),(p3 (rest (l++p1 (rest (l,e1)),e2)),Integer)]) \\ redundantes) --los tipos de e1 y e2 deben ser enteros
--Igualdad numérica
rest (l, Eq e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        Boolean, 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Integer),(p3 (rest (l++p1 (rest (l,e1)),e2)),Integer)]) \\ redundantes) --los tipos de e1 y e2 deben ser enteros
--Condicional If   
rest (l, If e e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        p3 (rest (l,e1)), 
                        ([(p3 (rest (l,e)),Boolean)] --restricciones del tipado de e
                        `union` p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l++p1 (rest (l,e1)),e2)),p3 (rest (l,e1)))]) \\ redundantes ) --los tipos de e1 y e2 deben ser iguales
--Tipado de aplicaciones
rest (l, App e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)), 
                        p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2)), 
                        fresh (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2))), 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2))  --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),Arrow (p3 (rest (l ++ p1 (rest (l,e1)),e2))) (fresh (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)))))]
                            ) \\ redundantes ) {-el tipo de la expresión e1 debe ser igual al tipo Arrow t2 Z, donde t2 es el 
                                                                             tipo de la expresión e2 y Z es la variable fresca a la que pertenece la aplicación-}
--Tipado de expresión Let
rest (l, Let x e1 e2) = (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)) `union` [fresh (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2)))], 
                        (p2 (rest (l,e1)) ++ p2 (rest (l++p1 (rest (l,e1)),e2))) \\ p2 (rest (l++p1 (rest (l,e1)),V x)),
                        p3 (rest (l++p1 (rest (l,e1)),e2)), 
                        (p4 (rest (l,e1)) --restricciones del tipado de e1
                        `union` p4 (rest (l++p1 (rest (l,e1)),e2)) --restricciones del tipado de e2
                        `union` restrS (p2 (rest (l,e1))) (p2 (rest (l++p1 (rest (l,e1)),e2))) --restricciones del conjunto S definido en el pdf de la práctica
                        `union` [(p3 (rest (l,e1)),fresh (l `union` p1 (rest (l,e1)) `union` p1 (rest (l++p1 (rest (l,e1)),e2))))]
                        )\\ redundantes) {-el tipo de la expresión 
                        e1 debe ser igual al tipo de la variable xArrow t2 Z, donde t2 es el tipo de la expresión e2 y Z es la variable fresca a la que pertenece la aplicación-}

                        
--Ejemplo: rest ([], exp1) = ([T 0],[],Arrow T0 T0,[]), donde exp1 se define como:
exp1 :: Expr
exp1 = Fn "x" (V "x" )
--Ejemplo: rest ([], exp2) = ([T 0,T 1],[("x",T 0),("x",T 1)],Integer,[(T 0,T 1),(T 0,Integer),(T 1,Integer)]), donde exp2 se define como:
exp2 :: Expr
exp2 = Add (V "x") (V "x")
--Ejemplo: rest ([T 0, T 1, T 2], exp1) = ([T 0,T 1,T 2,T 3],[("x",T 3)],Arrow (T 3) (T 3),[]) 
--Ejemplo: rest ([],e0) = ([T 0,T 1,T 2,T 3],[],Boolean,[(T 1,Integer),(Integer,T 2),(T 0,Boolean),(Boolean,T 3)]), donde e0 se define como:
e0 :: Expr
e0 = Let "x" e1 e2
e1 :: Expr
e1 = B True
e2 :: Expr
e2 = And (V "x") ( Let "y" (I 10) (Eq ( I 0 ) ( Succ (V "y" )))) --por que p4 (rest ([],e2)) es igual a [T 0, Integer, T 0, Boolean ] ?

-------------------------------------
--    Algoritmo de Unificación U   --
-------------------------------------

-- Definimos como una lista de duplas la substitucion en tipos.
type Substitution = [(TIdentifier,Type)]


{- 1. (1 pt) Implementar la función subst :: Type → Substitution → Type la cual aplica la
sustitucion a un tipo dado.
-}
subst :: Type -> Substitution -> Type
subst (T t) [] = T t
subst (T t) ((ti,T t'):xs) = if t == ti then T t' else subst (T t) xs
subst (Arrow t1 t2) s = Arrow (subst t1 s) (subst t2 s)
subst t s = t
--Ejemplo: subst t3 [(3 , T 4) , (5 , T 6)] = Arrow (T 1) (Arrow (T 2) (T 1)), donde t3 se define como:
t3 :: Type
t3 = Arrow (T 1) (Arrow (T 2) (T 1))
--Ejemplo: subst t4 [(1 , T 2) , (2 , T 3)] = Arrow (T 2) (Arrow (T 3) (T 2)), donde t4 se define como:
t4 :: Type
t4 = Arrow (T 1) (Arrow (T 2) (T 1))


{- 2. (1 pt) Implementar la función comp :: Substitution → Substitution → Substitution
la cual realiza la composicion de dos sustituciones.-}

comp :: Substitution -> Substitution -> Substitution
comp s1 s2 = [(fst t', subst (snd t') s2) | t' <- s1] `union`
             [(x,t) | (x,t) <- s2,  x `notElem` [y | (y, t) <- s1]] -- no c pk no jala con snd 

--Ejemplo: comp t5 t6 = [(1 , Arrow (T 6)  (T 3)) , (4 , T 5), (2 , T 6)], donde t5 y t6 se definen como:
t5 :: Substitution 
t5 = [(1 , Arrow (T 2)  (T 3)), (4 ,T 5)]
t6 :: Substitution 
t6 = [( 2 , T 6)]
--Ejemplo: comp t7 t8 = [(1,Arrow (T 6) (T 3)),(4,T 5),(2,T 6)], donde t7 y t8 se definen como:
t7 :: Substitution 
t7 = [(1, Arrow (T 2) (T 3)), (4, T 5)]
t8 :: Substitution 
t8 = [(2,T 6)]

{- 3. (1 pt) Implementar la función unif :: Constraint → Substitution la cual obtiene el unifi-
cador mas general (μ). Pueden consultar la implementacion realizada durante el laboratorio.
-}
unif :: Constraint -> Substitution
unif c = u where [u] = unifaux c

unifaux :: Constraint -> [Substitution]
unifaux [] = [[]]
unifaux (t: ts) = [comp s1 s2 |
                          s1 <- unifaux' (fst t) (snd t),
                          s2 <- unifaux [(subst (fst t) s1, subst (snd t) s1) | t <- ts]]

unifaux' :: Type -> Type -> [Substitution]
unifaux' (T x) (T y)
 | x == y = [[]]
 | otherwise = [[(x, T y)]]

unifaux' (T x) t 
 | x `elem` tvars t = error "No se puede ):, no son disjuntos"
 | otherwise = return [(x, t)]

unifaux' t (T x)
 | x `elem` tvars t = error "No se puede ):, no son disjuntos"
 | otherwise = return [(x, t)]
                   
unifaux' (Arrow t1 t2) (Arrow t3 t4) = [comp s1 s2 | -- analogo al anterior
                                       s1 <- unifaux' t1 t3, 
                                       s2 <- unifaux' (subst t2 s1) (subst t4 s1)]

unifaux' t s 
 | t == s = [[]] 
 | otherwise = error "No se puede hacer la unificación :("

------------------------------------------
--         Inferencia de tipos          --
------------------------------------------

{- 1. (1 pt) Implementar la función infer :: Expr > ( Ctxt , Type ) la cual dada una expre-
sion, infiere su tipo devolviendo el contexto donde es valido.-}

infer' :: ([Type], Expr) -> ([Type], Ctxt, [Type], Constraint)
infer' (ts, V x) = 
       let fs = fresh ts
           nv' =  ts `union` [fs]
           in (nv',[(x,fs)], [fs], [])

{-infer' (v, I i) = 
       let n = fresh v
           tl = v `union` [n]
           in (tl, [(i,n)], n, []) -- i debe ser string
infer' (v, B b) = 
       let n = fresh v
           tl = v `union` [n]
           in (tl, [(b,n)], n, [])-} -- b debe ser string
                        --ts, c, t, c
infer' (v, Succ e) = let (v, g, t, r) = infer' (v, e)
                         z = fresh v
                         nv' = t `union` [z]
                              in
                                (nv', g, [z], r)


infer :: Expr -> (Ctxt, Type)
infer = error "D:"

------------------------------------------------------------------------------------------------------------------
infer2 :: Expr -> (Ctxt, Type) {-  <-- al parecer esta sí jala :) -}
infer2 e = (p2 (rest ([],e)), p3 (rest ([],e))) 

--Ejemplo: infer2 exp3 = ([],Boolean), donde exp3 se define como: 
exp3 :: Expr
exp3 =  Let "x" (B True) (And (V "x") ( Let "x" (I 10) (Eq ( I 0 ) ( Succ (V "x" )))))
------------------------------------------------------------------------------------------------------------------

exp4 :: Expr
exp4 = Add (V "x") (V "y")

{-Ejemplos:
main > infer ( Let ”x” (B True) (And (V ”x” ) ( Let ”x” ( I 1 0 ) (Eq ( I 0 ) ( Succ
(V ”x” )))))) ⇒ ( [ ] , Boolean )-}


{-data Expr = V Identifier | I Int | B Bool
            | Fn Identifier Expr
            | Succ Expr | Pred Expr
            | Add Expr Expr | Mul Expr Expr
            | Not Expr | Iszero Expr
            | And Expr Expr | Or Expr Expr
            | Lt Expr Expr | Gt Expr Expr | Eq Expr Expr
            | If Expr Expr Expr
            | Let Identifier Expr Expr
            | App Expr Expr deriving (Eq, Show)-}

-----------------------------------
--stack ghci src/Practica2.Minhs.hs
-----------------------------------
