module EAB where
-----------------------------------------------------------
--      Lenguajes de Programación y sus Paradigmas       --  
-----------------------------------------------------------            
--                      Práctica 1                       --
-----------------------------------------------------------
--Integrantes:                                           --
--1. Bernal Márquez Erick                                --
--2. Deloya Andrade Ana Valeria                                            -- 
--3. Villegas Barrón César                               --
-----------------------------------------------------------

----------------------------
--      Introducción      --
----------------------------

-- 1. Crear un nuevo tipo de dato el cual representa la sintaxis abstracta para el lenguaje EAB:

data EAB = Var String
        |  Num Int
        |  B Bool   
        |  Sum EAB EAB
        |  Prod EAB EAB
        |  Neg EAB
        |  Pred EAB
        |  Suc EAB
        |  And EAB EAB
        |  Or EAB EAB
        |  Not EAB
        |  Iszero EAB
        |  If EAB EAB EAB
        |  Let EAB EAB
        |  Abs String EAB deriving (Show,Eq) 
 
--------------------------------
--     Semántica Dinámica     --
--------------------------------

--1. Implementar la función eval1 :: EAB -> EAB tal que eval1 e = e’ syss e -> e’. 

--Primero definimos la función auxiliar "fv" que identificará cuál es el conjunto de variables libres de una expresión EAB 
fv :: EAB -> [String]
fv (Var x) = [x]
fv (Num _) = []
fv (B _) = []
fv (Sum e1 e2) = fv e1 ++ fv e2
fv (Prod e1 e2) = fv e1 ++ fv e2
fv (Neg e) = fv e
fv (Pred e) = fv e
fv (Suc e) = fv e
fv (And e1 e2) = fv e1 ++ fv e2
fv (Or e1 e2) = fv e1 ++ fv e2
fv (Not e) = fv e
fv (Iszero e) = fv e
fv (If e e1 e2) = fv e ++ fv e1 ++ fv e2
fv (Let e1 e2) = fv e1 ++ fv e2
fv (Abs z e) = filter (/= z) (fv e) 


--Definimos la función auxiliar "subs" que se utilizará para la evaluación de expresiones que usan alguna abstracción (Let, MatchNat etc.)
type Subst = (String,EAB) -- este type representa la sustitución de la forma "[x:=r]"

subs :: EAB -> Subst -> EAB
subs (Var x) (y,e) = if x == y 
                     then e 
                     else Var x
subs (Num n) _ = Num n
subs (B b) _ = B b
subs (Sum e1 e2) s = Sum (subs e1 s) (subs e2 s)
subs (Prod e1 e2) s = Prod (subs e1 s) (subs e2 s)
subs (Neg e) s = Neg (subs e s)
subs (Pred e) s = Pred (subs e s)
subs (Suc e) s = Suc (subs e s)
subs (And e1 e2) s = And (subs e1 s) (subs e2 s)
subs (Or e1 e2) s = Or (subs e1 s) (subs e2 s)
subs (Not e) s = Not (subs e s)
subs (Iszero e) s = Iszero (subs e s)
subs (If e e1 e2) s = If (subs e s) (subs e1 s) (subs e2 s)
subs (Let e1 e2) s = Let (subs e1 s) (subs e2 s)
subs (Abs z e) s@(x,r) = if z==x 
                         then error "se hará la sustitución de una variable ligada, busca una alfa equivalencia de tu expresión" 
                         else Abs z (subs e s)


--Con las funciones auxiliares "fv" y "subs" ya podemos definir el intérprete "eval1" de la siguiente manera:
eval1 :: EAB -> EAB
-- Variable
eval1 (Var x) = Var "x"
-- Número
eval1 (Num n) = Num n
-- Booleano
eval1 (B b) = B b
-- Suma
eval1 (Sum (Num n) (Num m)) = Num (n+m)
eval1 (Sum (Num n) e2) = Sum (Num n) (eval1 e2)
eval1 (Sum e1 e2) = Sum (eval1 e1) e2
-- Producto
eval1 (Prod (Num n) (Num m)) = Num (n*m)
eval1 (Prod (Num n) e2) = Prod (Num n) (eval1 e2)
eval1 (Prod e1 e2) = Prod (eval1 e1) e2
-- Inverso aditivo
eval1 (Neg (Num n)) = Num (-1*n)
eval1 (Neg e) = Neg (eval1 e)
-- Predecesor
eval1 (Pred (Num n)) = Num (n-1)
eval1 (Pred e) = Pred (eval1 e)
-- Sucesor        
eval1 (Suc (Num n)) = Num (n+1)
eval1 (Suc e) = Suc (eval1 e)
-- Conjunción
eval1 (And (B True) (B True)) = B True
eval1 (And (B True) (B False)) = B False
eval1 (And (B False) (B True)) = B False
eval1 (And (B False) (B False)) = B False
eval1 (And (B b) e2) = And (B b) (eval1 e2)
eval1 (And e1 e2) = And (eval1 e1) e2
-- Disyunción 
eval1 (Or (B True) (B True)) = B True
eval1 (Or (B True) (B False)) = B True
eval1 (Or (B False) (B True)) = B True
eval1 (Or (B False) (B False)) = B False
eval1 (Or (B b) e2) = Or (B b) (eval1 e2)
eval1 (Or e1 e2) = Or (eval1 e1) e2
-- Negación
eval1 (Not (B False)) = B True
eval1 (Not (B True)) = B False
eval1 (Not e) = Not (eval1 e)
-- Verificador del número 0
eval1 (Iszero (Num 0)) = B True
eval1 (Iszero (Num n)) = B False  
eval1 (Iszero e) =  Iszero (eval1 e)        
-- If ternario
eval1 (If (B True) e1 e2) = e1 
eval1 (If (B False) e1 e2) = e2
eval1 (If e e1 e2) = If (eval1 e) e1 e2 
-- Let binario
eval1 (Let e1 e2) = error "Implementar"
-- Abstracción
eval1 (Abs x e) = error "Implementar"

--2 Implementar la función evals :: EAB -> EAB tal que evals e e’ syss e ->* e’ y e’ está bloqueado.

evals :: EAB -> EAB
evals _ = error "Implementar"

--3 Implementar la función eval :: EAB -> EAB tal que eval e = e’syss e ->* e’ y e’ es un valor. 
--La diferencia con evals es que deben manejarse los errores de ejecución.

eval :: EAB -> EAB
eval _ = error "Implementar"

--------------------------------
--     Semántica Estática     --
--------------------------------

--1 Definir un tipo Type para los Tipos de EAB y definir otro tipo Ctx para los Contextos.

--data Type = () -- Definir los tipos de EAB
--type Ctx = () -- Definir un sinomo para los contextos

--2.  Definir la función de verificación de tipado vt :: Ctx -> EAB -> Type -> Bool tal
--que vt Γ e T = True si y sólo si Γ |- e: T.

--vt :: Ctx -> EAB -> Type -> Bool
--vt _ _ _ = error "Implementar"


--3. Implementar la función de evaluación evalt :: EAB → EAB que es esencialmente una reimplementación de la función eval de forma que evalt verifique el tipado de la expresión y sólo en caso positivo inicie el proceso de evaluación. En otro caso debe informarse de un error por existencia de variables libres o por tipado.


--evalt :: EAB -> EAB
--evalt _ = error "Implementar"


--------------------------------
--         Extra (•‿•)        -- 
--------------------------------


-----------------
-- Caso base, parametros ya reducidos
p :: EAB
p = Sum (Num 2) (Num 2)

q :: EAB
q = Prod (Num 5) (Num 2)

-- Resolver primero a la izquierda
r :: EAB
r = Sum (Sum (Num 3) (Num 4)) (Num 5)


-- Resolver a la derecha suponiendo que ya tengamos resuelto la izquierda
s :: EAB
s = Sum (Num 5) (Sum (Num 3) (Num 4))
-- El caso para las multiplicaciones es analogo

-- Tipos booleanos 
b1 :: EAB
b1 = And (B True) (B True)

b2 :: EAB
b2 = And (B False) (B True)

b3 :: EAB
b3 = And b2 (B True)

b4 :: EAB
b4 = And (B False) b1

b5 :: EAB
b5 = And b1 b2
-- El caso para la conjunción es analogo
-- data EAB = Var String
--         |  Num Int
--         |  B Bool   
--         |  Sum EAB EAB
--         |  Prod EAB EAB
--         |  Neg EAB
--         |  Pred EAB
--         |  Suc EAB
--         |  And EAB EAB
--         |  Or EAB EAB
--         |  Not EAB
--         |  Iszero EAB
--         |  If EAB EAB EAB
--         |  Let EAB EAB
--         |  Abs String EAB deriving (Show,Eq) 
