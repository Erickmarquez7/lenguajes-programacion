module EAB where
-----------------------------------------------------------
--      Lenguajes de Programación y sus Paradigmas       --  
-----------------------------------------------------------            
--                      Práctica 1                       --
-----------------------------------------------------------
--Integrantes:                                           --
--1. Bernal Márquez Erick                                --
--2. Deloya Andrade Ana Valeria                          -- 
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
subs (Abs z e) (x,r) | z==x          = error "se hará una sustitución en una variable ligada "
                     | z `elem` fv r = error "la expresion a sustituir tiene una variable con el mismo nombre que una ligada" 
                     | otherwise     = Abs z (subs e (x,r))

--Con las funciones auxiliares "fv" y "subs" ya podemos definir el intérprete "eval1" de la siguiente manera:

eval1 :: EAB -> EAB
-- Variable
eval1 (Var x) = error "no se pueden evaluar expresiones con variables libres"
-- Número
eval1 (Num n) = Num n
-- Booleano
eval1 (B b) = B b
-- Suma
eval1 (Sum (Num n) (Num m)) = Num (n+m)
eval1 (Sum (B b) (Num n)) = Sum (B b) (Num n)
eval1 (Sum (Num n) (B b)) = Sum (Num n) (B b)
eval1 (Sum (B b) (B c)) = Sum (B b) (B c)
eval1 (Sum (Num n) e2) = Sum (Num n) (eval1 e2)
eval1 (Sum (B b) e2) = Sum (B b) (eval1 e2)
eval1 (Sum e1 e2) = Sum (eval1 e1) e2
-- Producto
eval1 (Prod (Num n) (Num m)) = Num (n*m)
eval1 (Prod (B b) (Num n)) = Prod (B b) (Num n)
eval1 (Prod (Num n) (B b)) = Prod (Num n) (B b)
eval1 (Prod (B b) (B c)) = Prod (B b) (B c)
eval1 (Prod (Num n) e2) = Prod (Num n) (eval1 e2)
eval1 (Prod (B b) e2) = Prod (B b) (eval1 e2)
eval1 (Prod e1 e2) = Prod (eval1 e1) e2
-- Inverso aditivo
eval1 (Neg (Num n)) = Num (-1*n)
eval1 (Neg (B b)) = Neg (B b)
eval1 (Neg e) = Neg (eval1 e)
-- Predecesor
eval1 (Pred (Num n)) = Num (n-1)
eval1 (Pred (B b)) = Pred (B b)
eval1 (Pred e) = Pred (eval1 e)
-- Sucesor        
eval1 (Suc (Num n)) = Num (n+1)
eval1 (Suc (B b)) = Suc (B b)
eval1 (Suc e) = Suc (eval1 e)
-- Conjunción
eval1 (And (B True) (B True)) = B True
eval1 (And (B False) (B b)) = B False
eval1 (And (B b) (B False)) = B False
eval1 (And (B b) (Num n)) = And (B b) (Num n)
eval1 (And (B b) e2) = And (B b) (eval1 e2)
eval1 (And (Num n) (B b)) = And (Num n) (B b)
eval1 (And (Num n) (Num m)) = And (Num n) (Num m)
eval1 (And (Num n) e2) = And (Num n) (eval1 e2)  
eval1 (And e1 e2) = And (eval1 e1) e2
-- Disyunción 
eval1 (Or (B True) (B b)) = B True
eval1 (Or (B b) (B True)) = B True
eval1 (Or (B False) (B False)) = B False
eval1 (Or (B b) (Num n)) = Or (B b) (Num n)
eval1 (Or (B b) e2) = Or (B b) (eval1 e2)
eval1 (Or (Num n) (B b)) = Or (Num n) (B b)
eval1 (Or (Num n) (Num m)) = Or (Num n) (Num m)
eval1 (Or (Num n) e2) = Or (Num n) (eval1 e2)
eval1 (Or e1 e2) = Or (eval1 e1) e2
-- Negación
eval1 (Not (B False)) = B True
eval1 (Not (B True)) = B False
eval1 (Not (Num n)) = Not (Num n)
eval1 (Not e) = Not (eval1 e)
-- Verificador del número 0
eval1 (Iszero (Num 0)) = B True
eval1 (Iszero (Num n)) = B False
eval1 (Iszero (B b)) = Iszero (B b)
eval1 (Iszero e) = Iszero (eval1 e)
-- If ternario
eval1 (If (B True) e1 e2) = e1 
eval1 (If (B False) e1 e2) = e2
eval1 (If (Num n) e1 e2) = If (Num n) e1 e2
eval1 (If e e1 e2) = If (eval1 e) e1 e2 
-- Let binario
eval1 (Let (B b) (Abs x e2)) = subs e2 (x, B b)
eval1 (Let (Num n) (Abs x e2)) = subs e2 (x, Num n)
eval1 (Let e1  (Abs x e2)) = Let (eval1 e1) (Abs x e2)

eval1 e = error "eval1 - adiós warning Pattern match(es) are non-exhaustive :)"

--2 Implementar la función evals :: EAB -> EAB tal que evals e e’ syss e ->* e’ y e’ está bloqueado.
evals :: EAB -> EAB
-- Variable
evals (Var x) = eval1 (Var x)
-- Número
evals (Num n) = eval1 (Num n)
-- Booleano
evals (B b) = eval1 (B b)
-- Suma
evals (Sum e1 e2) = eval1 (Sum (evals e1) (evals e2))
-- Producto
evals (Prod e1 e2) = eval1 (Prod (evals e1) (evals e2))
-- Inverso aditivo
evals (Neg e) = eval1 (Neg (evals e))
-- Predecesor
evals (Pred e) = eval1 (Pred (evals e))  
-- Sucesor                                                              
evals (Suc e) = eval1 (Suc (evals e)) 
-- Conjunción
evals (And e1 e2) = eval1 (And (evals e1) (evals e2))
-- Disyunción                                              
evals (Or e1 e2) = eval1 (Or (evals e1) (evals e2))
-- Negación
evals (Not e) = eval1 (Not (eval1 e))
-- Verificador del número 0
evals (Iszero e) = eval1 (Iszero (evals e))
-- If ternario
evals (If e e1 e2) = eval1 (If (evals e) (evals e1) (evals e2))
-- Let binario
evals (Let (Num n) (Abs x e2)) = evals (eval1 (Let (Num n) (Abs x e2)))
evals (Let (B b) (Abs x e2)) = evals (eval1 (Let (B b) (Abs x e2)))
evals (Let e1 (Abs x e2)) = eval1 (Let (evals e1) (Abs x e2))

evals e = error "evals - adiós warning 'Pattern match(es) are non-exhaustive' :)"

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

--Probando el Let
let1 :: EAB
let1 = Let (Num 4) (Abs "z" (Sum (Var "z") (Num 1))) -- let z = 4 in z + 1 o let(4,z.z+1)

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
