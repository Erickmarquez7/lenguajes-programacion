
module EAB1 where
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
        |  Abs String EAB 
        |  MatchNat EAB EAB EAB --Ejercicio extra
        |  Gt EAB EAB --Ejercicio extra
        |  Lt EAB EAB deriving (Show,Eq) --Ejercicio extra
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
fv (MatchNat e a1 a2) = fv e ++ fv a1 ++ fv a2 --Ejercicio extra
fv (Gt e1 e2) = fv e1 ++ fv e2 --Ejercicio extra
fv (Lt e1 e2) = fv e1 ++ fv e2 --Ejercicio extra

--Ahora definimos la función auxiliar "subs" que se utilizará para la evaluación de expresiones que usan alguna abstracción (Let, MatchNat etc.)
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
subs (MatchNat e a1 a2) s = MatchNat (subs e s) (subs a1 s) (subs a2 s) --Ejercicio extra
subs (Gt e1 e2) s = Gt (subs e1 s) (subs e2 s) --Ejercicio extra
subs (Lt e1 e2) s = Lt (subs e1 s) (subs e2 s) --Ejercicio extra
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
eval1 (Sum (B b) (Num n)) = Sum (B b) (Num n) --Término bloqueado
eval1 (Sum (Num n) (B b)) = Sum (Num n) (B b) --Término bloqueado
eval1 (Sum (B b) (B c)) = Sum (B b) (B c) --Término bloqueado
eval1 (Sum (Num n) e2) = Sum (Num n) (eval1 e2)
eval1 (Sum (B b) e2) = Sum (B b) (eval1 e2) --Término que será bloqueado
eval1 (Sum e1 e2) = Sum (eval1 e1) e2
-- Producto
eval1 (Prod (Num n) (Num m)) = Num (n*m)
eval1 (Prod (B b) (Num n)) = Prod (B b) (Num n) --Término bloqueado
eval1 (Prod (Num n) (B b)) = Prod (Num n) (B b) --Término bloqueado
eval1 (Prod (B b) (B c)) = Prod (B b) (B c) --Término bloqueado
eval1 (Prod (Num n) e2) = Prod (Num n) (eval1 e2)
eval1 (Prod (B b) e2) = Prod (B b) (eval1 e2) --Término que será bloqueado
eval1 (Prod e1 e2) = Prod (eval1 e1) e2
-- Inverso aditivo
eval1 (Neg (Num n)) = Num (-1*n) 
eval1 (Neg (B b)) = Neg (B b) --Término bloqueado
eval1 (Neg e) = Neg (eval1 e) 
-- Predecesor
eval1 (Pred (Num n)) = Num (n-1)
eval1 (Pred (B b)) = Pred (B b) --Término bloqueado
eval1 (Pred e) = Pred (eval1 e)
-- Sucesor        
eval1 (Suc (Num n)) = Num (n+1)
eval1 (Suc (B b)) = Suc (B b) --Término bloqueado
eval1 (Suc e) = Suc (eval1 e)
-- Conjunción
eval1 (And (B True) (B True)) = B True
eval1 (And (B False) (B b)) = B False
eval1 (And (B b) (B False)) = B False
eval1 (And (B b) (Num n)) = And (B b) (Num n) --Término bloqueado
eval1 (And (B b) e2) = And (B b) (eval1 e2)
eval1 (And (Num n) (B b)) = And (Num n) (B b) --Término bloqueado
eval1 (And (Num n) (Num m)) = And (Num n) (Num m) --Término bloqueado
eval1 (And (Num n) e2) = And (Num n) (eval1 e2)  --Término que será bloqueado
eval1 (And e1 e2) = And (eval1 e1) e2
-- Disyunción 
eval1 (Or (B True) (B b)) = B True
eval1 (Or (B b) (B True)) = B True
eval1 (Or (B False) (B False)) = B False
eval1 (Or (B b) (Num n)) = Or (B b) (Num n) --Término bloqueado
eval1 (Or (B b) e2) = Or (B b) (eval1 e2)
eval1 (Or (Num n) (B b)) = Or (Num n) (B b) --Término bloqueado
eval1 (Or (Num n) (Num m)) = Or (Num n) (Num m) --Término bloqueado
eval1 (Or (Num n) e2) = Or (Num n) (eval1 e2) --Término que será bloqueado
eval1 (Or e1 e2) = Or (eval1 e1) e2
-- Negación
eval1 (Not (B False)) = B True
eval1 (Not (B True)) = B False
eval1 (Not (Num n)) = Not (Num n) --Término bloqueado
eval1 (Not e) = Not (eval1 e)
-- Verificador del número 0
eval1 (Iszero (Num 0)) = B True
eval1 (Iszero (Num n)) = B False
eval1 (Iszero (B b)) = Iszero (B b) --Término bloqueado
eval1 (Iszero e) = Iszero (eval1 e)
-- If ternario
eval1 (If (B True) e1 e2) = e1 
eval1 (If (B False) e1 e2) = e2
eval1 (If (Num n) e1 e2) = If (Num n) e1 e2 --Término bloqueado
eval1 (If e e1 e2) = If (eval1 e) e1 e2 
-- Let binario
eval1 (Let (B b) (Abs x e2)) = subs e2 (x, B b)
eval1 (Let (Num n) (Abs x e2)) = subs e2 (x, Num n)
eval1 (Let e1  (Abs x e2)) = Let (eval1 e1) (Abs x e2)
--MatchNat ternario - Ejercicio extra
eval1 (MatchNat (Num n) a1 (Abs x a2)) = if n == 0
                                         then a1
                                         else subs a2 (x, Num (n-1))
eval1 (MatchNat (B b) a1 (Abs x a2)) = MatchNat (B b) a1 (Abs x a2) --Término bloqueado
eval1 (MatchNat e a1 (Abs x a2)) = MatchNat (eval1 e) a1 (Abs x a2) 
--Gt (mayor que) -- Ejercicio extra 
eval1 (Gt (Num n) (Num m)) =  if n - m > 0 then B True else B False
eval1 (Gt (Num n) (B b)) = Gt (Num n) (B b) --Término bloqueado
eval1 (Gt (B b) (Num n)) = Gt (B b) (Num n) --Término bloqueado
eval1 (Gt (B b) e2 ) = Gt (B b) (eval1 e2) --Término que será bloqueado
eval1 (Gt (Num n) e2 ) = Gt (Num n) (eval1 e2)
eval1 (Gt e1 e2 ) = Gt (eval1 e1) e2 
--Lt (menor que) -- Ejercicio extra
eval1 (Lt (Num n) (Num m)) =  if n - m < 0 then B True else B False
eval1 (Lt (Num n) (B b)) = Lt (Num n) (B b) --Término bloqueado
eval1 (Lt (B b) (Num n)) = Lt (B b) (Num n) --Término bloqueado
eval1 (Lt (B b) e2 ) = Lt (B b) (eval1 e2) --Término que será bloqueado
eval1 (Lt (Num n) e2 ) = Lt (Num n) (eval1 e2)
eval1 (Lt e1 e2 ) = Lt (eval1 e1) e2 

eval1 e = error "¡eval1!, algo salió mal D:, revisa que tu expresión esté correcta"

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
evals (Let e1 (Abs x e2)) =  evals (Let (evals e1) (Abs x e2))
--MatchNat ternario - Ejercicio extra
evals (MatchNat (Num n) a1 (Abs x a2)) = evals (eval1 (MatchNat (Num n) a1 (Abs x a2)))
evals (MatchNat (B b) a1 (Abs x a2)) = MatchNat (B b) a1 (Abs x a2) --Término bloqueado
evals (MatchNat a e1 (Abs x e2)) = evals (MatchNat (evals a) e1 (Abs x e2)) 
--Gt (mayor que) -- Ejercicio extra 
evals (Gt e1 e2) = eval1 (Gt (evals e1) (evals e2)) 
--Lt (menor que) -- Ejercicio extra
evals (Lt e1 e2) = eval1 (Lt (evals e1) (evals e2))
evals e = error "¡evals!, algo salió mal D:, revisa que tu expresión esté correcta"

--3 Implementar la función eval :: EAB -> EAB tal que eval e = e’syss e ->* e’ y e’ es un valor. 
--La diferencia con evals es que deben manejarse los errores de ejecución.
eval :: EAB -> EAB
-- Variable
eval (Var x) = eval1 (Var x)
-- Número
eval (Num n) = eval1 (Num n)
-- Booleano
eval (B b) = eval1 (B b)
-- Suma
eval (Sum (B b) _) = error "La suma solo adminte números"
eval (Sum _ (B b) ) = error "La suma solo adminte números"
eval (Sum e1 e2) = eval1 (Sum (eval e1) (eval e2))
-- Producto
eval (Prod (B b) _) = error "El producto solo adminte números"
eval (Prod _ (B b) ) = error "El producto solo adminte números"
eval (Prod e1 e2) = eval1 (Prod (eval e1) (eval e2))
-- Inverso aditivo
eval (Neg (B b)) = error "El inverso solo funciona con números"
eval (Neg e) = eval1 (Neg (evals e))
-- Predecesor
eval (Pred (B b)) = error "El predecesor solo admite números"
eval (Pred e) = eval1 (Pred (evals e))  
-- Sucesor
eval (Suc (B b)) = error "El sucesor solo admite números"                                                              
eval (Suc e) = eval1 (Suc (eval e)) 
-- Conjunción
eval (And (Num n) _ ) = error "La conjunción solo admite booleanos"
eval (And _ (Num n) ) = error "La conjunción solo admite booleanos"
eval (And e1 e2) = eval1 (And (eval e1) (eval e2))
-- Disyunción 
eval (Or (Num n) _) = error "La disyunción solo admite booleanos"
eval (Or _ (Num n)) = error "La disyunción solo admite booleanos"
eval (Or e1 e2) = eval1 (Or (eval e1) (eval e2))
-- Negación
eval (Not (Num n)) = error "El argumento de una negación debe ser un booleano"
eval (Not e) = eval1 (Not (eval1 e))
-- Verificador del número 0
eval (Iszero (B b)) = error "El argumento de un Iszero debe ser un número"
eval (Iszero e) = eval1 (Iszero (eval e))
-- If ternario
eval (If (Num n) e1 e2) = error "El primer argumento de un If debe ser booleano"
eval (If e e1 e2) = eval1 (If (eval e) (eval e1) (eval e2))
-- Let binario
eval (Let (Num n) (Abs x e2)) = eval (eval1 (Let (Num n) (Abs x e2)))
eval (Let (B b) (Abs x e2)) = eval (eval1 (Let (B b) (Abs x e2)))
eval (Let e1 (Abs x e2)) =  eval (Let (eval e1) (Abs x e2))
--MatchNat ternario - Ejercicio extra
eval (MatchNat (Num n) a1 (Abs x a2)) = eval (eval1 (MatchNat (Num n) a1 (Abs x a2)))
eval (MatchNat (B b) a1 (Abs x a2)) = error "El primer argumento de un MatchNat debe ser un número"
eval (MatchNat a e1 (Abs x e2)) = eval (MatchNat (eval a) e1 (Abs x e2)) 
--Gt (mayor que) -- Ejercicio extra 
eval (Gt (B b) _) = error "El primer argumento de un Gt (mayor que) debe ser un número"
eval (Gt _ (B b)) = error "El segundo argumento de un Gt (mayor que) debe ser un número"
eval (Gt e1 e2) = eval1 (Gt (eval e1) (eval e2))
--Lt (menor que) -- Ejercicio extra
eval (Lt (B b) _) = error "El primer argumento de un Lt (menor que) debe ser un número"
eval (Lt _ (B b)) = error "El segundo argumento de un Lt (menor que) debe ser un número"
eval (Lt e1 e2) = eval1 (Lt (eval e1) (eval e2))

eval e = error "¡eval!, algo salió mal D:, revisa que tu expresión esté correcta"


--------------------------------
--     Semántica Estática     --
--------------------------------

--1 Definir un tipo Type para los Tipos de EAB y definir otro tipo Ctx para los Contextos.

data Type = TNum 
          | TBool deriving (Show,Eq)
type Ctx = [(String,Type)]

--2.  Definir la función de verificación de tipado vt :: Ctx -> EAB -> Type -> Bool tal
--que vt Γ e T = True si y sólo si Γ |- e: T.

--    [], exp, Num o Varvt :: Ctx -> EAB -> Type -> Bool

vt :: Ctx -> EAB -> Type -> Bool
--vt [_,("x",a)] (Var "x") a = True --(tvar)
-- Casos base
vt _ (Num n) TNum = True --(tnum)
vt _ (Num n) TBool = False --Error de tipado
vt _ (B True) TBool = True --(ttrue)
vt _ (B False) TBool = True --(tfalse)
vt _ (B True) TNum = False --Error de tipado
vt _ (B False) TNum = False --Error de tipado

vt g (Sum e1 e2) TNum = vt g e1 TNum && vt g e2 TNum --(tsum)
vt g (Sum e1 e2) TBool = False --Error de tipado
vt g (Prod e1 e2) TNum = vt g e1 TNum && vt g e2 TNum --(tprod)
vt g (Prod e1 e2) TBool = False -- Error de tipado
vt g (Neg e1) TNum = vt g e1 TNum --(tneg)
vt g (Neg e1) TBool = False --Error de tipado
vt g (Pred e) TNum = vt g e TNum --(tpred)
vt g (Pred e) TBool = False --Error de tipado
vt g (Suc e) TNum = vt g e TNum --(tsuc)
vt g (Suc e) TBool = False --Error de tipado
vt g (And e1 e2) TBool = vt g e1 TBool && vt g e2 TBool --(tand)
vt g (And e1 e2) TNum = False --Error de tipado
vt g (Or e1 e2) TBool = vt g e1 TBool && vt g e2 TBool --(tor)
vt g (Or e1 e2) TNum = False --Error de tipado
vt g (Not e) TBool = vt g e TBool --(tnot)
vt g (Not e) TNum = False --Error de tipado
vt g (Iszero e) TBool = vt g e TNum --(tisz)
vt g (Iszero e) TNum = False --Error de tipado
vt g (If e1 e2 e3) t = vt g e1 TBool && vt g e2 t && vt g e3 t --(tif)
vt g (Let e1 (Abs x e2)) s = vt g e1 TNum && (vt (g++[("x",TNum)]) e2 s || (vt g e1 TBool && vt (g++[("x",TBool)]) e2 s))


--vt g (Abs s) = 
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

--vt _ (Sum (Num n) e) TNum = (vt _ (Num n) TNum) && (vt _ e TNum) --(tsum)
--vt _ Prod(e1 e2) TNum = (vt _ e1 TNum) &&  
--vt _ (Prod (Num n) (Num m)) TNum = True

vt e1 e2 e3 = error "a?"



sum' :: EAB
sum' = Sum (Num 3) (Num 3)

--3. Implementar la función de evaluación evalt :: EAB → EAB que es esencialmente una reimplementación de la función eval de forma que evalt verifique el tipado de la expresión y sólo en caso positivo inicie el proceso de evaluación. En otro caso debe informarse de un error por existencia de variables libres o por tipado.

evalt :: EAB -> EAB
evalt _ = error "Implementar"

--------------------------------
--         Extra (•‿•)        -- 
--------------------------------

--1. Agrega a nuestro lenguaje las expresiones de matchNat y orden "mayor que" (Gt) y "menor que" (Lt). La especificación para los operadores de orden es la usual, y para marchNat es la siguiente:
--Sintaxis Concreta: marchNat e with 0 -> e1 | suc x -> e2 end
--Semántica: para evaluar una expresión marchNat debemos evaluar e a un valor v. Si v es 0 se devuelve el valor de el y si v es suc v' entonces se devueleve el valor de e2 pasando el valor v' a x.

--Este ejercicio se hizo en conjunto con las anteriores preguntas de la práctica
--Para evaluar las expresiónes MatchNat, Gt y Lt debemos usar la función "eval" y se debe traducir la expresión en sintaxis concreta de la siguiente forma:

-- 1. eval (matchNat e with 0 -> e1 | suc x -> e2 end) <=> eval (MathNat e e1 (Abs x e2))
--Ejemplo
mn :: EAB
mn = MatchNat (Pred (Sum (Num 5) (Num 7))) (Num 7) (Abs "x" (Prod (Num 3) (Var "x")))

--Al introducir el comando "eval mn" en la terminal obtenemos el resultado deseado (Num 30).
-- 2. eval (e1 > e2) <=> eval (Gt e1 e2)
--Ejemplo

r :: EAB
r = Prod (Sum (Num 3) (Num 4)) (Num 5) -- = 35
gt1 :: EAB
gt1 = Gt r mn
--Al introducir el comando "eval gt1" en la terminal obtenemos el resultado deseado 35 > 30 -> B True.
--eval (e1 < e2) <=> eval (Lt e1 e2)

--Ejemplo
lt1 :: EAB
lt1 = Lt r mn
--Al introducir el comando "eval lt1" en la terminal obtenemos el resultado deseado 35 < 30 -> B False.
-----------------------------------------------------------------------------------------------------------------------
-- Caso base, parametros ya reducidos
p :: EAB
p = Sum (Num 2) (Num 2)

q :: EAB
q = Prod (Num 5) (Num 2)

-- Resolver primero a la izquierda
--r :: EAB
--r = Sum (Sum (Num 3) (Num 4)) (Num 5)

-- Resolver a la derecha suponiendo que ya tengamos resuelto la izquierda
--s :: EAB
--s = Sum (Num 5) (Sum (Num 3) (Num 4))
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

b6 :: EAB
b6 = Or (B True) (B False)

--Probando el Let
let1 :: EAB
let1 = Let (Num 4) (Abs "z" (Sum (Var "z") (Num 1))) -- let z = 4 in z + 1 o let(4,z.z+1)


let2 :: EAB
let2 = Let (Sum (Num 7) (Num 3)) (Abs "z" (Sum (Var "z") (Num 1))) -- let z = 4 in z + 1 o let(4,z.z+1)

let3 :: EAB
let3 = Let (Num 4) (Abs "z" (Prod (Sum (Var "z") (Num 1)) (Num 3) ) ) -- let z = 4 in z + 1 o let(4,z.z+1)

if1 :: EAB
if1 = If (Iszero (B True)) (Num 2) (Num 3)

if2 :: EAB
if2 =If (Iszero (Sum (Num (-1)) (Num 1))) (Num 2) (Num 3)

--Probando el MatchNat

mn1 :: EAB
mn1 =  MatchNat (Num 0) (Num 4) (Abs "x" (Sum (Var "x") (Num 5)))

mn2 :: EAB
mn2 = MatchNat r (Num 4) (Abs "x" (Sum (Var "x") (Num 5)))
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
