module Practica4.MaquinaK where
import Data.List

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
            | App Expr Expr
            | Raise Expr
            | Handle Expr Identifier Expr deriving(Eq)


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
            | HandleF Identifier Expr deriving (Eq)


{-- Show para las Expr -}
instance Show Expr where
    show e = case e of
      V s             -> "V("++ s ++")"
      I n             -> "I("++ show n ++")"
      B b             -> "B("++ show b ++")"
      Fn i e          -> "Fn("++i++"."++show e++")"
      Succ ex         -> "Succ("++ show ex ++")"
      Pred ex         -> "Pred("++ show ex ++")"
      Add ex ex'      -> "Add("++ show ex ++", "++ show ex'++")"
      Mul ex ex'      -> "Mul("++ show ex ++", "++ show ex'++")"
      Not ex          -> "Not("++ show ex ++")"
      Iszero ex       -> "IsZero("++ show ex ++")"
      And ex ex'      -> "And("++ show ex ++", "++ show ex'++")"
      Or ex ex'       -> "Or("++ show ex ++", "++ show ex'++")"
      Lt ex ex'       -> "Lt("++ show ex ++", "++ show ex'++")"
      Gt ex ex'       -> "GT("++ show ex ++", "++ show ex'++")"
      Eq ex ex'       -> "Eq("++ show ex ++", "++ show ex'++")"
      If ex ex' ex2   -> "If("++ show ex ++", "++ show ex'++", "++ show ex2++")"
      Let i ex  ex'   -> "Let("++ show ex ++", "++ i++"."++ show ex'++")"
      App ex ex'      -> "App("++ show ex ++", "++ show ex'++")"
      Raise ex        -> "Raise("++ show ex ++")"
      Handle ex s ex' -> "Handle("++show ex++", "++s++", "++show ex'++")"


--1. (1 punto) Crea una instancia de la clase Show para los marcos de acuerdo a la sintaxis descrita en las notas del curso.

{-- Show para los Frame -}
instance Show Frame where
    show e = case e of
        (AddFL a)     -> "Add(-, "++show a++")"
        (AddFR a)     -> "Add("++show a++", -)"
        (MulFL a)     -> "Mul(-, "++show a++")"
        (MulFR a)     -> "Mul("++show a++", -)"
        SuccF         -> "Succ(-)"
        PredF         -> "Pred(-)"
        (AndFL a)     -> "And(-, "++show a++")"
        (AndFR a)     -> "And("++show a++", -)"
        (OrFL a)      -> "Or(-, "++show a++")"
        (OrFR a)      -> "Or("++show a++", -)"
        NotF          -> "Not(-)"
        IsZeroF       -> "IsZero(-)"
        (LtFL a)      -> "Lt(-, "++show a++")"
        (GtFL a)      -> "Gt("++show a++", -)"
        (LtFR a)      -> "Lt(-, "++show a++")"
        (GtFR a)      -> "Gt("++show a++", -)"
        (EqFL a)      -> "Eq(-, "++show a++")"
        (EqFR a)      -> "Eq("++show a++", -)"
        (IfF a b)     -> "If(-, "++show a++", "++show b++")"
        (LetM a b)    -> "LetM(-, "++show a++", "++show b++")"
        (AppFL a)     -> "Eq(-, "++show a++")"
        (AppFR a)     -> "Eq("++show a++", -)"
        RaiseF        -> "Raise(-)"
        (HandleF a b) -> "HandleF(-, "++a++"."++show b++")"

        
-- 5. Extender la funcion frVars 
frVars :: Expr -> [Identifier]
frVars (V i)          = [i]
frVars (I n)          = []
frVars (B b)          = []
frVars (Fn x e)       = filter (/= x) (frVars e)
frVars (Succ b)       = frVars b
frVars (Pred p)       = frVars p
frVars (Add a b)      = frVars a `union` frVars b
frVars (Mul a b)      = frVars a `union` frVars b
frVars (Not p)        = frVars p
frVars (Iszero i)     = frVars i
frVars (And p q)      = frVars p `union` frVars q
frVars (Or p q)       = frVars p `union` frVars q
frVars (Lt p q)       = frVars p `union` frVars q
frVars (Gt p q)       = frVars p `union` frVars q
frVars (Eq p q)       = frVars p `union` frVars q
frVars (If a b c)     = frVars a `union` frVars b `union` frVars c
frVars (Let x a b)    = frVars a `union` filter (/=x) (frVars b)
frVars (App a b)      = frVars a `union` frVars b
frVars (Raise a)      = frVars a
frVars (Handle a x c) = frVars a `union` filter (/=x) (frVars c)


-- 5. Extender la funcion subst
type Substitution = (Identifier, Expr)
subst :: Expr -> Substitution -> Expr
subst (V x) (id, e)         | x == id = e
                            | otherwise = V x
subst (I n) _               = I n
subst (B b) _               = B b
subst (Fn x e) s            |              x == fst s = error "Se hará una sustitución en una variable ligada, busca una alfa equivalencia de tu expresión Fn"
                            | x `elem` frVars (snd s) = error "La expresion a sustituir tiene una variable con el mismo nombre que una ligada a una expresión Fn, busca una alfa equivalencia"
                            |               otherwise = Fn x (subst e s)
subst (Succ c) s            = Succ (subst c s)
subst (Pred p) s            = Pred (subst p s)
subst (Add a b) s           = Add (subst a s) (subst b s)
subst (Mul a b) s           = Mul (subst a s) (subst b s)
subst (Not b) s             = Not (subst b s)
subst (Iszero a) s          = Iszero (subst a s)
subst (And p q) s           = And (subst p s) (subst q s)
subst (Or p q) s            = Or (subst p s) (subst q s)
subst (Lt p q) s            = Lt (subst p s) (subst q s)
subst (Gt p q) s            = Gt (subst p s) (subst q s)
subst (Eq p q) s            = Eq (subst p s) (subst q s)
subst (If c a b) s          = If (subst c s) (subst a s) (subst b s)
subst (Let x e1 e2) (y,e) |            x == y = error "Se hará una sustitución en una variable ligada, busca una alfa equivalencia de una expresión Let"
                          | x `elem` frVars e = error "La expresion a sustituir tiene una variable con el mismo nombre que una ligada a una expresión Let, busca una alfa equivalencia"
                          |         otherwise = Let x (subst e1 (y,e)) (subst e2 (y,e))
subst (App a b) s           = App (subst a s) (subst b s)
subst (Raise a) s           = Raise (subst a s)
subst (Handle e1 x e2) (i,e)
                          | x == i || elem x (frVars e) = Handle e1 x e2
                          | x `elem` frVars e = error "Variables en comun ligadas. Encuentra una alfa equivalencia"
                          | otherwise = Handle (subst e1 (i,e)) x (subst e2 (i,e))


-- Defincion de pila de marcos
data Stack = Empty | S Frame Stack deriving (Show, Eq)


--Definicion de los estados
data State =  E Stack Expr -- P;⬚ > e
            | R Stack Expr -- P;⬚ < e
            | P Stack Expr deriving (Show, Eq)-- P;⬚ << e 

--La siguiente función auxiliar servirá para definir las interacciones rise <-> handle:
isHandleF :: Frame -> Bool
isHandleF (HandleF x e) = True 
isHandleF _             = False

-- 2. (5 puntos) eval1. Re implementa esta función para que dado un estado, devuelva un paso de transicion,
-- es decir, eval1 s = s’ si y sólo si s →_k s’
eval1 :: State -> State
----------------------Valores----------------------------------
eval1 (E Empty (I n))    = R Empty (I n) -----Estado final
eval1 (E Empty (B b))    = R Empty (B b) -----Estado final
eval1 (E Empty (V v))    = R Empty (V v) -----Término bloqueado
eval1 (E Empty (Fn x e)) = R Empty (Fn x e) --Estado final
eval1 (E s (I n))        = R s (I n)
eval1 (E s (B b))        = R s (B b) 
eval1 (E s (V v))        = R s (V v)
eval1 (E s (Fn x e))     = R s (Fn x e)
------------------------------Sucesor--------------------------------------
eval1 (R (S SuccF s) (B b))    = R (S SuccF s) (B b)------Término bloqueado
eval1 (R (S SuccF s) (V v))    = R (S SuccF s) (V v)------Término bloqueado
eval1 (R (S SuccF s) (Fn x e)) = R (S SuccF s) (Fn x e) --Término bloqueado
eval1 (R (S SuccF s) (I n))    = E s (I (n+1))------------Caso significativo
eval1 (E s (Succ e))           = E (S SuccF s) e ---------Caso significativo
-----------------------------Predecesor -----------------------------------
eval1 (R (S PredF s) (B b))    = R (S PredF s) (B b)------Término bloqueado
eval1 (R (S PredF s) (V v))    = R (S PredF s) (V v)------Término bloqueado
eval1 (R (S PredF s) (Fn x e)) = R (S PredF s) (Fn x e) --Término bloqueado
eval1 (R (S PredF s) (I n))    = E s (I (n-1))------------Caso significativo
eval1 (E s (Pred e))           = E (S PredF s) e----------Caso significativo
------------------------------------Suma--------------------------------------------------
eval1 (R (S (AddFL e2) s) (B b))       = E (S (AddFR (B b)) s) e2--------Término bloqueado 
eval1 (R (S (AddFL e2) s) (V v))       = E (S (AddFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (AddFL e2) s) (Fn x e))    = E (S (AddFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (AddFR (I n)) s) (B b))    = R (S (AddFR (I n)) s) (B b)-----Término bloqueado
eval1 (R (S (AddFR (I n)) s) (V v))    = R (S (AddFR (I n)) s) (V v)-----Término bloqueado
eval1 (R (S (AddFR (I n)) s) (Fn x e)) = R (S (AddFR (I n)) s) (Fn x e)--Término bloqueado
eval1 (R (S (AddFL e2) s) (I n))       = E (S (AddFR (I n)) s) e2--------Caso significativo
eval1 (R (S (AddFR (I n)) s) (I m))    = R s (I (n + m))-----------------Caso significativo
eval1 (E s (Add e1 e2))                = E (S (AddFL e2) s) e1-----------Caso significativo
----------------------------------Producto------------------------------------------------
eval1 (R (S (MulFL e2) s) (B b))       = E (S (MulFR (B b)) s) e2--------Término bloqueado 
eval1 (R (S (MulFL e2) s) (V v))       = E (S (MulFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (MulFL e2) s) (Fn x e))    = E (S (MulFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (MulFR (I n)) s) (B b))    = R (S (MulFR (I n)) s) (B b)-----Término bloqueado
eval1 (R (S (MulFR (I n)) s) (V v))    = R (S (MulFR (I n)) s) (V v)-----Término bloqueado
eval1 (R (S (MulFR (I n)) s) (Fn x e)) = R (S (MulFR (I n)) s) (Fn x e)--Término bloqueado
eval1 (R (S (MulFL e2) s) (I n))       = E (S (MulFR (I n)) s) e2--------Caso significativo
eval1 (R (S (MulFR (I n)) s) (I m))    = R s (I (n * m))-----------------Caso significativo
eval1 (E s (Mul e1 e2))                = E (S (MulFL e2) s) e1-----------Caso significativo
---------------------------------Conjuntción----------------------------------------------
eval1 (R (S (AndFL e2) s) (I n))       = E (S (AndFR (I n)) s) e2--------Término bloqueado 
eval1 (R (S (AndFL e2) s) (V v))       = E (S (AndFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (AndFL e2) s) (Fn x e))    = E (S (AndFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (AndFR (B b)) s) (I n))    = R (S (AndFR (B b)) s) (I n)-----Término bloqueado
eval1 (R (S (AndFR (B b)) s) (V v))    = R (S (AndFR (B b)) s) (V v)-----Término bloqueado
eval1 (R (S (AndFR (B b)) s) (Fn x e)) = R (S (AndFR (B b)) s) (Fn x e)--Término bloqueado
eval1 (R (S (AndFL e2) s) (B b))       = E (S (AndFR (B b)) s) e2--------Caso significativo
eval1 (R (S (AndFR (B b)) s) (B d))    = R s (B (b && d))----------------Caso significativo
eval1 (E s (And e1 e2))                = E (S (AndFL e2) s) e1-----------Caso significativo
---------------------------------Disyunción---------------------------------------------
eval1 (R (S (OrFL e2) s) (I n))       = E (S (OrFR (I n)) s) e2--------Término bloqueado 
eval1 (R (S (OrFL e2) s) (V v))       = E (S (OrFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (OrFL e2) s) (Fn x e))    = E (S (OrFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (OrFR (B b)) s) (I n))    = R (S (OrFR (B b)) s) (I n)-----Término bloqueado
eval1 (R (S (OrFR (B b)) s) (V v))    = R (S (OrFR (B b)) s) (V v)-----Término bloqueado
eval1 (R (S (OrFR (B b)) s) (Fn x e)) = R (S (OrFR (B b)) s) (Fn x e)--Término bloqueado
eval1 (R (S (OrFL e2) s) (B b))       = E (S (OrFR (B b)) s) e2--------Caso significativo
eval1 (R (S (OrFR (B b)) s) (B d))    = R s (B (b || d))---------------Caso significativo
eval1 (E s (Or e1 e2))                = E (S (OrFL e2) s) e1-----------Caso significativo
----------------------------Negación------------------------------------
eval1 (R (S NotF s) (I n))    = E (S NotF s) (I n)-----Término bloqueado
eval1 (R (S NotF s) (V v))    = E (S NotF s) (V v)-----Término bloqueado
eval1 (R (S NotF s) (Fn x e)) = E (S NotF s) (Fn x e)--Término bloqueado
eval1 (R (S NotF s) (B b))    = R s (B (not b))--------Caso significativo
eval1 (E s (Not e))           = E (S NotF s) e---------Caso significativo
--------------------------Test iszero-----------------------------------------
eval1 (R (S IsZeroF s) (B b))    = E (S IsZeroF s) (B b)-----Término bloqueado
eval1 (R (S IsZeroF s) (V v))    = E (S IsZeroF s) (V v)-----Término bloqueado
eval1 (R (S IsZeroF s) (Fn x e)) = E (S IsZeroF s) (Fn x e)--Término bloqueado
eval1 (R (S IsZeroF s) (I i))    = if i == 0          
                                    then R s (B True) 
                                    else R s (B False)-------Caso significativo
eval1 (E s (Iszero e))           = E (S IsZeroF s) e---------Caso significativo
-----------------------------Test menor que---------------------------------------------
eval1 (R (S (LtFL e2) s) (B b))       = E (S (LtFR (B b)) s) e2--------Término bloqueado 
eval1 (R (S (LtFL e2) s) (V v))       = E (S (LtFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (LtFL e2) s) (Fn x e))    = E (S (LtFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (LtFR (I n)) s) (B b))    = R (S (LtFR (I n)) s) (B b)-----Término bloqueado
eval1 (R (S (LtFR (I n)) s) (V v))    = R (S (LtFR (I n)) s) (V v)-----Término bloqueado
eval1 (R (S (LtFR (I n)) s) (Fn x e)) = R (S (LtFR (I n)) s) (Fn x e)--Término bloqueado
eval1 (R (S (LtFL e2) s) (I n))       = E (S (LtFR (I n)) s) e2--------Caso significativo
eval1 (R (S (LtFR (I n)) s) (I m))    = if n-m < 0          
                                          then R s (B True) 
                                          else R s (B False)-----------Caso significativo
eval1 (E s (Lt e1 e2))                = E (S (LtFL e2) s) e1-----------Caso significativo
------------------------------Test mayor que--------------------------------------------
eval1 (R (S (GtFL e2) s) (B b))       = E (S (GtFR (B b)) s) e2--------Término bloqueado 
eval1 (R (S (GtFL e2) s) (V v))       = E (S (GtFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (GtFL e2) s) (Fn x e))    = E (S (GtFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (GtFR (I n)) s) (B b))    = R (S (GtFR (I n)) s) (B b)-----Término bloqueado
eval1 (R (S (GtFR (I n)) s) (V v))    = R (S (GtFR (I n)) s) (V v)-----Término bloqueado
eval1 (R (S (GtFR (I n)) s) (Fn x e)) = R (S (GtFR (I n)) s) (Fn x e)--Término bloqueado
eval1 (R (S (GtFL e2) s) (I n))       = E (S (GtFR (I n)) s) e2--------Caso significativo
eval1 (R (S (GtFR (I n)) s) (I m))    = if m-n < 0          
                                          then R s (B True) 
                                          else R s (B False)-----------Caso significativo
eval1 (E s (Gt e1 e2))                = E (S (GtFL e2) s) e1-----------Caso significativo
-----------------------------Test igualdad----------------------------------------------
eval1 (R (S (EqFL e2) s) (B b))       = E (S (EqFR (B b)) s) e2--------Término bloqueado 
eval1 (R (S (EqFL e2) s) (V v))       = E (S (EqFR (V v)) s) e2--------Término bloqueado
eval1 (R (S (EqFL e2) s) (Fn x e))    = E (S (EqFR (Fn x e)) s) e2-----Término bloqueado 
eval1 (R (S (EqFR (I n)) s) (B b))    = R (S (EqFR (I n)) s) (B b)-----Término bloqueado
eval1 (R (S (EqFR (I n)) s) (V v))    = R (S (EqFR (I n)) s) (V v)-----Término bloqueado
eval1 (R (S (EqFR (I n)) s) (Fn x e)) = R (S (EqFR (I n)) s) (Fn x e)--Término bloqueado
eval1 (R (S (EqFL e2) s) (I n))       = E (S (EqFR (I n)) s) e2--------Caso significativo
eval1 (R (S (EqFR (I n)) s) (I m))    = if n == m 
                                          then R s (B True) 
                                          else R s (B False)-----------Caso significativo
eval1 (E s (Eq e1 e2))                = E (S (EqFL e2) s) e1-----------Caso significativo
---------------------------Condicional if then else-----------------------------------
eval1 (R (S (IfF e1 e2) s) (I n))    = E (S (IfF e1 e2) s) (I n)-----Término bloqueado
eval1 (R (S (IfF e1 e2) s) (V v))    = E (S (IfF e1 e2) s) (V v)-----Término bloqueado
eval1 (R (S (IfF e1 e2) s) (Fn x e)) = E (S (IfF e1 e2) s) (Fn x e)--Término bloqueado
eval1 (R (S (IfF e1 e2) s) (B b))    = if b then E s e1 else E s e2--Caso significativo
eval1 (E s (If e e1 e2))             = E (S (IfF e1 e2) s) e --------Caso significativo
------------------------------Abstracción let------------------------------------------
eval1 (R (S (LetM x e2) s) (V v))     = E s (subst e2 (x, V v))------Caso significativo
eval1 (R (S (LetM x e2) s) (I n))     = E s (subst e2 (x, I n))------Caso significativo
eval1 (R (S (LetM x e2) s) (B b))     = E s (subst e2 (x, B b))------Caso significativo
eval1 (R (S (LetM x e2) s) (Fn y e3)) = E s (subst e2 (x, Fn y e3))--Caso significativo
eval1 (E s (Let x e1 e2))             = E (S (LetM x e2) s) e1-------Caso significativo
----------------------------Aplicación de función--------------------------------------------
eval1 (R (S (AppFL e2) s) (I i))            = E (S (AppFL e2) s) (I i)------Término bloqueado
eval1 (R (S (AppFL e2) s) (B b))            = E (S (AppFL e2) s) (B b)------Término bloqueado
eval1 (R (S (AppFL e2) s) (V v))            = E (S (AppFL e2) s) (V v)------Término bloqueado
eval1 (R (S (AppFL e2) s) (Fn x e3))        = E (S (AppFR (Fn x e3)) s) e2--Caso significativo
eval1 (R (S (AppFR (Fn x e3)) s) (I i))     = E s (subst e3 (x,I i))--------Caso significativo
eval1 (R (S (AppFR (Fn x e3)) s) (B b))     = E s (subst e3 (x,B b))--------Caso significativo
eval1 (R (S (AppFR (Fn x e3)) s) (V v))     = E s (subst e3 (x,V v))--------Caso significativo
eval1 (R (S (AppFR (Fn x e3)) s) (Fn y e4)) = E s (subst e3 (x,Fn y e4))----Caso significativo
eval1 (E s (App e1 e2))                     = E (S (AppFL e2) s) e1---------Caso significativo
--------------------------Manejo de error raise------------------------------
eval1 (R (S RaiseF s) (I n))    = P s (Raise (I n))---------Caso significativo
eval1 (R (S RaiseF s) (B b))    = P s (Raise (B b))---------Caso significativo
eval1 (R (S RaiseF s) (V v))    = P s (Raise (V v))---------Caso significativo
eval1 (R (S RaiseF s) (Fn x e)) = P s (Raise (Fn x e))------Caso significativo
eval1 (R s (Raise e))           = R (S RaiseF s) e----------Caso significativo
--------------------------Manejo de error handle------------------------------
eval1 (R (S (HandleF x e2) s) (I n))    = R s (I n)---------Caso significativo
eval1 (R (S (HandleF x e2) s) (B b))    = R s (B b)---------Caso significativo
eval1 (R (S (HandleF x e2) s) (V v))    = R s (V v)---------Caso significativo
eval1 (R (S (HandleF x e2) s) (Fn y e)) = R s (Fn y e)------Caso significativo
------------------------Interacción rise <-> handle----------------------------------------------------
eval1 (P (S (HandleF x e) p) (Raise (I n)))      = E p (subst e (x, I n))
eval1 (P (S (HandleF x e) p) (Raise (B b)))      = E p (subst e (x, B b))
eval1 (P (S (HandleF x e) p) (Raise (V v)))      = E p (subst e (x, V v))
eval1 (P (S (HandleF x e1) p) (Raise (Fn y e2))) = E p (subst e1 (x, Fn y e2))
eval1 (P (S m p) (Raise (I n)))    = if isHandleF m then P p (Raise (I n)) else P (S m p) (Raise (I n))       -- Caso significativo
eval1 (P (S m p) (Raise (B b)))    = if isHandleF m then P p (Raise (B b)) else P (S m p) (Raise (B b))       -- Caso significativo
eval1 (P (S m p) (Raise (V v)))    = if isHandleF m then P p (Raise (V v)) else P (S m p) (Raise (V v))       -- Caso significativo
eval1 (P (S m p) (Raise (Fn x e))) = if isHandleF m then P p (Raise (Fn x e)) else P (S m p) (Raise (Fn x e)) -- Caso significativo
eval1 state = state -- <-- Finalmente se define que cuando se llegue a un estado final o un estado bloqueado simplemente
                         --eval1 se comporta como la identidad, ¡esto será crucial para la definición de evals!

--Ejemplos:

--      eval1 (E Empty (Add (I 2) (I 3))) = E (S (AddFL (I 3)) Empty) (I 2) = E (S Add(-, I(3)) Empty) I(2)
--eval1 (E (S (AddFL (I 3)) Empty) (I 2)) = R (S (AddFL (I 3)) Empty) (I 2) = R (S Add(-, I(3)) Empty) I(2)

--Función que auxiliar que ayuda a probar la forma de cada iteración de la función eval1:

{-evaln :: Int -> State -> State
evaln n me = if n == 0
           then me
           else evaln (n-1) (eval1 me)-}

--3. (1.5 puntos) evals. Extiende esta función para que dado un estado, aplica la funcion de transicion
-- hasta llegar a un estado bloqueado, es decir, evals s = s’ si y sólo si s →∗_k s’ 
-- y s’ esta bloqueado o la pila esta vacia.

evals :: State -> State
evals e = if e == eval1 e then e else evals (eval1 e)

--Ejemplos :

--evals (E Empty (Let "x" (I 2) (Mul (Add (I 1) (V "x")) (V "x")))) = R Empty (I 6)
--evals (E Empty (Let "x" (B True) (If (V "x") (V "x") (B False)))) = R Empty (B True)

--4. (1.5 puntos) evale. Extiende esta función para que dada una expresión, devuelva la evaluación de un programa 
--tal que evale e = e’ syss e→∗_k e’, e’ es un valor devuelto a una pila vacia. En caso de que e’
--no sea un valor cuando la pila quede vacia o se llegue a un estado bloqueado deberá 
--mostrar un mensaje de error particular del operador que lo causó. 
{- NOTA: aunque en esta funcion no es visible la evaluacion
debe hacerse utilizando la maquina K. Hint: utiliza la funcion evals.-}

--Primero definimos la función auxiliar auxevale que extrae una expresión de un constructor State:

auxevale :: State -> Expr
auxevale (E s e) = e
auxevale (R s e) = e
auxevale (P s e) = e

--Luego definimos la función auxiliar verif que verifica que un estado esté correcto o devuelve un error:

verif :: State -> State
-----------------------------------Valores-------------------------------------
verif (R Empty (V v))          = error "Se devolverá una variable libre como resultado"
--Sucesor
verif (R (S SuccF s) (B b))    = error "[Succ] Espera un número entero"
verif (R (S SuccF s) (V v))    = error "[Succ] Espera un número entero"
verif (R (S SuccF s) (Fn x e)) = error "[Succ] Espera un número entero"
-----------------------------------Predecesor-----------------------------------
verif (R (S PredF s) (B b))    = error "[Pred] Espera un número entero"
verif (R (S PredF s) (V v))    = error "[Pred] Espera un número entero"
verif (R (S PredF s) (Fn x e)) = error "[Pred] Espera un número entero"
-----------------------------------Suma------------------------------------------
verif (R (S (AddFL e2) s) (B b))       = error "[Add] Espera dos números enteros"
verif (R (S (AddFL e2) s) (V v))       = error "[Add] Espera dos números enteros"
verif (R (S (AddFL e2) s) (Fn x e))    = error "[Add] Espera dos números enteros"
verif (R (S (AddFR (I n)) s) (B b))    = error "[Add] Espera dos números enteros"
verif (R (S (AddFR (I n)) s) (V v))    = error "[Add] Espera dos números enteros"
verif (R (S (AddFR (I n)) s) (Fn x e)) = error "[Add] Espera dos números enteros"
-----------------------------------Producto--------------------------------------
verif (R (S (MulFL e2) s) (B b))       = error "[Mul] Espera dos números enteros"
verif (R (S (MulFL e2) s) (V v))       = error "[Mul] Espera dos números enteros"
verif (R (S (MulFL e2) s) (Fn x e))    = error "[Mul] Espera dos números enteros"
verif (R (S (MulFR (I n)) s) (B b))    = error "[Mul] Espera dos números enteros"
verif (R (S (MulFR (I n)) s) (V v))    = error "[Mul] Espera dos números enteros"
verif (R (S (MulFR (I n)) s) (Fn x e)) = error "[Mul] Espera dos números enteros"
-----------------------------------Conjunción------------------------------
verif (R (S (AndFL e2) s) (I n))       = error "[And] Espera dos booleanos"
verif (R (S (AndFL e2) s) (V v))       = error "[And] Espera dos booleanos"
verif (R (S (AndFL e2) s) (Fn x e))    = error "[And] Espera dos booleanos"
verif (R (S (AndFR (B b)) s) (I n))    = error "[And] Espera dos booleanos"
verif (R (S (AndFR (B b)) s) (V v))    = error "[And] Espera dos booleanos"
verif (R (S (AndFR (B b)) s) (Fn x e)) = error "[And] Espera dos booleanos"
--------------------------------Disyunción-------------------------------
verif (R (S (OrFL e2) s) (I n))       = error "[Or] Espera dos booleanos"
verif (R (S (OrFL e2) s) (V v))       = error "[Or] Espera dos booleanos"
verif (R (S (OrFL e2) s) (Fn x e))    = error "[Or] Espera dos booleanos"
verif (R (S (OrFR (B b)) s) (I n))    = error "[Or] Espera dos booleanos"
verif (R (S (OrFR (B b)) s) (V v))    = error "[Or] Espera dos booleanos"
verif (R (S (OrFR (B b)) s) (Fn x e)) = error "[Or] Espera dos booleanos"
-----------------------------Negación---------------------------
verif (R (S NotF s) (I n))    = error "[Not] Espera un booleano"
verif (R (S NotF s) (V v))    = error "[Not] Espera un booleano"
verif (R (S NotF s) (Fn x e)) = error "[Not] Espera un booleano"
------------------------------Test iszero---------------------------------
verif (R (S IsZeroF s) (B b))    = error "[Iszero] Espera un número entero"
verif (R (S IsZeroF s) (V v))    = error "[Iszero] Espera un número entero"
verif (R (S IsZeroF s) (Fn x e)) = error "[Iszero] Espera un número entero"
------------------------------Test menor que-----------------------------------
verif (R (S (LtFL e2) s) (B b))       = error "[Lt] Espera dos números enteros"
verif (R (S (LtFL e2) s) (V v))       = error "[Lt] Espera dos números enteros"
verif (R (S (LtFL e2) s) (Fn x e))    = error "[Lt] Espera dos números enteros"
verif (R (S (LtFR (I n)) s) (B b))    = error "[Lt] Espera dos números enteros"
verif (R (S (LtFR (I n)) s) (V v))    = error "[Lt] Espera dos números enteros"
verif (R (S (LtFR (I n)) s) (Fn x e)) = error "[Lt] Espera dos números enteros"
--T------------------------------est mayor que---------------------------------
verif (R (S (GtFL e2) s) (B b))       = error "[Gt] Espera dos números enteros"
verif (R (S (GtFL e2) s) (V v))       = error "[Gt] Espera dos números enteros"
verif (R (S (GtFL e2) s) (Fn x e))    = error "[Gt] Espera dos números enteros"
verif (R (S (GtFR (I n)) s) (B b))    = error "[Gt] Espera dos números enteros"
verif (R (S (GtFR (I n)) s) (V v))    = error "[Gt] Espera dos números enteros"
verif (R (S (GtFR (I n)) s) (Fn x e)) = error "[Gt] Espera dos números enteros"
--------------------------------Test igualdad----------------------------------
verif (R (S (EqFL e2) s) (B b))       = error "[Eq] Espera dos números enteros"
verif (R (S (EqFL e2) s) (V v))       = error "[Gt] Espera dos números enteros"
verif (R (S (EqFL e2) s) (Fn x e))    = error "[Gt] Espera dos números enteros"
verif (R (S (EqFR (I n)) s) (B b))    = error "[Gt] Espera dos números enteros"
verif (R (S (EqFR (I n)) s) (V v))    = error "[Gt] Espera dos números enteros"
verif (R (S (EqFR (I n)) s) (Fn x e)) = error "[Gt] Espera dos números enteros"
-------------------------------Condicional if then else--------------------------------------
verif (R (S (IfF e1 e2) s) (I n))    = error "[If] Espera un booleano en su primer argumento"
verif (R (S (IfF e1 e2) s) (V v))    = error "[If] Espera un booleano en su primer argumento"
verif (R (S (IfF e1 e2) s) (Fn x e)) = error "[If] Espera un booleano en su primer argumento"
---------------------------------Aplicación de función---------------------------------------
verif (R (S (AppFL e2) s) (I i))  = error "[App] Espera una función Fn en su primer argumento"
verif (R (S (AppFL e2) s) (B b))  = error "[App] Espera una función Fn en su primer argumento"
verif (R (S (AppFL e2) s) (V v))  = error "[App] Espera una función Fn en su primer argumento"
------------Estados finales-------------
verif (R Empty (I n))    = R Empty (I n) 
verif (R Empty (B b))    = R Empty (B b) 
verif (R Empty (Fn x e)) = R Empty (Fn x e) 
------Filtro por si una pila termina no siendo vacía o cualquier otra anomalía-----
verif e = error "Algo salió mal D:"

--Así definimos la función evale como:

evale :: Expr -> Expr
evale e = auxevale (verif (evals (E Empty e)))

--Ejemplos:

--                  evale (Add (Mul (I 2) (I 6)) (B True)) *** Exception : [ Add ] Expects two Integer
-- evale (Or (Eq (Add (I 0) (I 0)) (I 0)) (Eq (I 1) (I 10))) = B True


--Manejo de excepciones -- <-- Solo falta esto


--5. (1 punto) Extiende las funciones frVars y subst para los nuevos constructores agregados. 

-- ✔


--6. (2 puntos) Extiende las funciones de eval1, evals y evale para incluir el manejo de excepciones con valor usando las expresiones que agregamos a la sintaxis.

-- ✔

--Ejemplo:

s :: State
s =  P (S (HandleF "x" (V "x")) Empty) (Raise (B False))

-- eval1 s = E Empty (B False)


---------
-- FIN --
---------
