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
      V s -> "V("++ s ++")"
      I n -> "I("++ show n ++")"
      B b -> "B("++ show b ++")"
      Fn i e -> "Fn("++i++"."++show e++")"
      Succ ex -> "Succ("++ show ex ++")"
      Pred ex -> "Pred("++ show ex ++")"
      Add ex ex' -> "Add("++ show ex ++", "++ show ex'++")"
      Mul ex ex' -> "Mul("++ show ex ++", "++ show ex'++")"
      Not ex -> "Not("++ show ex ++")"
      Iszero ex -> "IsZero("++ show ex ++")"
      And ex ex' -> "And("++ show ex ++", "++ show ex'++")"
      Or ex ex' -> "Or("++ show ex ++", "++ show ex'++")"
      Lt ex ex' -> "Lt("++ show ex ++", "++ show ex'++")"
      Gt ex ex' -> "GT("++ show ex ++", "++ show ex'++")"
      Eq ex ex' -> "Eq("++ show ex ++", "++ show ex'++")"
      If ex ex' ex2 -> "If("++ show ex ++", "++ show ex'++", "++ show ex2++")"
      Let i ex ex' -> "Let("++ show ex ++", "++ i++"."++ show ex'++")"
      L n -> "L(" ++ show n ++ ")"
      Alloc ex -> "Alloc("++ show ex ++")"
      Dref ex -> "Dref("++ show ex ++")"
      Assig ex ex' -> "Assig("++ show ex ++", "++ show ex'++")"
      Void -> "Void()"
      Seq ex ex' -> "Seq("++ show ex ++", "++ show ex'++")"
      While ex ex' -> "While("++ show ex ++", "++ show ex'++")"
      App ex ex' -> "App("++ show ex ++", "++ show ex'++")"
      Raise ex -> "Raise("++ show ex ++")"
      Handle ex s ex' -> "Handle("++show ex++", "++s++", "++show ex'++")"

{-- Show para los Frame -}
instance Show Frame where
    show e = case e of
        (AddFL a) -> "Add(-, "++show a++")"
        (AddFR a) -> "Add("++show a++", -)"
        (MulFL a) -> "Mul(-, "++show a++")"
        (MulFR a) -> "Mul("++show a++", -)"
        SuccF -> "Succ(-)"
        PredF -> "Pred(-)"
        (AndFL a) -> "And(-, "++show a++")"
        (AndFR a) -> "And("++show a++", -)"
        (OrFL a) -> "Or(-, "++show a++")"
        (OrFR a) -> "Or("++show a++", -)"
        NotF -> "Not(-)"
        IsZeroF -> "IsZero(-)"
        (LtFL a) -> "Lt(-, "++show a++")"
        (GtFL a) -> "Gt("++show a++", -)"
        (LtFR a) -> "Lt(-, "++show a++")"
        (GtFR a) -> "Gt("++show a++", -)"
        (EqFL a) -> "Eq(-, "++show a++")"
        (EqFR a) -> "Eq("++show a++", -)"
        (IfF a b) -> "If(-, "++show a++", "++show b++")"
        (LetM a b) -> "LetM(-, "++show a++", "++show b++")"
        (AppFL a) -> "Eq(-, "++show a++")"
        (AppFR a) -> "Eq("++show a++", -)"
        RaiseF -> "Raise(-)"
        (HandleF a b) -> "HandleF(-, "++a++"."++show b++")"


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
subst (Handle e1 x e2) (i,e)
  | x == i || elem x (frVars e) = Handle e1 x e2
  | x `elem` frVars e = error "Variables en comun ligadas. Encuentra una alfa equivalencia"
  | otherwise = Handle (subst e1 (i,e)) x (subst e2 (i,e))


-- Defincion de pila de marcos
data Stack = Empty | S Frame Stack


--Definicion de los estados
data State = E Stack Expr
            | R Stack Expr
            | P Stack Expr


-- Re implementa esta función para que dado un estado, devuelva un paso de transicion,
-- es decir, eval1 s = s’ si y sólo si s →_k s’
eval1 :: State -> State
eval1 (E s (I n)) = R s (I n) -- C quedan igual
eval1 (E s (B b)) = R s (B b) -- s para seguir manteniendo el estado de la pila
eval1 (E s (V v)) = R s (V v)
-------- Creo que sería mejor si primero hacemos las E's
--eval1 (E s (Fn i e)) = E (S Fn) ?? a chinga, no falta un marco para fn?
eval1 (E s (Succ e)) = E (S (SuccF ) s) e -- NO recibe argumento
eval1 (E s (Pred e)) = E (S (PredF ) s) e
eval1 (E s (Add e1 e2)) = E (S (AddFL e2) s) e1 --Ponemos la expr de la izq en la pila
eval1 (E s (Mul e1 e2)) = E (S (MulFL e2) s) e1
eval1 (E s (Not e)) = E (S (NotF ) s) e
eval1 (E s (Iszero e)) = E (S (IsZeroF ) s) e
eval1 (E s (And e1 e2)) = E (S (AndFL e2) s) e1
eval1 (E s (Or e1 e2)) = E (S (OrFL e2) s) e1
eval1 (E s (Lt e1 e2)) = E (S (LtFL e2) s) e1
eval1 (E s (Gt e1 e2)) = E (S (GtFL e2) s) e1
eval1 (E s (Eq e1 e2)) = E (S (EqFL e2) s) e1
eval1 (E s (If b e2 e3)) = E (S (IfF e2 e3) s) b
eval1 (E s (Let i e1 e2)) = E (S (LetM i e2) s) e1
eval1 (E s (App e1 e2)) = E (S (AppFL e2) s) e1

--Ahora las R con su respectiva variable xd





--Idea
--eval1 (E s (Add e1 e2)) = E (S (AddFL e2) s) e1 --Ponemos la expr de la izq en la pila
--eval1 (R (S (AddFL e) s) (I n)) = E (S (AddFR (I n)) s) e --Metemos el otro lado
--eval1 (R (S (AddFR (I n)) s) (I m)) = R s (I (n+m)) -- finalmente evaluamos



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


