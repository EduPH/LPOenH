\begin{code}
module DNHPrueba where
import LPH
import Data.List
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}

Propuesta para la construcción de la deducción natural. La idea es          
construir los tipos de datos necesarios para la representación de la          
deducción natural a partir de un tipo de dato para las reglas. Y otro
tipo de dato llamado Deducción formado por una lista de premisas y cosas ya deducidas, y otra lista de supuestos, además de una lista de reglas. 

\begin{code}
data Reglas = Suponer Form --
            | IntroConj Form Form --
            | ElimConjI Form  --
            | ElimConjD Form  --
            | ElimDobleNeg Form --
            | IntroDobleNeg Form --
            | ElimImpl Form Form --
            | MT Form Form
            | IntroImpl Form Form --
            | IntroDisyI Form Form --
            | IntroDisyD Form Form --
            | ElimDisy Form --
            | ElimNeg Form Form -- Falta elim. de lo falso
            | IntroNeg Form --
            | ElimContrad Form 
            | IntroEquiv Form Form
            | ElimEquivI Form
            | ElimEquivD Form 
            
data Deduccion = D [Form] [Form] [Reglas]

contradiccion :: Form
contradiccion = Atom "⊥" []

verifica :: Deduccion -> Bool

verifica (D pr [] []) = True
verifica (D pr sp ((Suponer f):rs)) = verifica (D pr (f:sp) rs)

verifica (D pr sp ((IntroConj f g):rs)) 
    | elem f (pr++sp) = verifica (D ((Disy [f,g]):pr) sp rs) 
    | otherwise = error "No se puede aplicar IntroConj"

verifica (D pr sp ((ElimConjD f@(Conj fs)):rs)) 
    | elem f pr || elem f sp = verifica (D ((Conj (init fs)):pr) sp rs)
    | otherwise = error "No se puede aplicar ElimConjD"

verifica (D pr sp ((ElimConjI f@(Conj fs)):rs)) 
    | elem f pr || elem f sp = verifica (D ((Conj (tail fs)):pr) sp rs)
    | otherwise = error "No se puede aplicar ElimConjI"

verifica (D pr sp ((ElimDisy (Disy [f,g])):rs)) 
    | elem f sp && elem g sp && elem (Conj [f,g]) pr = 
        verifica (D pr (quita [f,g] sp) rs)
    | otherwise = error "No se puede aplicar ElimDisy"

verifica (D pr sp ((IntroDisyD f g):rs)) 
    | elem f (pr++sp) = verifica (D ((Disy [f,g]):pr) sp rs)
    | otherwise = error "No se puede aplicar IntroDisyD"

verifica (D pr sp ((IntroDisyI f g):rs)) 
    | elem g (pr++sp) = verifica (D ((Disy [f,g]):pr) sp rs)
    | otherwise = error "No se puede aplicar IntroDisyI"

verifica (D pr sp ((ElimDobleNeg form@(Neg (Neg f))):rs))
    | elem form pr || elem form sp = verifica (D (f:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimDobleNeg"

verifica (D pr sp ((IntroDobleNeg f):rs)) 
    | elem f pr || elem f sp = verifica (D ((Neg (Neg f)):pr) sp rs)
    | otherwise = error "No se puede aplicar la IntroDobleNeg"

verifica (D pr sp ((ElimImpl f1 form@(Impl f2 g)):rs))
    | c = verifica (D (g:pr) sp rs)
    | otherwise = error "No se puede aplicar la ElimImpl"
    where 
      c = pertenece [f1,f2] (pr++sp) && f1 == f2

verifica (D pr sp ((MT f g):rs)) = undefined

verifica (D pr sp ((IntroImpl f g):rs))
    | elem f sp && elem g pr = 
        verifica (D ((Impl f g):pr) (delete f sp) rs)
    | otherwise = error "No se puede aplicar IntroImpl"

verifica (D pr sp ((IntroNeg f):rs)) 
    | elem f sp && elem contradiccion pr = 
        verifica (D ((Neg f):pr) sp rs)
    | otherwise = error "No se puede aplicar IntroNeg"

verifica (D pr sp ((ElimNeg f):rs))
    | elem f (pr++sp) && elem (Neg f) (pr++sp) = 
        verifica (D (contradiccion:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimNeg"

verifica (D pr sp ((ElimContrad f):rs))
    | elem contradiccion (pr++sp) = verifica (D (f:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimContrad"
\end{code} 

Funciones auxiliares (quita xs ys) y (pertenece xs ys)

\begin{code}
quita :: [Form] -> [Form] -> [Form]
quita [] ys = ys
quita (x:xs) ys = quita xs (delete x ys)

pertenece :: [Form] -> [Form] -> Bool
pertenece xs ys = all (`elem` ys) xs
\end{code}
