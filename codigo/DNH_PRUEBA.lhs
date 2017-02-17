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
data Reglas = Suponer Form
            | IntroConj Form Form
            | ElimConjI Form
            | ElimConjD Form 
            | ElimDobleNeg Form
            | IntroDobleNeg Form
            | ElimImpl Form Form
            | MT Form Form
            | IntroImpl Form Form
            | IntroDisyI Form Form
            | IntroDisyD Form Form
            | ElimDisy [Reglas] 
            | ElimNeg Form Form -- Falta elim. de lo falso
            | IntroNeg [Reglas]
            | IntroEquiv Form Form
            | ElimEquivI Form
            | ElimEquivD Form 
            
data Deduccion = D [Form] [Form] [Reglas]

verifica :: Deduccion -> Deduccion
verifica (D pr sp ((Suponer f):rs)) = verifica (D pr (f:sp) rs)
verifica (D pr sp ((IntroConj f g):rs)) 
    | elem f pr = verifica (D ((Disy [f,g]):pr) sp rs)
    | elem f sp = verifica (D pr ((Disy [f,g]):sp) rs) 
    | otherwise = error "No se puede aplicar la regla"
verifica (D pr sp ((ElimConjI f@(Conj fs)):rs)) 
    | elem f pr = verifica (D ((Conj (tail fs)):pr) sp rs)
    | elem f sp = verifica (D pr ((Conj (tail fs)):sp) rs)
    | otherwise = error "No se puede aplicar la regla"
verifica (D pr sp ((ElimConjD f@(Conj fs)):rs)) 
    | elem f pr = verifica (D ((Conj (init fs)):pr) sp rs)
    | elem f sp = verifica (D pr ((Conj (init fs)):sp) rs)
    | otherwise = error "No se puede aplicar la regla"
verifica (D pr sp ((ElimDobleNeg form@(Neg (Neg f))):rs))
    | elem form pr = verifica (D (f:pr) sp rs)
    | elem form sp = verifica (D pr (f:sp) rs)
    | otherwise = error "No se puede aplicar la regla"
verifica (D pr sp ((IntroDobleNeg f):rs)) 
    | elem f pr = verifica (D ((Neg (Neg f)):pr) sp rs)
    | elem f sp = verifica (D pr ((Neg (Neg f)):sp) rs)
    | otherwise = error "No se puede aplicar la regla"
verifica (D pr sp ((ElimImpl f1 form@(Impl f2 g)):rs))
    | elem form pr && elem f1 pr && f1==f2 = 
        verifica (D (g:pr) sp rs)
    | elem form sp && f1==f2 && elem f1 sp = 
        verifica (D pr (g:sp) rs)
    | otherwise = error "No se puede aplicar la regla"
verifica (D pr sp ((MT f g):rs)) = undefined
verifica (D pr sp ((IntroImpl f g):rs))
    | elem f sp && elem g sp = (D ((Impl f g):pr) (quita [f,g] sp) rs)
    | otherwise = error "No se puede aplicar la regla"

quita [] ys = ys
quita (x:xs) ys = quita xs (delete x ys)


-- EN PROCESO
instance Show Reglas where
    show (IntroConj f g) = "⋀i. "++ (show f)++ " , "++ (show g)
    show (ElimConjI f) = "⋀e. " ++ (show f)
instance Show Deduccion where
    show (D (p:pr) (s:sp) (r:rs)) = "Premisas  |  Supuestos  | Reglas"++
                                    "\n"++ (show p) ++ "    " ++ (show s)
                                          ++"   " ++ (show r) ++ "\n" ++
                                                  show (D pr sp rs)
\end{code} 
