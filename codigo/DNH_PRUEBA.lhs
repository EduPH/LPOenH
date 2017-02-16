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
            | ElimConjI Form Form
            | ElimConjD Form Form
            | ElimDobleNeg Form
            | IntroDobleNeg Form
            | ElimImpl Form Form
            | MT Form Form
            | IntroImpl [Reglas]
            | IntroDisyI Form Form
            | IntroDisyD Form Form
            | ElimDisy [Reglas] 
            | ElimNeg Form Form -- Falta elim. de lo falso
            | IntroNeg [Reglas]
            | IntroEquiv Form Form
            | ElimEquivI Form
            | ElimEquivD Form 
            
data Deduccion = D [Form] [Form] [Reglas]

verifica :: Deduccion -> Bool
verifica (D pr sp ((Suponer f):rs)) = verifica (D pr (f:sp) rs)
verifica (D pr sp ((IntroConj f g):rs)) 
    | elem f pr && elem g pr = verifica (D ((Disy [f,g]):pr) sp rs)
                               -- Hay que determinar si f o g son
                               -- supuestos o cosas deducidas
\end{code}
