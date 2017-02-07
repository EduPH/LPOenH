\begin{code}
module DNHPrueba where
import LPH
import Data.List
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}

Propuesta para la construcción de la deducción natural. La idea es          
construir los tipos de datos necesarios para la representación de la          
deducción natural a partir de un tipo de dato para las reglas
\begin{code}
data Reglas = IntroConj Form Form
            | ElimConj Form Form
\end{code}
