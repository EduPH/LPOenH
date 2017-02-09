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
data Regla = Premisa 
            | IntroConj Form Form
            | ElimConj Form Form

data Instancia = I Form Regla
data Razonamiento = Rs [Instancia]

instance Show Regla where
    show Premisa = "Premisa"
    show (IntroConj f g) = "⋀i"++" ( " ++ show f ++" ) " ++ " ( " ++
                           show f++ " )" -- Se intentará que en vez de
                                         -- mostrar fórmulas completas,
                                         -- simplemente muestre la
                                         -- posición de las fórmulas que usa.

instance Show Instancia where
    show (I f r) = show f ++" . " ++ show r
\end{code}
