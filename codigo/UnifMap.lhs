\section{Unificación con la librería Data.Map}

En esta sección queremos redefinir la unificación
(\ref{sec:unificacion}) empleando las implementaciones
de la librería \texttt{Data.Map}, y lo ya definido sobre
sustitución.

\begin{code}
module UnifMap where
import LPH
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import SustMap
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}


\begin{code}
unifTerminos :: Termino -> Termino -> Map Variable Termino
unifTerminos (Var x) (Var y)
    | x== y = M.fromList []
    | otherwise = M.fromList [(x,Var y)]
\end{code}
