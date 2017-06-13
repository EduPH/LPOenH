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


Definimos la función \texttt{(unifTerminos t1 t2)} que calcula la unificación
de los términos \texttt{t1} y \texttt{t2}.

\index{\texttt{unifTerminos}}
\begin{code}
unifTerminos :: Termino -> Termino -> Map Variable Termino
unifTerminos (Var x) (Var y)
    | x== y = M.fromList []
    | otherwise = M.fromList [(x,Var y)]
unifTerminos (Var x) t = 
    M.fromList [(x,t)| x `notElem` varEnTerm t]
unifTerminos t (Var y) =
    M.fromList [(y,t) | y `notElem` varEnTerm t]
unifTerminos (Ter f ts) (Ter g rs) =
    if f==g then unifListas ts rs M.empty  else (M.empty)
\end{code}

Finalmente, se generaliza para listas de términos mediante la función
\texttt{(unifListas ts rs d)}

\index{\texttt{unifListas}}
\begin{code}
unifListas :: [Termino] -> [Termino] -> Map Variable Termino -> Map
              Variable Termino
unifListas [] [] d = M.empty
unifListas [] _ d = d 
unifListas _ [] d = d
unifListas (t:ts) (r:rs) d = unifListas (sustTerms ts d') (sustTerms rs d') d'
    where
      d' = M.union (unifTerminos t r) d
\end{code}


