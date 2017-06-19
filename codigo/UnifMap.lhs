\section{Unificación con la librería Data.Map}

En esta sección queremos redefinir la unificación (\ref{sec:unificacion})
empleando las implementaciones de la librería \texttt{Data.Map} y lo ya
definido sobre sustitución.

\begin{code}
module UnifMap where
import LPH
import PTLP
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
unifTerminos :: Termino -> Termino -> [Map Variable Termino]
unifTerminos (Var x) (Var y)
  | x == y    = [M.fromList []]
  | otherwise = [M.fromList [(x,Var y)]]
unifTerminos (Var x) t = 
  [M.fromList [(x,t)]| x `notElem` varEnTerm t]
unifTerminos t (Var y) =
  [M.fromList [(y,t)] | y `notElem` varEnTerm t]
unifTerminos (Ter f ts) (Ter g rs) =
  [u | f == g, u <- unifListas ts rs]
\end{code}

\comentario{Añadir los ejemplos de unificación de términos del curso de
  Lógica (tema 12)} 

Finalmente, se generaliza para listas de términos mediante la función
\texttt{(unifListas ts rs d)}

\index{\texttt{unifListas}}
\begin{code}
unifListas :: [Termino] -> [Termino] -> [Map Variable Termino]
unifListas [] [] = [M.empty]
unifListas [] _  = []
unifListas _ []  = []
unifListas (t:ts) (r:rs) =
  [composicionMap u1 u2
  | u1 <- unifTerminos t r
  , u2 <- unifListas (sustTerms ts u1) (sustTerms rs u1)]   
\end{code}

Veamos algunos ejemplos:

\begin{code}
-- | Ejemplos
-- >>> unifListas [tx] [ty]
-- [fromList [(x,y)]]
-- >>> unifListas [tx] [tx]
-- [fromList []]
-- >>> unifListas [tx,tx] [a,b]
-- []
-- >>> unifListas [tx,b] [a,ty]
-- [fromList [(x,a),(y,b)]]
-- >>> unifListas [ty, tz] [tx, Ter "f" [ty]]
-- [fromList [(z,f[x])]]
-- >>> unifListas [ty, ty] [tx, Ter "f" [ty]]
-- []
\end{code}


