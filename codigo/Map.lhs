\section{Librería Data.Map}

Introducimos la librería \texttt{Data.Map} cuya función es el trabajo             
con diccionarios, permitiendo tanto la construcción de estos diccionarios, 
como su modificación y acceso a la información.

\begin{code}
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}

Debido a que mucha de sus funciones tienen nombres coincidentes con 
algunas ya definidas en \texttt{Prelude}, es necesario importarla
renombrandola, de la siguiente manera: \texttt{import qualified Data.Map as M}.
Eso implica que cuando llamemos a una función de esta librería, tendremos que hacerlo
poniendo \texttt{M.(función)}.

Los diccionarios son del tipo \texttt{M k} y la forma de construirlos es
mediante la función \texttt{(M.fromList)} seguida de una lista de pares.
Por ejemplo

\begin{code}
-- >>> :type M.fromList
-- M.fromList :: Ord k => [(k, a)] -> Map k a
--
-- >>> M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- fromList [(0,"Luis"),(1,"Pablo"),(7,"Cristina"),(10,"Elisabeth")]
\end{code}

Una vez creada un diccionario, podemos acceder a la información registrada en él,
y modificarla.

El operador \texttt{(M.!)} sirve para acceder a elementos del diccionario.

\begin{code}
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> l M.! 1
-- "Pablo"
-- >>> l M.! 10
-- "Elisabeth"
\end{code}

La función \texttt{(M.size)} devuelve el tamaño del diccionario, es decir, su número
de elementos. 

\begin{code}
-- >>> M.size l
-- 4
\end{code}

La función \texttt{(M.insert)} registra un elemento en el diccionario.

\begin{code}
-- >>> M.insert 8 "Jesus" l
-- fromList [(0,"Luis"),(1,"Pablo"),(7,"Cristina"),(8,"Jesus"),(10,"Elisabeth")]
\end{code}

\comentario{sección en proceso}