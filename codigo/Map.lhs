\section{Librería Data.Map}

Introducimos la librería \texttt{Data.Map} cuya función es el trabajo
con diccionarios, permitiendo tanto la construcción de estos
diccionarios, como su modificación y acceso a la información.

\begin{code}
module Map where  
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}

Debido a que mucha de sus funciones tienen nombres coincidentes con
algunas ya definidas en \texttt{Prelude}, es necesario importarla
renombrándola de la siguiente manera: \texttt{import qualified Data.Map
as M}.  Eso implica que cuando llamemos a una función de esta librería,
tendremos que hacerlo poniendo \texttt{M.(función)}.

Los diccionarios son del tipo \texttt{Map k a} y la forma de construirlos es
mediante la función \texttt{(M.fromList)} seguida de una lista de pares.

\begin{code}
-- | Ejemplos:
-- >>> :type M.fromList
-- M.fromList :: Ord k => [(k, a)] -> Map k a
--
-- >>> M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- fromList [(0,"Luis"),(1,"Pablo"),(7,"Cristina"),(10,"Elisabeth")]
\end{code}

Una vez creado un diccionario, podemos acceder a la información
registrada en él y modificarla.

El operador \texttt{(M.!)} sirve para acceder a elementos del diccionario.

\begin{code}
-- | Ejemplos:
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> l M.! 1
-- "Pablo"
-- >>> l M.! 10
-- "Elisabeth"
\end{code}

La función \texttt{(M.size)} devuelve el tamaño del diccionario; es
decir, su número de elementos.

\begin{code}
-- | Ejemplos  
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> M.size l
-- 4
\end{code}

La función \texttt{(M.insert)} registra un elemento en el diccionario.

\begin{code}
-- | Ejemplos
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> M.insert 8 "Jesus" l
-- fromList [(0,"Luis"),(1,"Pablo"),(7,"Cristina"),(8,"Jesus"),(10,"Elisabeth")]
\end{code}

El operador \texttt{(M.\textbackslash\textbackslash)} realiza la
diferencia entre dos diccionarios.

\begin{code}
-- | Ejemplos
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> let l' = M.fromList [(1,"Pablo"),(7,"Cristina"),(0,"Luis")]  
-- >>> l M.\\ l
-- fromList []
-- >>> l M.\\ l'
-- fromList [(10,"Elisabeth")]
\end{code}

Para determinar si un elemento pertenece a un diccionario se emplea
\texttt{(M.member)}

\begin{code}
-- | Ejemplos
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> M.member 10 l
-- True
-- >>> M.member 3 l
-- False
\end{code}

Para localizar la definición de un elemento en un diccionario usamos la
función \texttt{(M.lookup)}

\begin{code}
-- | Ejemplos
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elisabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> M.lookup 10 l
-- Just "Elisabeth"
\end{code}

La función \texttt{(M.adjust)} actualiza una entrada de un diccionario
aplicando una función determinada.

\begin{code}
-- | Ejemplos
-- >>> let l = M.fromList [(1,"Pablo"),(10,"Elizabeth"),(7,"Cristina"),(0,"Luis")]
-- >>> M.adjust (++ " the Queen") 10 l
-- fromList [(0,"Luis"),(1,"Pablo"),(7,"Cristina"),(10,"Elizabeth the Queen")]
\end{code}
