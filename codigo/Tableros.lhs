\begin{code}
module Tableros where
import PTLP
import LPH
\end{code}

Definimos el tipo de dato \texttt{Nodo}

\begin{code}
data Nodo = Nd Indice [Termino] [Termino] [Form]
            deriving Show
\end{code}

Para finalmente, definir los tableros como una lista de nodos.

\begin{code}
type Tablero = [Nodo]
\end{code}
