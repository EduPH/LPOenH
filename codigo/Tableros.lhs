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

Necesitamos poder reconocer las dobles negaciones

\index{\texttt{dobleNeg}}
\begin{code}
dobleNeg (Neg (Neg f)) = True
dobleNeg _             = False
\end{code}

Una función auxiliar de conversión de literales a términos.

\index{\texttt{literalATer}}
\begin{code}
literalATer :: Form -> Term
literalATer (Atom n ts)       = Ter n ts
literalATer (Neg (Atom n ts)) = Ter n ts
\end{code}
