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
literalATer :: Form -> Termino
literalATer (Atom n ts)  = Ter n ts
literalATer (Neg (Atom n ts)) = Ter n ts
\end{code}

Definimos la función \texttt{(componentes f)} que determina
los componentes de una fórmula \texttt{f}.

\index{\texttt{componentes}}
\begin{code}
componentes :: Form -> [Form]
componentes (Conj fs) = fs
componentes (Disy fs) = fs
componentes (Neg (Conj fs)) = [Neg f | f <- fs]
componentes (Neg (Disy fs)) = [Neg f | f <- fs]
componentes (Neg (Neg f)) = [f]
componentes (PTodo x f) = [f]
componentes (Neg (Ex x f)) = [Neg f]
\end{code}

Definimos la función \texttt{(varLigada f)} que devuelve la
variable ligada de la fórmula \texttt{f}

\index{\texttt{varLigada}}
\begin{code}
varLigada :: Form -> Variable
varLigada (PTodo x f)    = x
varLigada (Neg (Ex x f)) = x
\end{code}

Definimos la función \texttt{(descomponer f)} que determina
los cuantificadores universales de \texttt{f}.

\index{\texttt{descomponer}}
\begin{code}
descomponer :: Form -> ([Variable],Form)
descomponer f = descomp [] f where
    descomp xs f = if gamma f then descomp (xs ++ [x]) f' else (xs,f)
        where x = varLigada f
              [f'] = componentes f
\end{code}

Por ejemplo

\begin{sesion}
ghci> descomponer formula_2
([x,y],(R[x,y]⟹∃z (R[x,z]⋀[R[z,y]])))
ghci> descomponer formula_3
([],(R[x,y]⟹∃z (R[x,z]⋀[R[z,y]])))
ghci> descomponer formula_4
([],∃x R[cero,x])
\end{sesion}
