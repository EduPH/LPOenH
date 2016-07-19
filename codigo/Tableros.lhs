\begin{code}
module Tableros where
import PTLP
import LPH
import Debug.Trace     -- Para ejemplos
\end{code}

Hemos importado la librería \texttt{Debug.Trace} porque emplearemos la función
\texttt{trace}. Esta función tiene como argumentos una cadena de caracteres,
una función, y un valor sobre el que se aplica la función. Por ejemplo

\begin{sesion}
ghci> trace ("aplicando even a x = " ++ show 3) (even 3)
aplicando even a x = 3
False
\end{sesion}

A lo largo de esta sección trabajaremos con fórmulas
en su forma de Skolem.
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


Definimos \texttt{(ramificacion nodo)} que ramifica un nodo.

\intex{\texttt{ramificacion}}
\begin{code}
ramificacion :: Nodo -> Tablero
ramificacion (Nd i pos neg []) = [Nd i pos neg []]
ramificacion (Nd i pos neg (f:fs)) 
    | atomo f = if elem (literalATer f) neg then []
                else [Nd i ((literalATer f):pos) neg fs]
    | negAtomo f = if elem (literalATer f) pos then []
                   else [Nd i pos ((literalATer f):neg) fs]
    | dobleNeg f = [Nd i pos neg ((componentes f) ++ fs)]
    | alfa f  = [Nd i pos neg ((componentes f) ++ fs)]
    | beta f  = [(Nd (i++[n]) pos neg (f':fs)) |
                (f',n) <- zip (componentes f) [0..]]
    | gamma f = [Nd i pos neg (f':(fs++[f]))]
    where
      (xs,g) = descomponer f
      b      = [((Variable nombre j), 
                 Var (Variable nombre i)) |
                (Variable nombre j) <- xs]
      f'     = sustitucionForm b g
\end{code}

Debido a que pueden darse la infinitud de un árbol por las fórmulas
gamma, definimos otra función \texttt{(ramificacionP k nodo)} que ramifica
un nodo teniendo en cuenta la profundidad.

\index{\texttt{ramificacionP}}
\begin{code}
ramificacionP :: Int -> Nodo -> (Int,Tablero)
ramificacionP k nodo@(Nd i pos neg []) = (k,[nodo])
ramificacionP k (Nd i pos neg (f:fs))
    | atomo    f = if elem (literalATer f) neg then (k,[])
                   else (k,[Nd i ((literalATer f):pos) neg fs])
    | negAtomo f = if elem (literalATer f) neg then (k,[]) 
                   else (k,[Nd i pos ((literalATer f):neg) fs])
    | dobleNeg f = (k,[Nd i pos neg ((componentes f) ++ fs)])
    | alfa     f = (k,[Nd i pos neg ((componentes f) ++ fs)])
    | beta     f = (k,[(Nd (i++[n]) pos neg (f':fs)) |
                       (f',n) <- zip (componentes f) [0..] ])
    | gamma    f = (k-1, [Nd i pos neg (f':(fs++[f]))])
    where 
      (xs,g) = descomponer f
      b      = [((Variable nombre j), Var (Variable nombre i)) |
                (Variable nombre j) <- xs]
      f'     = sustitucionForm b g
\end{code}

\begin{Def}
  Un nodo está completamente expandido si no se puede seguir ramificando
\end{Def}

Se define en Haskell

\index{\texttt{nodoExpandido}}
\begin{code}
nodoExpandido :: Nodo -> Bool
nodoExpandido (Nd i pos neg []) = True
nodoExpandido _                 = False
\end{code}

Definimos la función \texttt{(expandeTablero k tab)} que desarrolla 
un tablero a una profundidad \texttt{k}.

\begin{code}
expandeTablero :: Int -> Tablero -> Tablero
expandeTablero 0 tab = tab
expandeTablero _ []  = []
expandeTablero k (nodo:nodos) 
    | nodoExpandido nodo = nodo:(expandeTablero k nodos)
    | otherwise =  if k == k then expandeTablero k (nuevoNodo ++ nodos)
                   else expandeTablero (k-1) (nodos ++ nuevoNodo)
    where (k,nuevoNodo) = ramificacionP k nodo
\end{code}
