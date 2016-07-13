\section{Sustitución}

\begin{code}
module PTLP where
import LPH
import Test.QuickCheck -- Para ejemplos
import Generadores     -- Para ejemplos
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

\begin{Def}
  Una variable $x$ está ligada en una fórmula cuando tiene una aparición
  de la forma $\forall x$ o $\exists x$.
\end{Def}

\begin{Def}
  Una sustitución es una aplicación $S: Variable \rightarrow Termino$.
\end{Def}

En la lógica de primer orden, aquellas variables que están ligadas,
a la hora de emplear el método de tableros, es necesario sustituirlas
por términos. Para ello definimos un nuevo tipo de dato

\begin{code}
type Sust = [(Variable, Termino)]
\end{code}

Este nuevo tipo de dato es una asociación de la variable con el término
mediante pares. Denotamos el elemento identidad de la sustitución como 
\texttt{identidad}

\index{\texttt{identidad}}
\begin{code}
identidad :: Sust
identidad = []
\end{code}

Para que la sustitución sea correcta, debe ser lo que denominaremos como
apropiada. Para ello eliminamos aquellas sustituciones que dejan la variable
igual.

\begin{code}
hacerApropiada :: Sust -> Sust
hacerApropiada xs = [x | x <- xs, Var (fst x) /= snd x]
\end{code}

Como la sustitución es una aplicación, podemos distinguir \texttt{dominio} y
\texttt{recorrido}.

\index{\texttt{dominio}}
\index{\texttt{recorrido}}
\begin{code}
dominio :: Sust -> [Variable]
dominio = map fst

recorrido :: Sust -> [Termino]
recorrido = map snd
\end{code}

Posteriormente, se define una función que hace la sustitución de una
variable concreta. La denotamos \texttt{(sustituyeVar sust var)}
\begin{code}
sustituyeVar :: Sust -> Variable -> Termino
sustituyeVar [] y                      = Var y
sustituyeVar ((x,x'):xs) y | x == y    = x'
                           | otherwise = sustituyeVar xs y
\end{code}

Ahora aplicando una recursión entre funciones, podemos hacer sustituciones
basándonos en los términos, mediante las funciones \texttt{(susTerm xs t)} y
\texttt{(susTerms sust ts)}.

\index{\texttt{susTerm}}
\index{\texttt{susTerms}}
\begin{code}
susTerm :: Sust -> Termino -> Termino
susTerm s (Var y)    = sustituyeVar s y
susTerm s (Ter f ts) = Ter f (susTerms s ts)

susTerms :: Sust -> [Termino] -> [Termino]
susTerms = map . susTerm
\end{code}

Finalmente, esta construcción nos sirve para generalizar a cualquier
fórmula. Con este fin definimos \texttt{(sustitucionForm s f)}, donde
\texttt{s} representa la susticución y \texttt{f} la fórmula.

\index{\texttt{sustitucionForm}}
\begin{code}
sustitucionForm :: Sust -> Form -> Form
sustitucionForm s (Atom r ts) =
  Atom r (susTerms s ts)
sustitucionForm s (Neg f) =
  Neg (sustitucionForm s f)
sustitucionForm s (Impl f1 f2) = 
  Impl (sustitucionForm s f1) (sustitucionForm s f2)
sustitucionForm s (Equiv f1 f2) =
  Equiv (sustitucionForm s f1) (sustitucionForm s f2)
sustitucionForm s (Conj fs) =
  Conj (sustitucionForms s fs)
sustitucionForm s (Disy fs) =
  Disy (sustitucionForms s fs)
sustitucionForm s (PTodo v f) =
  PTodo v (sustitucionForm s' f)
  where s' = [x | x <- s, fst x /= v]
sustitucionForm s (Ex v f) =
  Ex v (sustitucionForm s' f)
  where s' = [x | x <- s, fst x /= v]
\end{code}

Se puede generalizar a una lista de fórmulas mediante la funcion
\texttt{(sustitucionForms s fs)}. La hemos necesitado en la definición de la
función anterior, pues las conjunciones y disyunciones trabajan con listas de
fórmulas.

\begin{code}
sustitucionForms :: Sust -> [Form] -> [Form]
sustitucionForms s = map (sustitucionForm s)
\end{code}

Nos podemos preguntar si la sustitución conmuta con la composición. Para ello
definimos la función \texttt{(composicion s1 s2)}

\index{\texttt{composicion}}
\begin{code}
composicion :: Sust -> Sust -> Sust
composicion s1 s2 = 
    hacerApropiada [(y,susTerm s1 y') | (y,y') <- s2 ] ++
    [x | x <- s1, fst x `notElem` dominio s2]
\end{code}

\comentario{Añadir ejemplos de composición}

\begin{code}
composicionConmutativa :: Sust -> Sust -> Bool
composicionConmutativa s1 s2 = 
  composicion s1 s2 == composicion s2 s1
\end{code} 
 
\section{Unificación}

Y comprobando con QuickCheck, no lo es

\begin{sesion}
ghci> quickCheck composicionConmutativa
*** Failed! Falsifiable (after 3 tests and 1 shrink): 
[(i3,n)]
[(c19,i)]
\end{sesion}

\begin{description}
\item Nota: Las comprobaciones con QuickCheck emplean código del módulo
  \texttt{Generadores}.
\end{description}

\begin{Def}
  Un unificador de dos términos $t_1$ y $t_2$ es una sustitución $S$ tal que
  $S(t_1) = S(t_2)$.
\end{Def}

\begin{code}
unificadoresTerminos :: Termino -> Termino -> [Sust]
unificadoresTerminos (Var x) (Var y)   
  | x == y    = [identidad]
  | otherwise = [[(x,Var y)]]
unificadoresTerminos (Var x) t =
  [[(x,t)] | x `notElem` varEnTerm t]
unificadoresTerminos t (Var y) =
  [[(y,t)] | y `notElem` varEnTerm t]
unificadoresTerminos (Ter f ts) (Ter g rs) = 
  [u | f == g, u <- unificaTermLista ts rs]
\end{code}

El valor de \texttt{(unificadoresLista ts rs)} es un unificador de las listas
de términos \texttt{ts} y \texttt{rs}; es decir, una sustitución \texttt{s} tal
que si \texttt{ts = [t1,...,tn]} y \texttt{rs = [r1,...,rn]} entonces
\texttt{s(t1) = s(r1)}, \dots, \texttt{s(tn) = s(rn)}.

\begin{code}
unificadoresLista :: [Termino] -> [Termino] -> [Sust]
unificadoresLista [] [] = [identidad]
unificadoresLista [] _  = []
unificadoresLista _ []  = []
unificadoresLista (t:ts) (r:rs) = 
    [composicion u1 u2
    | u1 <- unificadoresTerminos t r
    , u2 <- unificadoresLista (susTerms u1 ts) (susTerms u1 rs) ]   
\end{code}

\comentario{Añadir ejemplos de unificadoresLista}

\section{Skolem}

Para una unificación eficiente 
