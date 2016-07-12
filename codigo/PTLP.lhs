\section{Sustitución}

\begin{Def}
Una sustitución es una aplicación $S: Variable \rightarrow Termino $.
\end{Def}

\begin{code}
module PTLP where
import Data.List
import LPH
import PFH
import Test.QuickCheck
\end{code}

Hemos importado la librería \texttt{Debug.Trace} porque emplearemos
la función \texttt{trace}. Esta función tiene como argumentos
una cadena de caracteres, una función, y un valor sobre el que se aplica
la función. Por ejemplo

\begin{sesion}
ghci> trace ("aplicando even a x = " ++ show 3) (even 3)
aplicando even a x = 3
False
\end{sesion}

\begin{Def}
  Una variable $x$ es ligada en una fórmula cuando tiene una aparición
  de la forma $\forall x$ o $\exists x$.
\end{Def}

En la lógica de primer orden, aquellas variables que están ligadas,
a la hora de emplear el método de tableros, es necesario sustituirlas
por términos. Para ello definimos un nuevo tipo de dato

\begin{code}
type Sust = [(Variable, Termino)]
\end{code}

Este nuevo tipo de dato es una asociación de la variable con el término
mediante 2-uplas. Denotamos el elemento identidad de la sustitución como 
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

Posteriormente, se define una función que haga una sustitución de una
variable concreta. La denotamos \texttt{(sustituyeVar sust var)}
\begin{code}
sustituyeVar :: Sust -> Variable -> Termino
sustituyeVar [] y                      = Var y
sustituyeVar ((x,x'):xs) y | x==y      = x'
                           | otherwise = sustituyeVar xs y
\end{code}

Ahora aplicando una recursión entre funciones, podemos hacer sustituciones
basándonos en los términos, mediante las funciones \texttt{(susTerm xs t)} y
\texttt{(susTerms sust ts)}
\index{\texttt{susTerm}}
\index{\texttt{susTerms}}
\begin{code}
susTerm :: Sust -> Termino -> Termino
susTerm xs (Var y) = sustituyeVar xs y
susTerm xs (Ter n ts) = Ter n (susTerms xs ts)

susTerms :: Sust -> [Termino] -> [Termino]
susTerms = map . susTerm
\end{code}

Finalmente, esta construcción nos sirve para generalizar a
cualquier fórmula. Con este fin definimos \texttt{(sustitucionForm xs f)},
donde \texttt{xs} representa la lista de pares que definen las sustituciones,
y \texttt{f} la fórmula.

\index{\texttt{sustitucionForm}}
\begin{code}
sustitucionForm :: Sust -> Form -> Form
sustitucionForm xs (Atom a ts)  = Atom a (susTerms xs ts)
sustitucionForm xs (Neg f) = Neg (sustitucionForm xs f)
sustitucionForm xs (Impl f1 f2)  = 
    Impl (sustitucionForm xs f1) (sustitucionForm xs f2)
sustitucionForm xs (Equiv f1 f2) =
    Equiv (sustitucionForm xs f1) (sustitucionForm xs f2)
sustitucionForm xs (Conj fs)     = Conj (sustitucionForms xs fs)
sustitucionForm xs (Disy fs)     = Disy (sustitucionForms xs fs)
sustitucionForm xs (PTodo v f)   = PTodo v (sustitucionForm xs' f)
    where
      xs' = [ x | x <- xs, fst x /= v]
sustitucionForm xs (Ex v f)      = Ex v (sustitucionForm xs' f)
    where
      xs' = [ x | x <- xs, fst x /= v]
\end{code}

Se puede generalizar a una lista de fórmulas mediante la funcion
\texttt{sustitucionForms xs fs}. La hemos necesitado en la definición
de la función anterior, pues las conjunciones y disyunciones trabajan
con listas de fórmulas.

\begin{code}
sustitucionForms :: Sust -> [Form] -> [Form]
sustitucionForms xs fs = map (sustitucionForm xs) fs
\end{code}

Nos podemos preguntar si la sustitución conmuta con la composición.
Para ello definimos la función \texttt{(composicion xs ys)}

\index{\texttt{composicion}}
\begin{code}
composicion :: Sust -> Sust -> Sust
composicion xs ys = 
    (hacerApropiada [ (y,(susTerm xs y')) | (y,y') <- ys ])
    ++
    [ x | x <- xs, fst x `notElem` (dominio ys)]
\end{code}

\begin{code}
composicionConmutativa :: Sust -> Sust -> Bool
composicionConmutativa xs ys = 
    composicion xs ys == composicion ys xs
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
\item Nota: Las comprobaciones con QuickCheck emplean código del
  módulo \texttt{Generadores}.
\end{description}


\begin{Def}
 Una unificación de las variables $x_1$ y $x_2$ es una sustitución $S$
 tal que $S(x_1) = S(x_2)=t$. 
\end{Def}

\begin{code}
unificacionTerminos :: Termino -> Termino -> [Sust]
unificacionTerminos (Var x) (Var y)   | x==y      = [identidad]
                                      | otherwise = [[(x,Var y)]]
unificacionTerminos (Var x) t         = [ [(x,t)] | x `notElem` varEnTerm t]
unificacionTerminos t (Var y)         = [ [(y,t)] | y `notElem` varEnTerm t]
unificacionTerminos (Ter a ts) (Ter b rs) = 
    [ u | a==b, u <- unificaTermLista ts rs ]
\end{code}

\begin{Def}
  \texttt{UnificaTermLista} es una función que se aplica a dos listas
  dadas, tal que
  \begin{enumerate}
  \item Si las dos listas son vacías, devuelve la \texttt{identidad}
    de la sustitución.
  \item La unificación de las listas $t_1,\dots,t_n$ y $r_1,\dots,r_n$
    es el resultado de ejecutar la composición de unificaciones.
  \end{enumerate}
\end{Def}

\begin{code}
unificaTermLista :: [Termino] -> [Termino] -> [Sust]
unificaTermLista [] []         = [identidad]
unificaTermLista [] (r:rs)     = []
unificaTermLista (t:ts) []     = []
unificaTermLista (t:ts) (r:rs) = 
    [ composicion u1 u2 | u1 <- unificacionTerminos t r,
     u2 <- unificaTermLista (susTerms u1 ts) (susTerms u1 rs) ]   
\end{code}

\section{Skolem}
Para una unificación eficiente 
