\section{Sustitución con la librería Data.Map}

En esta sección procuraremos dar una implementación alternativa de la
sustitución empleando funciones procedentes de la librería \texttt{Data.Map}.

\begin{code}
module SustMap where
import LPH
import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
\end{code}

Se define la sustitución de términos mediante la función \texttt{sustTerm t d},
donde \texttt{t} representa el término que será sustituido y \texttt{d} el
diccionario en el que se definen las distintas sutituciones.

\index{\texttt{sustTerm}}
\begin{code}
sustTerm :: Termino -> Map Variable Termino -> Termino
sustTerm (Var x) d    = M.findWithDefault (Var x) x d
sustTerm (Ter f ts) d = Ter f (sustTerms ts d)
\end{code}

\begin{nota}
  El tipo sustitución que definimos en la sección sobre sustitución en el
  capítulo ``El método de los tableros semánticos'' \ref{sec:sustitucion} será
  sustituido por un diccionario del tipo \texttt{Map Variable Termino}.
\end{nota}

Como en una fórmula pueden aparecer varios términos en una misma lista,
implementamos una generalización de la función anterior,
\texttt{(sustTerms ts d)}.

\index{\texttt{sustTerms}}
\begin{code}
sustTerms :: [Termino] -> Map Variable Termino -> [Termino]
sustTerms ts d = [sustTerm t d | t <- ts]
\end{code}

Finalmente, se define \texttt{(sustitucion f d)} que aplica
la sustitución representada por el diccionario \texttt{d} a la
fórmula \texttt{f}.

\index{\texttt{sustitucion}}
\begin{code}
sustitucion :: Form -> Map Variable Termino -> Form 
sustitucion (Atom str ts) d = Atom str (sustTerms ts d)
sustitucion (Ig t1 t2) d    = Ig (sustTerm t1 d) (sustTerm t2 d)
sustitucion (Neg f) d       = Neg (sustitucion f d)
sustitucion (Impl f1 f2) d  =
  Impl (sustitucion f1 d) (sustitucion f2 d)
sustitucion (Equiv f1 f2) d =
  Equiv (sustitucion f1 d) (sustitucion f2 d)
sustitucion (Conj fs) d     = Conj [sustitucion f d | f <- fs]
sustitucion (Disy fs) d     = Disy [sustitucion f d | f <- fs]
sustitucion (PTodo v f) d   = PTodo v (sustitucion f (M.delete v d))
sustitucion (Ex v f) d      = Ex v (sustitucion f (M.delete v d))
\end{code}

Veamos algunos ejemplos:

\begin{code}
-- | Ejemplo:
-- >>> formula3
-- (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- >>> let sust = M.fromList [(x,ty),(y,tx),(z,tx)]
-- >>> sustitucion formula3 sust
-- (R[y,x]⟹∃z (R[y,z]⋀R[z,x]))
\end{code}

Se define la función \texttt{(hacerApropiadaM d)} que elimina los pares
con sus dos componentes iguales

\index{\texttt{hacerApropiadaM}}
\begin{code}
hacerApropiadaM :: Map Variable Termino -> Map Variable Termino
hacerApropiadaM = M.filterWithKey (\k t -> t /= Var x)
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplo  
-- >>> hacerApropiadaM (M.fromList [(x,tx),(y,tz),(z,tz)])
-- fromList [(y,z)]
\end{code}

En nuestra primera definición de sustitución comprobamos que su composición
no era conmutativa. Definamos la función \texttt{(composicionMap d1 d2)}
que compone ambos diccionarios.

\begin{code}
composicionMap :: Map Variable Termino
               -> Map Variable Termino -> Map Variable Termino
composicionMap d1 d2 =
    hacerApropiadaM (M.fromList ([(y,sustTerm y' d1) | (y,y') <- d2']++
               [ x | x <- d1', fst x `notElem` (M.keys d2)]))
    where
      d1' = M.toList d1
      d2' = M.toList d2
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> composicionMap (M.fromList [(x,ty)]) (M.fromList [(y,tz)])
-- fromList [(x,y),(y,z)]
-- >>> composicionMap (M.fromList [(y,tz)]) (M.fromList [(x,ty)])
-- fromList [(x,z),(y,z)]
\end{code}
