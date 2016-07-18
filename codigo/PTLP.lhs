\section{Sustitución}

\begin{code}
module PTLP where
import LPH
import Data.List
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
sustitucionForm s (Ig t1 t2) =
  Ig (susTerm s t1) (susTerm s t2)
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

Por ejemplo,

\begin{sesion}
ghci> composicion [(x,tx)] [(y,ty)]
[(x,x)]
ghci> composicion [(x,tx)] [(x,ty)]
[(x,y)]
\end{sesion}

\begin{code}
composicionConmutativa :: Sust -> Sust -> Bool
composicionConmutativa s1 s2 = 
  composicion s1 s2 == composicion s2 s1
\end{code} 
 
Y comprobando con QuickCheck, no lo es

\begin{sesion}
ghci> quickCheck composicionConmutativa
*** Failed! Falsifiable (after 3 tests and 1 shrink): 
[(i3,n)]
[(c19,i)]
\end{sesion}

Un contraejemplo más claro es

\begin{sesion}
ghci> composicion [(x,tx)] [(y,ty)]
[(x,x)]
ghci> composicion  [(y,ty)] [(x,tx)]
[(y,y)]
ghci> composicion  [(y,ty)] [(x,tx)] == composicion [(x,tx)] [(y,ty)]
False
\end{sesion}

\begin{description}
\item Nota: Las comprobaciones con QuickCheck emplean código del módulo
  \texttt{Generadores}.
\end{description}

\section{Unificación}

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
  [u | f == g, u <- unificadoresListas ts rs]
\end{code}

El valor de \texttt{(unificadoresListas ts rs)} es un unificador de las listas
de términos \texttt{ts} y \texttt{rs}; es decir, una sustitución \texttt{s} tal
que si \texttt{ts = [t1,...,tn]} y \texttt{rs = [r1,...,rn]} entonces
\texttt{s(t1) = s(r1)}, \dots, \texttt{s(tn) = s(rn)}.

\begin{code}
unificadoresListas :: [Termino] -> [Termino] -> [Sust]
unificadoresListas [] [] = [identidad]
unificadoresListas [] _  = []
unificadoresListas _ []  = []
unificadoresListas (t:ts) (r:rs) = 
    [composicion u1 u2
    | u1 <- unificadoresTerminos t r
    , u2 <- unificadoresListas (susTerms u1 ts) (susTerms u1 rs)]   
\end{code}

Por ejemplo

\begin{sesion}
ghci> unificadoresListas [tx] [ty]
[[(x,y)]]
ghci> unificadoresListas [tx] [tx]
[[]]
\end{sesion}

\section{Skolem}

\begin{Def}
  La fórmula \texttt{F} está en forma de Skolem si es de la forma
  $\forall x_1 \dots \forall x_n \texttt{G}$, donde $n\geq 0$ y \texttt{G}
  no tiene cuantificadores.
\end{Def}

Para alcanzar una fórmula en forma de Skolem emplearemos sustituciones y
unificaciones. Además, necesitamos eliminar las equivalencias e implicaciones.
Para ello definimos la equivalencia y equisatisfacibilidad entre fórmulas.

\begin{Def}
  Las fórmulas \texttt{F} y \texttt{G} son equivalentes si para toda
  interpretación valen lo mismo.
\end{Def}

\begin{Def}
  Las fórmulas \texttt{F} y \texttt{G} son equisatisfacibles si se cumple
  $(\texttt{F} \text{ satisfacible } \Leftrightarrow 
    \texttt{G} \text{ satisfacible })$
\end{Def}

Definimos la función \texttt{(elimImpEquiv f)}, para obtener fórmulas
equivalentes sin equivalencias ni implicaciones.

\begin{code}
elimImpEquiv :: Form -> Form
elimImpEquiv (Atom f xs) =
  Atom f xs
elimImpEquiv (Ig t1 t2) =
  Ig t1 t2
elimImpEquiv (Equiv f1 f2) =
  Conj [ elimImpEquiv (Impl f1 f2),
         elimImpEquiv (Impl f2 f1)]
elimImpEquiv (Impl f1 f2) =
  Disy [ Neg f1, f2]
elimImpEquiv (Neg f) =
  Neg (elimImpEquiv f)
elimImpEquiv (Disy fs) =
  Disy (map elimImpEquiv fs)
elimImpEquiv (Conj fs) =
  Conj (map elimImpEquiv fs)
elimImpEquiv (PTodo x f) =
  PTodo x (elimImpEquiv f)
elimImpEquiv (Ex x f) =
  Ex x (elimImpEquiv f)
\end{code}

Empleamos las fórmulas 2,3 y 4 ya definidas anteriormenta como ejemplo:
\begin{sesion}
ghci> formula_2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀[R[z,y]]))
ghci> elimImpEquiv formula_2
∀x ∀y (¬R[x,y]⋁[∃z (R[x,z]⋀[R[z,y]])])
ghci> formula_3
(R[x,y]⟹∃z (R[x,z]⋀[R[z,y]]))
ghci> elimImpEquiv formula_3
(¬R[x,y]⋁[∃z (R[x,z]⋀[R[z,y]])])
ghci> formula_4
∃x R[cero,x]
ghci> elimImpEquiv formula_4
∃x R[cero,x]
\end{sesion}

Finalmente, definamos una cadena de funciones, para finalizar con
\texttt{(skolem f)} que transforma \texttt{f} a su forma de Skolem.

\index{\texttt{skol}}
\begin{code}
skol :: Int -> [Variable] -> Termino
skol k vs = Ter ("sk" ++ show k) [Var x | x <- vs]
\end{code}

Definimos la función \texttt{(skf f vs pol k)}, donde
\begin{enumerate}
\item \texttt{f} es la fórmula que queremos convertir.
\item \texttt{vs} es la lista de los cuantificadores (son necesarios
  en la recursión).
\item \texttt{pol} es la polaridad, es de tipo \texttt{Bool}.
\item \texttt{k} es de tipo \texttt{Int} y sirve como idetificador
  de la forma de Skolem.
\end{enumerate}

\index{\texttt{skf}}
\begin{code}
skf :: Form -> [Variable] -> Bool -> Int -> (Form,Int)
skf (Atom n ts) _ _ k =
  (Atom n ts,k)
skf (Conj fs) vs pol k =
  (Conj fs',j)
  where (fs',j) = skfs fs vs pol k
skf (Disy fs) vs pol k =
  (Disy fs', j)
  where (fs',j) = skfs fs vs pol k
skf (PTodo x f) vs True k =
  (PTodo x f',j)
  where vs'    = insert x vs
        (f',j) = skf f vs' True k
skf (PTodo x f) vs False k =
  skf (sustitucionForm b f) vs False (k+1)
  where b = [(x,skol k vs)]
skf (Ex x f) vs True k =
  skf (sustitucionForm b f) vs True (k+1)
  where b = [(x,skol k vs)]
skf (Ex x f) vs False k =
  (Ex x f',j)
  where vs' = insert x vs
        (f',j) = skf f vs' False k
skf (Neg f) vs pol k =
  (Neg f',j)
  where (f',j) = skf f vs (not pol) k
\end{code}

donde la skolemización de una lista está definida por  
\index{\texttt{skfs}}
\begin{code}
skfs :: [Form] -> [Variable] -> Bool -> Int -> ([Form],Int)
skfs [] _ _ k        = ([],k)
skfs (f:fs) vs pol k = (f':fs',j)
  where (f',j1) = skf  f  vs pol k
        (fs',j) = skfs fs vs pol j1
\end{code}

La skolemizacoón de una fórmula sin equivalencias ni implicaciones se define
por \index{\texttt{sk}}
\begin{code}
sk :: Form -> Form
sk f = fst (skf f [] True 0)
\end{code}

La función \texttt{(skolem f)} devuelve la forma de Skolem de la fórmula
\texttt{f}.

\index{\texttt{skolem}}
\begin{code}
skolem :: Form -> Form
skolem  = sk . elimImpEquiv 
\end{code}

Por ejemplo,

\begin{sesion}
ghci> sk formula_2
∀x ∀y (¬R[x,y]⋁[(R[x,sk0[x,y]]⋀[R[sk0[x,y],y]])])
ghci> skolem formula_3
(¬R[x,y]⋁[(R[x,sk0]⋀[R[sk0,y]])])
ghci> skolem formula_4
R[cero,sk0]
\end{sesion}

\section{Tableros semánticos}

\begin{Def}
  Una fórmula o conjunto de fórmulas es consistente si tiene algún modelo. En
  caso contrario, se denomina inconsistente.
\end{Def}

La idea de obtener fórmulas equivalentes, nos hace introducir los tipos de
fórmulas alfa, beta, gamma y delta. No son más que equivalencias ordenadas, por
orden teórico en el que se pueden acometer, para una simplicación eficiente de
una fórmula a otra cuyas únicas conectivas lógicas sean disyunciones y
conjunciones.

\begin{itemize}
\item Fórmulas alfa
 
   \vspace*{1ex}

   $\begin{array}{|l|l| } \hline
     \neg (F_1 \rightarrow F_2) & F_1 \wedge F_2               \\ \hline
     \neg(F_1 \vee F_2)         & F_1 \wedge \neg F_2          \\ \hline
     F_1 \leftrightarrow F_2    & (F_1 \rightarrow F_2) \wedge 
                                  (F_2 \rightarrow F_1)        \\ \hline
   \end{array}$

\vspace*{2ex}
Las definimos en Haskell

\index{\texttt{alfa}}
\begin{code}
alfa :: Form -> Bool
alfa (Conj _) = True
alfa (Neg (Disy _)) = True
alfa _ = False
\end{code}

\vspace*{2ex}



\item Fórmulas beta 
  
  \vspace*{1ex}

  $\begin{array}{|l|l|} \hline
    F_1 \rightarrow F_2             & \neg F_1 \vee F_2                \\ \hline
    \neg (F_1 \wedge F_2)           & \neg F_1 \vee \neg F_2           \\ \hline
    \neg (F_1 \leftrightarrow F_2)  & \neg (F_1 \rightarrow F_2 ) \vee 
                                      (\neg F_2 \rightarrow F_1)       \\ \hline
   \end{array}$
   
  \vspace*{2ex}
Las definimos en Haskell

\index{\texttt{Beta}}
\begin{code}
beta :: Form -> Bool
beta (Disy _)       = True
beta (Neg (Conj _)) = True
beta _              = False
\end{code}

\vspace*{2ex}
  
\item Fórmulas gamma 

  \vspace*{1ex}

  $\begin{array}{|l|c|} \hline
    \forall x F      & F [x/t]       \\ \hline
    \neg \exists x F & \neg F [x/t ] \\ \hline
  \end{array}$



\vspace*{1ex}

Notar que $t$ es un término básico.

  \vspace*{2ex}
  
Las definimos en Haskell
  
  \index{\texttt{gamma}}
\begin{code}
gamma :: Form -> Bool
gamma (PTodo _ _)    = True
gamma (Neg (Ex _ _)) = True
gamma _              = False
\end{code}
\vspace*{2ex}
  
\item Fórmulas delta 

  \vspace*{1ex}

  $\begin{array}{|l|l|} \hline
    \exists x F    & F[x / a]       \\ \hline
    \neg \forall F & \neg F [x / a] \\ \hline
  \end{array}$

  \vspace*{1ex}

  Notar que $a$ es una constante nueva.

\end{itemize}

\begin{nota}
  En las tablas, cada elemento de una columna es equivalente a su análogo en la
  otra columna.
\end{nota}

Mediante estas equivalencias se procede a lo que se denomina método de los
tableros semánticos. Uno de los objetivos del método de los tableros es
determinar si una fórmula es inconsistente, así como la búsqueda de modelos.

\begin{Def}
  Un literal es un átomo o la negación de un átomo.
\end{Def}

\begin{Def}
  Se dice que una hoja es cerrada si contiene una fórmula y su negación.
  Se representa $\bot$
\end{Def}

\begin{Def}
  Se dice que una hoja es abierta si es un conjunto de literales y no contiene
  un literal y su negación.
\end{Def}

\begin{Def}
  Un tablero completo es un tablero tal que todas sus hojas son abiertas o
  cerradas.
\end{Def}
Ejemplo de tablero completo
\begin{center}
  \begin{tikzpicture}[sibling distance=15em,
  every node/.style = {shape=rectangle, rounded corners,
    draw, align=center,
    top color=white}]]
  \node {1. $\neg (p \vee q \rightarrow p \wedge q)$}
  child { node {2. $P\vee q$ , $\neg (p \wedge q)$ (1)}
    child { node {3. $p$ , $\neg (p\wedge q)$ (2)}
      child { node {5. $p$, $\neg p$ (3)}
        child { node {7. $\perp$ (5)}}}
      child { node {6. $p$ , $\neg q$ (3)}}}
    child { node {4.  $q$ , $\neg (p\wedge q)$ (2)}
      child { node {8. $q$ , $\neg p$ (4)}}
      child { node {9. $q$ , $\neg q$ (4)}
        child { node {10. $\perp$ (9)}}}}}
  ;
  \end{tikzpicture}
\end{center}

\begin{Def}
  Un tablero es cerrado si todas sus hojas son cerradas.
\end{Def}

Un ejemplo de tablero cerrado es


\begin{center}
\begin{tikzpicture}[sibling distance=15em,
  every node/.style = {shape=rectangle, rounded corners,
    draw, align=center, top color=white}]]
  \node {1. $ (p \rightarrow q) \wedge (q \rightarrow r)
    \wedge ( \neg (p \rightarrow r)$  }
  child { node {2. $p \rightarrow q$, $q \rightarrow r$,
      $P$, $ \neg r$ (1) }
    child { node {3. $p \rightarrow q$ , $\neg p$ ,
        $p$, $\neg r$ (2)}
      child { node {5. $ \neg p$ , $ \neg q$ ,
          $p$ , $ \neg r$ (3)}
        child { node {7. $ \perp $ (5)}}}
      child { node {6. $q$ , $ \neg q$ ,
          $p$ , $ \neg r$ (3)}
        child { node {8. $ \perp $ (6)}}}}
    child { node {4. $P \rightarrow q$ , $r$ ,
        $p$ , $ \neg r$ (2)}
      child { node {9. $ \perp $ (4)} }}}
\end{tikzpicture}
\end{center}

.

\begin{Teo}
  Si una fórmula $F$ es consitente, entonces cualquier tablero de $F$ tendrá
  ramas abiertas.
\end{Teo}

Nuestro objetivo es definir en Haskell un método para el cálculo de
tableros semánticos. El contenido relativo a tableros semánticos 
se encuentra en el módulo \texttt{Tableros}.
\entrada{Tableros}


