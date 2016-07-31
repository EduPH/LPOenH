\begin{code}
module PTLP where
import LPH
import Data.List
import Test.QuickCheck -- Para ejemplos
import Generadores     -- Para ejemplos

\end{code}

\section{Sustitución}

\begin{Def}
  Una \textbf{sustitución} es una aplicación $S: Variable \rightarrow Termino$.
\end{Def}

\begin{nota}
  $[x_1/t_1,x_2/t_2,\dots ,x_n/t_n]$ representa la sustitución
  \begin{equation*}
    S(x) =
     \left\{
      \begin{array}{ll}
        t_i, \text{ si } x \text{ es } x_i \\
        x, \text{ si } x \notin \left\{x_1,\dots ,x_n \right\}
      \end{array}
     \right .
  \end{equation*}
\end{nota}

En la lógica de primer orden, a la hora de emplear el método de tableros, es
necesario sustituir las variables ligadas por términos. Por lo tanto,
requerimos de la definición de un nuevo tipo de dato para las sustituciones.

\begin{code}
type Sust = [(Variable, Termino)]
\end{code}

\comentario{Sería interesante comparar la representación de sustituciones
  mediante diccionarios con la librería Data.Map}

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
hacerApropiada [] = []
hacerApropiada (x:xs) | Var (fst x) /= snd x = x: hacerApropiada xs
                      | otherwise = hacerApropiada xs
\end{code}

Por ejemplo,

\begin{sesion}
hacerApropiada [(x,tx)]         ==  []
hacerApropiada [(x,tx),(x,ty)]  ==  [(x,y)]
\end{sesion}

Como la sustitución es una aplicación, podemos distinguir \texttt{dominio} y
\texttt{recorrido}.

\index{\texttt{dominio}}
\index{\texttt{recorrido}}
\begin{code}
dominio :: Sust -> [Variable]
dominio = nub . map fst

recorrido :: Sust -> [Termino]
recorrido = nub . map snd
\end{code}

Por ejemplo,

\begin{sesion}
dominio [(x,tx)]           ==  [x]
dominio [(x,tx),(x,ty)]    ==  [x]
recorrido [(x,tx)]         ==  [x]
recorrido [(x,tx),(x,ty)]  ==  [x,y]
\end{sesion}


Posteriormente, se define una función que hace la sustitución de una variable
concreta. La denotamos \texttt{(sustituyeVar sust var)}

\begin{code}
sustituyeVar :: Sust -> Variable -> Termino
sustituyeVar [] y                      = Var y
sustituyeVar ((x,x'):xs) y | x == y    = x'
                           | otherwise = sustituyeVar xs y
\end{code}

\begin{Def}
  $t[x_1/t_1, \dots , x_n/t_n]$ es el término obtenido sustituyendo en $t$ las
  apariciones de $x_i$ por $t_i$.
\end{Def}

\begin{Def}
  La extensión de la sustitución a términos es la aplicación
  $S: Term(L) \rightarrow Term(L)$ definida por
  \begin{equation*}
    S(t) = \left\{
    \begin{array}{ll}
      c,                       & \text{si $t$ es una constante $c$} \\
      S(x),                    & \text{si $t$ es una variable $x$} \\
      f(S(t_1),\dots, S(t_n)), & \text{si $T$ es $f(t_1,\dots ,t_n)$} 
    \end{array} \right.
  \end{equation*}
\end{Def}

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

Por ejemplo,

\begin{sesion}
susTerm  [(x,ty)] tx              ==  y
susTerms [(x,ty),(y,tx)] [tx,ty]  ==  [y,x]
\end{sesion}

\begin{Def}
  $F[x_1/t_1,\dots , x_n/t_n]$ es la fórmula obtenida sustituyendo en $F$ las
  apariciones libres de $x_i$ por $t_i$.
\end{Def}

\begin{Def}
  La extensión de $S$ a fórmulas es la aplicación $S: Form(L) \rightarrow Form(L)$
  definida por
  \begin{equation*}
    S(F) =
     \left\{
      \begin{array}{ll}
        P(S(t_1),\dots,S(t_n)),
         & \text{si $F$ es la fórmula atómica $P(t_1,\dots , t_n)$} \\
        S(t_1) = S(t_2),
         & \text{si $F$ es la fórmula $t_1 = t_2$} \\
        \neg(S(G)),
         & \text{si $F$ es $\neg G$} \\
        S(G)*S(H),
         & \text{si $F$ es $G*H$} \\
        (Qx)(S_x(G)),
         & \text{si $F$ es $(Qx)G$}
      \end{array}
     \right .
  \end{equation*}
  donde $S_x$ es la sustitución definida por
  \begin{equation*}
    S_x(y) =
    \left\{
      \begin{array}{ll}
        x,    &\text{si $y$ es $x$} \\
        S(y), &\text{si $y$ es distinta de $x$}
      \end{array}
    \right .
  \end{equation*}
\end{Def}

Definimos \texttt{(sustitucionForm s f)}, donde \texttt{s} representa la
sustitución y \texttt{f} la fórmula.

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

Por ejemplo,
\begin{sesion}
ghci> formula3
(R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> sustitucionForm [(x,ty)] formula3
(R[y,y]⟹∃z (R[y,z]⋀R[z,y]))
\end{sesion}

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
composicion [(x,tx)] [(y,ty)]  ==  [(x,x)]
composicion [(x,tx)] [(x,ty)]  ==  [(x,y)]
\end{sesion}

\begin{code}
composicionConmutativa :: Sust -> Sust -> Bool
composicionConmutativa s1 s2 = 
  composicion s1 s2 == composicion s2 s1
\end{code} 
 
Y comprobando con QuickCheck que no lo es

\begin{sesion}
ghci> quickCheck composicionConmutativa
*** Failed! Falsifiable (after 3 tests and 1 shrink): 
[(i3,n)]
[(c19,i)]
\end{sesion}

Un contraejemplo más claro es

\begin{sesion}
composicion [(x,tx)] [(y,ty)]  ==  [(x,x)]
composicion [(y,ty)] [(x,tx)]  ==  [(y,y)]
\end{sesion}

\begin{nota}
  Las comprobaciones con QuickCheck emplean código del módulo
  \texttt{Generadores}.
\end{nota}

\begin{Def}
  Una sustitución se denomina \textbf{libre para una fórmula} cuando
  todas las apariciones de variables introducidas por la sustitución
  en esa fórmula resultan libres.
\end{Def}

Un ejemplo de una sustitución que no es libre

\begin{sesion}
ghci> Ex x (Atom "R" [tx,ty])
∃x R[x,y]
ghci> variablesLibres (Ex x (Atom "R" [tx,ty]))
[y]
ghci> sustitucionForm [(y,tx)] (Ex x (Atom "R" [tx,ty]))
∃x R[x,x]
ghci> variablesLibres (sustitucionForm [(y,tx)] (Ex x (Atom "R" [tx,ty])))
[]
\end{sesion}

Un ejemplo de una sustitución libre

\begin{sesion}
ghci> formula5
(∀x P[x]⟹∀y Q[x,y])
ghci> variablesLibres formula5
[x]
ghci> sustitucionForm [(x,tz)] formula5
(∀x P[x]⟹∀y Q[z,y])
ghci> variablesLibres (sustitucionForm [(x,tz)] formula5)
[z]
\end{sesion}

\comentario{¿Una sustitución libre se puede caracterizar por la longitud de
  la lista de variables libres antes y despues de la sustitución?}

\section{Unificación}

\begin{Def}
  Un \textbf{unificador} de dos términos $t_1$ y $t_2$ es una sustitución $S$ tal que
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

Por ejemplo,

\begin{sesion}
unificadoresListas [tx] [ty]  ==  [[(x,y)]]
unificadoresListas [tx] [tx]  ==  [[]]
\end{sesion}

\section{Skolem}

\begin{Def}
  Una fórmula está en \textbf{forma normal conjuntiva} si es una conjunción de
  disyunciones de literales.
  $$(p_1\vee \dots \vee p_n) \wedge \dots \wedge (q_1 \vee \dots \vee q_m)$$
\end{Def}

\begin{Def}
  Una fórmula está en \textbf{forma normal disyuntiva} si es una disyunción de
  conjunciones de literales.
  $$(p_1 \wedge \dots \wedge p_n) \vee \dots \vee (q_1\wedge \dots \wedge q_m)$$
\end{Def}

\subsection{Forma rectificada}

\begin{Def}
  Una fórmula $F$ está en forma \textbf{rectificada} si ninguna variable
  aparece libre y ligada y cada cuantificador se refiere a una variable
  diferente.
\end{Def}

\subsection{Forma normal prenexa}

\begin{Def}
  Una fórmula $F$ está en forma \textbf{normal prenexa} si es de la forma
  $Q_1x_1 \dots Q_nx_nG$ donde $Q_i \in \{\forall ,\exists \}$ y $G$ no tiene
  cuantificadores.
\end{Def}

\subsection{Forma normal prenexa conjuntiva}
\begin{Def}
  Una fórmula $F$ está en \textbf{forma normal prenexa conjuntiva} si está en
  forma normal prenexa con $G$ en forma normal conjuntiva.
\end{Def}

\subsection{Forma de Skolem}

\begin{Def}
  La fórmula \texttt{F} está en \textbf{forma de Skolem} si es de la forma
  $\forall x_1 \dots \forall x_n G$, donde $n \geq 0$ y $G$ no tiene
  cuantificadores.
\end{Def}

Para transformar una fórmula en forma de Skolem emplearemos sustituciones y
unificaciones. Además, necesitamos eliminar las equivalencias e implicaciones.
Para ello definimos la equivalencia y equisatisfacibilidad entre fórmulas.

\begin{Def}
  Las fórmulas \texttt{F} y \texttt{G} son \textbf{equivalentes} si para toda
  interpretación valen lo mismo.
\end{Def}

\begin{Def}
  Las fórmulas \texttt{F} y \texttt{G} son \textbf{equisatisfacibles} si se cumple
  que ambas son satisfacibles o ninguna lo es.
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
  Conj [elimImpEquiv (Impl f1 f2),
        elimImpEquiv (Impl f2 f1)]
elimImpEquiv (Impl f1 f2) =
  Disy [Neg f1, f2]
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

Empleamos las fórmulas 2, 3 y 4 ya definidas anteriormente como ejemplo:

\begin{sesion}
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> elimImpEquiv formula2
∀x ∀y (¬R[x,y]⋁∃z (R[x,z]⋀R[z,y]))
ghci> formula3
(R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> elimImpEquiv formula3
(¬R[x,y]⋁∃z (R[x,z]⋀R[z,y]))
ghci> formula4
∃x R[cero,x]
ghci> elimImpEquiv formula4
∃x R[cero,x]
\end{sesion}

Finalmente, definamos una cadena de funciones, para finalizar con
\texttt{(skolem f)} que transforma \texttt{f} a su forma de Skolem.

Se define la función \texttt{(skol k vs)} que convierte una lista de variables
a un término de Skolem. Al calcular la forma de skolem de una fórmula, las variables
cuantificadas son sustituidas por lo que denotamos \textbf{término de skolem} para obtener
una fórmula libre. Los términos de skolem estan compuestos por las siglas ``sk''
y un entero que lo identifique.


\index{\texttt{skol}}
\begin{code}
skol :: Int -> [Variable] -> Termino
skol k vs = Ter ("sk" ++ show k) [Var x | x <- vs]
\end{code}

Por ejemplo,

\begin{sesion}
skol 1 [x]  ==  sk1[x]
\end{sesion}

Definimos la función \texttt{(skf f vs pol k)}, donde
\begin{enumerate}
\item \texttt{f} es la fórmula que queremos convertir.
\item \texttt{vs} es la lista de los cuantificadores (son necesarios
  en la recursión).
\item \texttt{pol} es la polaridad, es de tipo \texttt{Bool}.
\item \texttt{k} es de tipo \texttt{Int} y sirve como identificador
  de la forma de Skolem.
\end{enumerate}

\begin{Def}
  La \textbf{Polaridad} cuantifica las apariciones de las variables cuantificadas
  de la siguiente forma:
  \begin{itemize*}
  \item  Una cantidad de apariciones impar de $x$ en la subfórmula $F$ de
    $\exists x F$ indica que $x$ tiene una polaridad negativa en la fórmula.
  \item  Una cantidad de apariciones par de $x$ en la subfórmula $F$ de
    $\forall x F$ indica que $x$ tiene una polaridad positiva en la fórmula. 
  \end{itemize*}
\end{Def}

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

La skolemización de una fórmula sin equivalencias ni implicaciones se define
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
ghci> skolem formula2
∀x ∀y (¬R[x,y]⋁(R[x,sk0[x,y]]⋀R[sk0[x,y],y]))
ghci> skolem formula3
(¬R[x,y]⋁(R[x,sk0]⋀R[sk0,y]))
ghci> skolem formula4
R[cero,sk0]
ghci> skolem formula5
(¬P[sk0]⋁∀y Q[x,y])
\end{sesion}

\section{Tableros semánticos}

\begin{Def}
  Un conjunto de fórmulas es \textbf{consistente} si tiene algún modelo. En
  caso contrario, se denomina \textbf{inconsistente}.
\end{Def}

\comentario{Distinguir el caso de fórmulas con variables libres.}

La idea de obtener fórmulas equivalentes nos hace introducir los tipos de
fórmulas alfa, beta, gamma y delta. No son más que equivalencias ordenadas por
orden teórico en el que se pueden acometer para una simplicación eficiente de
una fórmula, a otra cuyas únicas conectivas lógicas sean disyunciones y
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
alfa (Conj _)       = True
alfa (Neg (Disy _)) = True
alfa _              = False
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

\index{\texttt{beta}}
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
  
  \vspace*{2ex}
  
Las definimos en Haskell
  
  \index{\texttt{delta}}
\begin{code}
delta :: Form -> Bool
delta  (Neg (PTodo _ _))    = True
delta  (Ex _ _)             = True
delta _                     = False
\end{code}
\vspace*{2ex}
  
\end{itemize}

\begin{nota}
  En las tablas, cada elemento de una columna es equivalente a su análogo en la
  otra columna.

  \comentario{Precisar la equivalencia con las componentes.}
  
\end{nota}

Mediante estas equivalencias se procede a lo que se denomina método de los
tableros semánticos. Uno de los objetivos del método de los tableros es
determinar si una fórmula es consistente, así como la búsqueda de modelos.

\begin{Def}
  Un \textbf{literal} es un átomo o la negación de un átomo.
\end{Def}

Lo definimos en haskell

\index{\texttt{literal}}
\begin{code}
atomo, negAtomo, literal :: Form -> Bool

atomo (Atom _ _)          = True
atomo _                   = False

negAtomo (Neg (Atom _ _)) = True
negAtomo  _               = False

literal f = atomo f || negAtomo f
\end{code}

El método de tableros de un conjunto de fórmulas $S$ sigue el siguiente
algoritmo:

\begin{itemize*}
\item El árbol cuyo único nodo tiene como etiqueta $S$ es
  un tablero de $S$.
\item Sea $\mathcal{T}$ un tablero de $S$ y $S_1$ la etiqueta de
  una hoja  de $\mathcal{T}$.
  \begin{enumerate}
  \item Si $S_1$ contiene una fórmula y su negación, entonces el árbol
    obtenido añadiendo como hijo de $S_1$ el nodo etiquetado con
    $\left\{ \perp \right\}$ es un tablero de $S$.
  \item Si $S_1$ contiene una doble negación $\neg \neg F$, entonces
    el árbol obtenido añadiendo como hijo de $S_1$ el nodo etiquetado
    con $(S_1 \backlash \left\{\neg \neg F \right\})\cup \left\{ F \right\}$
    es un tablero de $S$.
  \item Si $S_1$ contiene una fórmula alfa $F$ de componentes $F_1$ y $F_2$,
    entonces el árbol obtenido añadiendo como hijo de $S_1$ el nodo etiquetado
    con $(S_1 \backlash \left\{ F \right\})\cup \left\{ F_1,F_2 \right\}$
    es un tablero de $S$.
  \item Si $S_1$ contiene una fórmula beta de $F$ de componentes $F_1$ y $F_2$,
    entonces el árbol obtenido añadiendo como hijos de $S_1$ los nodos
    etiquetados con $(S_1 \backlash \left\{ F \right\}) \cup \left\{ F_1 \right\}$ y
    $(S_1 \backlash \left\{ F \right\})\cup \left\{ F_2 \right\}$ es un tablero
    de $S$.
  \end{enumerate}
\end{itemize*}


\begin{Def}
  Se dice que una hoja es \textbf{cerrada} si contiene una fórmula y su negación.
  Se representa $\bot$
\end{Def}

\begin{Def}
  Se dice que una hoja es \textbf{abierta} si es un conjunto de literales y no contiene
  un literal y su negación.
\end{Def}

\begin{Def}
  Un \textbf{tablero completo} es un tablero tal que todas sus hojas son abiertas o
  cerradas.
\end{Def}

Ejemplo de tablero completo

\begin{center}
  \begin{tikzpicture}[sibling distance=15em,
  every node/.style = {shape=rectangle, rounded corners,
    draw, align=center,
    top color=white}
]]
  \node {1. $\neg (p \vee q \rightarrow p \wedge q)$}
  child { node {2. $p\vee q$ , $\neg (p \wedge q)$ (1)}
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

\comentario{Se solapan las ramas del arbol}

La fórmula del tablero se representa en Haskell
Se definen los átomos.

\begin{code}
p = Atom "p" []
q = Atom "q" []
r = Atom "r" []
\end{code}

Para que la fórmula quede

\begin{code}
tab1 = Neg (Impl (Disy [p,q]) (Conj [p,q]))
\end{code}

\begin{sesion}
ghci> tab1
¬((p⋁q)⟹(p⋀q))
\end{sesion}

\begin{Def}
  Un tablero es \textbf{cerrado} si todas sus hojas son cerradas.
\end{Def}

Un ejemplo de tablero cerrado es

\begin{center}
\begin{tikzpicture}[sibling distance=15em,
  every node/.style = {shape=rectangle, rounded corners,
    draw, align=center, top color=white}]]
  \node {1. $ (p \rightarrow q) \wedge (q \rightarrow r)
    \wedge  \neg (p \rightarrow r)$  }
  child { node {2. $p \rightarrow q$, $q \rightarrow r$,
      $p$, $ \neg r$ (1) }
    child { node {3. $p \rightarrow q$ , $\neg p$ ,
        $p$, $\neg r$ (2)}
      child { node {5. $ \neg p$ , $ \neg q$ ,
          $p$ , $ \neg r$ (3)}
        child { node {7. $ \perp $ (5)}}}
      child { node {6. $q$ , $ \neg q$ ,
          $p$ , $ \neg r$ (3)}
        child { node {8. $ \perp $ (6)}}}}
    child { node {4. $p \rightarrow q$ , $r$ ,
        $p$ , $ \neg r$ (2)}
      child { node {9. $ \perp $ (4)} }}};
\end{tikzpicture}
\end{center}

La fórmula del tablero se representa en Haskell

\begin{code}
tab2 = Conj [Impl p q, Impl q r, Neg (Impl p r)]
\end{code}

\begin{sesion}
ghci> tab2
((p⟹q)⋀((q⟹r)⋀¬(p⟹r)))
\end{sesion}

\begin{Teo}
  Si una fórmula $F$ es consistente, entonces cualquier tablero de $F$ tendrá
  ramas abiertas.
\end{Teo}

Nuestro objetivo es definir en Haskell un método para el cálculo de tableros
semánticos. El contenido relativo a tableros semánticos se encuentra en el
módulo \texttt{Tableros}.

\entrada{Tableros}


