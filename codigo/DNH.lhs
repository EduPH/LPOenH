\begin{code}
module DNH where
import LPH
import Data.List
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty
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

\begin{code}
-- | Ejemplos
-- >>> hacerApropiada [(x,tx)]         
-- []
-- >>> hacerApropiada [(x,tx),(x,ty)]
-- [(x,y)]
\end{code}

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

\begin{code}
-- | Ejemplos
-- >>> dominio [(x,tx)]           
-- [x]
-- >>> dominio [(x,tx),(x,ty)]    
-- [x]
-- >>> recorrido [(x,tx)]         
-- [x]
-- >>> recorrido [(x,tx),(x,ty)]  
-- [x,y]
\end{code}


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

\begin{code}
-- | Ejemplos
-- >>> susTerm  [(x,ty)] tx                
-- y
-- >>> susTerms [(x,ty),(y,tx)] [tx,ty]  
-- [y,x]
\end{code}

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

\begin{code}
-- | Ejemplos
-- >>> formula3
-- (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- >>> sustitucionForm [(x,ty)] formula3
-- (R[y,y]⟹∃z (R[y,z]⋀R[z,y]))
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

\begin{code}
-- | Ejemplos
-- >>> composicion [(x,tx)] [(y,ty)]  
-- [(x,x)]
-- >>> composicion [(x,tx)] [(x,ty)]  
-- [(x,y)]
\end{code}

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

\begin{code}
-- | Ejemplo
-- >>> let f1 = Ex x (Atom "R" [tx,ty])
-- >>> f1
-- ∃x R[x,y]
-- >>> variablesLibres f1
-- [y]
-- >>> sustitucionForm [(y,tx)] f1
-- ∃x R[x,x]
-- >>> variablesLibres (sustitucionForm [(y,tx)] f1)
-- []
\end{code}

Un ejemplo de una sustitución libre

\begin{code}
-- | Ejemplo
-- >>> formula5
-- (∀x P[x]⟹∀y Q[x,y])
-- >>> variablesLibres formula5
-- [x]
-- >>> sustitucionForm [(x,tz)] formula5
-- (∀x P[x]⟹∀y Q[z,y])
-- >>> variablesLibres (sustitucionForm [(x,tz)] formula5)
-- [z]
\end{code}

\section{Reglas de deducción natural}

Se definen los átomos.

\begin{code}
p = Atom "p" []
q = Atom "q" []
r = Atom "r" []
\end{code}

\subsection{Reglas de la conjunción}

Debido a la representación que hemos elegido, pueden darse conjunciones
de conjunciones, lo cual no nos interesa. Por ello, definimos \texttt{unificacionConjuncion}
que extrae la conjunción al exterior.

\index{\texttt{unificaConjuncion}}
\begin{code}
unificaConjuncion :: Form -> Form
unificaConjuncion p@(Atom _ _) = p
unificaConjuncion (Disy fs) = Disy fs
unificaConjuncion (Conj fs) = Conj (concat (map (aux) (concat xs)))
    where 
      xs = [ aux f | f <- fs]
      aux (Conj xs) = xs
      aux f = [f]
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> let f1 = Conj [p, Conj [r,q]]
-- >>> f1
-- (p⋀(r⋀q))
-- >>> unificaConjuncion f1
-- (p⋀(r⋀q))
-- >>> unificaConjuncion f1 == (Conj [p, Conj [r,q]])
-- False
-- >>> unificaConjuncion f1 == (Conj [p,r,q])
-- True
\end{code}

\begin{nota}
  La representación ``visual'' por pantalla de una conjunción de conjunciones
  y su unificación puede ser la misma, como en el ejemplo anterior.
\end{nota}


\begin{itemize*}
\item Regla de la introducción de la conjunción:
  $$\frac{F\quad G}{F\wedge G}$$
  Se implementa en Haskell mediante la función \texttt{(introConj f g)}
  \index{\texttt{introConj}}
\begin{code}
introConj :: Form -> Form -> Form
introConj f g = unificaConjuncion (Conj [f,g])
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplos
-- >>> introConj p q
-- (p⋀q)
-- >>> introConj (Conj [p,q]) r
-- (p⋀(q⋀r))
\end{code}


\item Reglas de la eliminación de la introducción:
  $$\frac{F_1 \wedge \dots \wedge F_n}{F_1} \text{ y } \frac{F_1\wedge \dots \wedge F_n}{F_n} $$
  Se implementa en Haskell mediante las funciones \texttt{(elimConjI f g)} y
  \texttt{(elimConjD f g)}.
\index{\texttt{elimConjI}}
\index{\texttt{elimConjD}}
\begin{code}
elimConjI, elimConjD :: Form -> Form
elimConjI (Conj fs) = head fs
elimConjD (Conj fs) = last fs
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> let f1 = Conj [p,q]
-- >>> elimConjI f1
-- p
-- >>> elimConjD f1
-- q
\end{code}
\end{itemize*}

\subsection{Reglas de la doble negación}

\begin{itemize*}
\item Regla de eliminación de la doble negación: 
  $$\frac{\neg \neg F}{F}$$
  Se implementa en Haskell mediante la función \texttt{(elimDNeg f)}
\index{\texttt{elimDNeg}}
\begin{code}
elimDNeg :: Form -> Form
elimDNeg (Neg (Neg f)) = f
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> elimDNeg (Neg (Neg p))
-- p
\end{code}

\item Regla de la introducción de la doble negación:
  $$\frac{F}{\neg \neg F} $$
  Se implementa en Haskell mediante la función \texttt{(introDNeg f)}
\index{\texttt{introDNeg}}
\begin{code}
introDNeg :: Form -> Form
introDNeg f = Neg (Neg f)
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> introDNeg p
-- ¬¬p
\end{code}
\end{itemize*}


\subsection{Reglas de eliminación del condicional}

\begin{itemize*}
\item Regla de la eliminación del condicional:
  $$\frac{F\quad F\rightarrow G}{G}$$
  Lo implementamos en haskell mediante la función \texttt{elimCond f g}
\index{\texttt{elimCond}}
\begin{code}
elimCond :: Form -> Form -> Form
elimCond  f (Impl f1 f2) |f == f1 = f2
elimCond  (Impl f1 f2) f |f == f1 = f2
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> elimCond p (Impl p q)
-- q
\end{code}
\end{itemize*}

\subsection{Regla derivada de Modus Tollens(MT)}

\begin{itemize*}
\item Regla derivada de modus Tollens:
  $$\frac{F \rightarrow G\quad \neg G}{\neg F}$$
  Lo implementamos en Haskell mediante la función \texttt{(modusTollens f g)}
\index{\texttt{modusTollens}}
\begin{code}
modusTollens :: Form -> Form -> Form
modusTollens (Impl f1 f2) (Neg f) | f == f2 = Neg f1
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> modusTollens (Impl p q) (Neg q)
-- ¬p
\end{code}  
\end{itemize*}

\subsection{Regla de introducción del condicional}

\begin{itemize*}
\item Regla de introducción del condicional:
$$\frac{}{G} $$ 
\comentario{escribir expresión LaTex}
Lo implementamos en Haskell mediante la función \texttt{(introCond f g)}

\index{\texttt{introCond}}
\begin{code}
introCond :: Form -> Form -> Form
introCond f g = Impl f g
\end{code}
\end{itemize*}

