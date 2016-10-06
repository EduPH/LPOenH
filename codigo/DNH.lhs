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
                      | otherwise            = hacerApropiada xs
\end{code}

\comentario{La definición de hacerApropiada por comprensión es más simple.}

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
-- >>> dominio [(x,tx),(z,ty)]    
-- [x,z]
-- >>> recorrido [(x,tx)]         
-- [x]
-- >>> recorrido [(x,tx),(z,ty)]  
-- [x,y]
\end{code}

Posteriormente, se define una función que aplica la sustitución a una variable
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

\section{Sustitucion mediante diccionarios}

En esta sección definiremos las sustituciones ,de una manera alternativa,
mediante la librería \texttt{Data.Map}.
\entrada{SustitucionMap}

\section{Reglas de deducción natural}

La deducción natural está compuesta de una serie de reglas a través de las cuales,
partiendo de una fórmula o conjunto de fórmulas, conseguimos deducir otra u otras
fórmulas.

Se definen los átomos \texttt{p},\texttt{q} y \texttt{r}, que nos servirán
para la definición de las fórmulas en los ejemplos.

\begin{code}
p = Atom "p" []
q = Atom "q" []
r = Atom "r" []
\end{code}

A continuación se introducen las reglas de la deducción natural.

\subsection{Reglas de la conjunción}

\begin{itemize*}
\item Regla de la introducción de la conjunción:
  $$\frac{F\quad G}{F\wedge G}$$
  Se implementa en Haskell mediante la función \texttt{(introConj f g)}
  
\index{\texttt{introConj}}
\begin{code}
introConj :: Form -> Form -> Form
introConj (Conj fs) (Conj gs) = Conj (nub (fs++gs))
introConj (Conj fs) g         = Conj (nub (fs++[g]))
introConj f (Conj gs)         = Conj (nub (f:gs))
introConj f g                 = Conj [f,g]      
\end{code}

\begin{nota}
  En la función \texttt{introConj} se distinguen los casos en los que
  alguno de sus argumentos sean conjunciones para su expresión como única conjunción.
\end{nota}

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
elimConjI _         = error "Entrada no valida para esta regla."
elimConjD (Conj fs) = last fs
elimConjD _         = error "Entrada no valida para esta regla."
\end{code}

\begin{nota}
  La función \texttt{error} permite mostrar un mensaje en el caso de que
  la regla sea aplicada a fórmulas que no son del tipo al que debe aplicarse.
\end{nota}
\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> let f1 = Conj [p,q]
-- >>> elimConjI f1
-- p
-- >>> elimConjD f1
-- q
-- >>> introConj (Conj [p,q]) (Conj [q,r])
-- (p⋀(q⋀r))
\end{code}

\item Ejemplo: \framebox{$p\wedge q, r\vdash q \wedge r $}
  \begin{enumerate}
  \item $p\wedge q$ \hfill \texttt{Premisa}
  \item $r$ \hfill \texttt{Premisa}
  \item $q$ \hfill \texttt{elimConjD 1}
  \item $r \wedge q$ \hfill \texttt{introConj 2 3}
  \end{enumerate}
  
En Haskell sería

\begin{code}
-- | Ejemplo
-- >>> let f1 = (Conj [p,q])
-- >>> let f2 = r
-- >>> let f3 = elimConjD f1
-- >>> let f4 = introConj f2 f3
-- >>> f1
--  (p⋀q)
-- >>> f2
-- r
-- >>> f3
-- q
-- >>> f4
-- (r⋀q)
\end{code}
\end{itemize*}

\subsection{Reglas de eliminación del condicional}

\begin{itemize*}
\item Regla de la eliminación del condicional:
  $$\frac{F\quad F\rightarrow G}{G}$$
  Lo implementamos en Haskell mediante la función \texttt{(elimCond f g)}
\index{\texttt{elimCond}}
\begin{code}
elimCond :: Form -> Form -> Form
elimCond  f (Impl f1 f2) | f == f1 = f2
elimCond  (Impl f1 f2) f | f == f1 = f2
elimCond _ _                       = error "Entrada no valida para esta regla."
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> elimCond p (Impl p q)
-- q
\end{code}
\item Ejemplo: $p,p\rightarrow q, p\rightarrow ( q \rightarrow r) \vdash r $
  \begin{enumerate}
  \item $p$ \hfill \texttt{Premisa}
  \item $p\rightarrow q$ \hfill \texttt{Premisa}
  \item $p\rightarrow (q\rightarrow r)$ \hfill \texttt{Premisa}
  \item $q$ \hfill \texttt{elimCond 1 2}
  \item $q\rightarrow r$ \hfill \texttt{elimCond 1 3}
  \item $r$ \hfill \texttt{elimCond 4 5}
  \end{enumerate}

En Haskell sería

\begin{code}
-- | Ejemplo
-- >>> let f1 = p
-- >>> let f2 = Impl p q
-- >>> let f3 = Impl p (Impl q r)
-- >>> let f4 = elimCond f1 f2
-- >>> let f5 = elimCond f1 f3
-- >>> let f6 = elimCond f4 f5
-- >>> f1
-- p
-- >>> f2
-- (p⟹q)
-- >>> f3
-- (p⟹(q⟹r))
-- >>> f4
-- q
-- >>> f5
-- (q⟹r)
-- >>> f6
-- r
\end{code}
  
\end{itemize*}

\subsection{Regla de introducción del condicional}

\begin{itemize*}
\item Regla de introducción del condicional:
$$\frac{\begin{bmatrix}{F}\\{\vdots}\\{G}\end{bmatrix}}{F \to G} $$ 
Lo implementamos en Haskell mediante la función \texttt{(introCond f g)}

\index{\texttt{introCond}}
\begin{code}
introCond :: Form -> Form -> Form
introCond f g = Impl f g
\end{code}

\item Ejemplo: \framebox{$p\rightarrow q \vdash \neg q \rightarrow \neg p$}
  \begin{enumerate}
  \item $p \rightarrow q$ \hfill \texttt{Premisa}
  \item $\neg q$ \hfill \texttt{supuesto}
  \item $\neg p$ \hfill \texttt{modusTollens 1 2}
  \item $\neg q \rightarrow \neg p$ \hfill \texttt{introCond 2 3}
  \end{enumerate}

  Quedando en Haskell:

  \begin{code}
-- | Ejemplo
-- >>> let f1 = Impl p q
-- >>> let f2 = Neg q
-- >>> let f3 = modusTollens f1 f2
-- >>> let f4 = introCond f2 f3
-- >>> f1
-- (p⟹q)
-- >>> f2
-- ¬q
-- >>> f3
-- ¬p
-- >>> f4
-- (¬q⟹¬p)
\end{code}  
\end{itemize*}

\subsection{Reglas de la disyunción}

\begin{itemize*}
\item Reglas de la introducción de la disyunción:
  $$ \frac{F}{F\vee G} \text{ y } \frac{G}{F \vee G} $$
  Lo implementamos en Haskell mediante la función
  \texttt{(introDisy f g)}

\index{\texttt{introDisy}}
\begin{code}
introDisy :: Form -> Form -> Form
introDisy (Disy fs) (Disy gs) = Disy (nub (fs++gs))
introDisy (Disy fs) g = Disy (nub (fs ++ [g]))
introDisy f (Disy gs) = Disy (nub (f:gs))
introDisy f g = Disy [f,g]
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> introDisy (Disy [p,q]) r
-- (p⋁(q⋁r))
\end{code}
\item Ejemplo: \framebox{$p\vee q \vdash q \vee p$}
  \begin{enumerate}
  \item $p\vee q$ \hfill \texttt{Premisa}
  \item $p$ \hfill \texttt{supuesto}
  \item $q\vee p$ \hfill \texttt{introDisy 2 q}
  \item $q$ \hfill \texttt{supuesto}
  \item $q\vee p$ \hfill \texttt{introDisy 4 q}
  \item $q \vee p$ \hfill \texttt{elimDisy } $1,2 \rightarrow 3, 4 \rightarrow 5$ 
  \end{enumerate}
\begin{code}
-- | Ejemplo
-- >>> let f1 = Disy [p,q]
-- >>> let f2 = p
-- >>> let f3 = introDisy f2 q
-- >>> let f4 = q
-- >>> let f5 = introDisy f4 p
-- >>> f1
-- (p⋁q)
-- >>> f2
-- p
-- >>> f3
-- (p⋁q)
-- >>> f4
-- q
-- >>> f5
-- (q⋁p)
-- >>> elimDisy f1 (Impl f2 f5) (Impl f4 f5)
-- (q⋁p)
\end{code}

\item Regla de la eliminación de la disyunción:
  $$\frac{F \vee G \quad \begin{bmatrix}{F}\\{\vdots}\\{H}\end{bmatrix} \quad
    \begin{bmatrix}{G}\\{\vdots}\\{H}\end{bmatrix}}{H} $$
  Lo implementamos en Haskell mediante la función \texttt{elimDisy f1 f2 i1 i2}
\index{\texttt{elimDisy}}
\begin{code}
elimDisy :: Form -> Form -> Form -> Form 
elimDisy (Disy [f,g]) (Impl f1 i1) (Impl g1 i2) 
    | f == f1 && g == g1 && i1 == i2 = i1
    | g == f1 && f == g1 && i1 == i2 = i1
    | otherwise = error "Entrada no valida para esta regla."
\end{code}
\end{itemize*}

\subsection{Reglas de la negación}

\begin{itemize*}
  
\item Definimos la contradicción como una fórmula:

\index{\texttt{contradiccion}}
\begin{code}
contradiccion :: Form
contradiccion = Atom "⊥" []
\end{code}

\item Regla de eliminación de lo falso:
  $$ \frac{\perp}{F}$$
  Lo implementamos en Haskell mediante la función \texttt{(elimFalso f g)}

\index{\texttt{elimFalso}}
\begin{code}
elimFalso :: Form -> Form -> Form
elimFalso f g | f == contradiccion = g
              | g == contradiccion = f
\end{code}

\item Regla de eliminación de la negación;
  $$ \frac{F\quad \neg F}{\perp} $$
  Lo implementamos en Haskell mediante la función \texttt{(elimNeg f g)}

\index{\texttt{elimNeg}}
\begin{code}
elimNeg :: Form -> Form -> Form
elimNeg f g | f == (Neg g) || (Neg f) == g = contradiccion
\end{code}

\item Ejemplo
\begin{code}
-- | Ejemplo 
-- >>> elimNeg (Neg p) p
-- ⊥
\end{code}

\item Ejemplo \framebox{$\neg \vee q \vdash \rightarrow q$}:

\begin{enumerate}
\item $\neg \vee q$ \hfill \texttt{Premisa}
\item $p$ \hfill \texttt{supuesto}
\item $\neg p$ \hfill \texttt{supuesto}
\item $\perp$ \hfill \texttt{elimNeg 2 3}
\item $q$ \hfill \texttt{elimFalso 4}
\item $q$  \hfill \texttt{supuesto}
\item $q$ \hfill \texttt{elimDisy} $1,3\rightarrow 5,6\rightarrow 6$
\item $p\rightarrow q$ \hfill \texttt{introCond 2 7}
\end{enumerate}

En Haskell sería

\begin{code}
-- | Ejemplo
-- >>> let f1 = Disy [Neg p, q]
-- >>> let f2 = p
-- >>> let f3 = Neg p
-- >>> let f4 = elimNeg f2 f3
-- >>> let f5 = elimFalso f4 q
-- >>> let f6 = q
-- >>> let f7 = elimDisy f1 (Impl f3 f5) (Impl f6 f6)
-- >>> let f8 = introCond f2 f7
-- >>> f8
-- (p⟹q)
\end{code}
\end{itemize*}

\subsection{Reglas del bicondicional}
\begin{itemize*}
\item Regla de introducción del bicondicional:
  $$\frac{F \rightarrow G\quad G\rightarrow F}{F\leftrightarrow F} $$
  Lo implementamos en Haskell mediante la función \texttt{(introBicond f g)}
\begin{code}
introBicond :: Form -> Form -> Form
introBicond (Impl f1 f2) (Impl g1 g2)
    | f1 == g2 && f2 == g1 = Equiv f1 f2
\end{code}

\item Ejemplo

\begin{code}
-- | Ejemplo
-- >>> introBicond (Impl p q) (Impl q p)
-- (p⟺q)
\end{code}

\item Reglas de la eliminación del bicondicional:
  $$ \frac{F\leftrightarrow G}{F\rightarrow G} \text{ y }
  \frac{F\leftrightarrow G}{G\rightarrow F}$$
  Lo implementamos en Haskel mediante las funciones \texttt{(elimBicondI f g)}
  y \texttt{(elimBicondD f g)}
\begin{code}
elimBicondI, elimBicondD :: Form -> Form
elimBicondI (Equiv f g) = Impl f g
elimBicondD (Equiv f g) = Impl g f
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

\subsection{Regla de Reducción al absurdo}

\begin{itemize*}
\item Regla de reducción al absurdo:
  $$\frac{\begin{bmatrix}{\neg F}\\{\vdots}\\{\perp}\end{bmatrix}}{F} $$
Lo implementamos en Haskell mediante la función \texttt{(RedAbsurdo f)}

\index{\texttt{redAbsurdo}}
\begin{code}
redAbsurdo :: Form -> Form
redAbsurdo (Impl (Neg f) contradiccion) = f
\end{code}
\end{itemize*}

\subsection{Ley del tercio excluido}

\begin{itemize*}
\item Ley del tercio excluido:
 $$ \frac{}{F\vee \neg F} $$
 Lo implementamos en Haskell mediante la función \texttt{(tercExcluido f)}
\index{\texttt{tercExcluido}}
\begin{code}
tercExcluido :: Form -> Form
tercExcluido f = Disy [f,Neg f]
\end{code}
\item Ejemplo
\begin{code}
-- | Ejemplo
-- >>> tercExcluido p
-- (p⋁¬p)
\end{code}
\end{itemize*}


\subsection{Ejemplos}

\begin{itemize*}
\item Ejemplo:  \framebox{$\neg q \rightarrow \neg p \vdash p \rightarrow \neg \neg q$}

  \begin{enumerate}
  \item $\neg q \rightarrow \neg p$
  \item $p$
  \item $\neg \neg p$
  \item $\neg \neg q$
  \item $p \rightarrow \neg \neg q$
  \end{enumerate}

\begin{code}
-- | Ejemplo 1
-- >>> let f1 = Impl (Neg q) (Neg p)
-- >>> let f2 = p
-- >>> let f3 = introDNeg p
-- >>> let f4 = modusTollens f1 f3
-- >>> let f5 = introCond f2 f4
-- >>> f1
-- (¬q⟹¬p)
-- >>> f2
-- p
-- >>> f3
-- ¬¬p
-- >>> f4
-- ¬¬q
-- >>> f5
-- (p⟹¬¬q)
\end{code}
\end{itemize*}

\comentario{Idea: Definir un tipo de dato para una demostración, que muestre
el rezonamiento. Otra forma sería usar listas. Pendiente:
   Reflexionar. Abajo propuesta}

\section{Definición de razonamientos}

En esta sección se propone una aplicación directa en Haskell de las reglas antes definidas, así como un tipo de dato que represente dicha aplicación.

Para ello, definimos el tipo de dato \texttt{Razonamiento}
\begin{code}
data Razonamiento = R Int Form
\end{code}

Para su representación por pantalla

\begin{code}
instance Show Razonamiento where
    show (R n f) = show n ++ ". "++ show f 
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplo 
-- >>> R 1 p
-- 1. p
-- >>> R 1 (Impl p q)
-- 1. (p⟹q)
\end{code}

Definimos el tipo de dato \texttt{Razonamientos} para definir
una cadena de razonamiento.

\begin{code}
data Razonamientos = Rz [Razonamiento]
\end{code}

Su representación por pantalla mediante \texttt{show}

\begin{code}
instance Show Razonamientos where
    show (Rz [p]) = show p
    show (Rz (p:ps)) = show p ++ "\n" ++ show (Rz ps)
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplo
-- >>> Rz [R 1 p, R 2 q]
-- 1. p
-- 2. q
\end{code}

Definimos la función \texttt{(deduce n1 n2 f r)} que aplica la regla \texttt{f} a las fórmulas en las posiciones \texttt{n1} y \texttt{n2}, con \texttt{r} la lista de razonamientos.

\index{\texttt{deduce}}
\begin{code}
deduce :: Int -> Int -> (Form -> Form -> t) -> Razonamientos -> t
deduce n1 n2 f (Rz rz) = 
    f (aux (rz !! (n1-1))) (aux (rz !! (n2-1)))
    where
      aux (R n g) = g
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplo
-- >>> let r1 = Rz [R 1 p,R 2 (Impl p q)]
-- >>> r1
-- 1. p
-- 2. (p⟹q)
-- >>> deduce 1 2 elimCond r1
-- q
\end{code}

Se define \texttt{(deduccion n1 n2 f r)} que realiza la deducción aplicando una
regla entre las fórmulas de \texttt{r} y la añade a \texttt{r}.

\index{\texttt{deduccion}}
\begin{code}
deduccion :: Int -> Int -> (Form -> Form -> Form) 
                 -> Razonamientos -> Razonamientos
deduccion n1 n2 f (Rz rz) =  
    Rz (rz++[R ((length rz)+1) (deduce n1 n2 f (Rz  rz))])
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplo
-- >>> deduccion 1 2 elimCond (Rz [R 1 p,R 2 (Impl p q)])
-- 1. p
-- 2. (p⟹q)
-- 3. q
\end{code}

Se define la función \texttt{(premisas fs)} que construye las premisas iniciales a partir de una lista de fórmulas \texttt{fs}.

\index{\texttt{premisas}}
\begin{code}
premisas :: [Form] -> Razonamientos
premisas fs = Rz (aux 1 fs)
    where
      aux n [f] = [R n f]
      aux n (f:fs) = (R n f): aux (n+1) fs
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplo
-- >>> let premisa1 = premisas [p,Impl p q,Impl p (Impl q r)]
-- >>> let deduccion1 = deduccion 1 2 elimCond premisa1
-- >>> let deduccion2 = deduccion 1 3 elimCond deduccion1
-- >>> let deduccion3 = deduccion 4 5 elimCond deduccion2
-- >>> premisa1
-- 1. p
-- 2. (p⟹q)
-- 3. (p⟹(q⟹r))
-- >>> deduccion1
-- 1. p
-- 2. (p⟹q)
-- 3. (p⟹(q⟹r))
-- 4. q
-- >>> deduccion2
-- 1. p
-- 2. (p⟹q)
-- 3. (p⟹(q⟹r))
-- 4. q
-- 5. (q⟹r)
-- >>> deduccion3
-- 1. p
-- 2. (p⟹q)
-- 3. (p⟹(q⟹r))
-- 4. q
-- 5. (q⟹r)
-- 6. r
\end{code}


\comentario{Propuesta de tipo de dato que refleje las reglas aplicadas}

\begin{code}

data Deduccion = D Razonamiento String

instance Show Deduccion where
    show (D r str) = show r ++ "  " ++ str

data Deducciones = Ds [Deduccion]

instance Show Deducciones where
    show (Ds [d]) = show d
    show (Ds ((D (R n f) str):ds)) = 
        show (R n f) ++ "  " ++ str ++ "\n" ++ show (Ds ds)
\end{code}

\begin{code}
-- | Ejemplo
-- >>> let p1 = R 1 p
-- >>> let p2 = R 2 q
-- >>> Ds [D p1 "Premisa", D p2 "Premisa"]
-- 1. p  Premisa
-- 2. q  Premisa
\end{code}



