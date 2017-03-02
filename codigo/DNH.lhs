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

\index{\texttt{hacerApropiada}}
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

\index{\texttt{sustituyeVar}}
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
      f(S(t_1),\dots, S(t_n)), & \text{si $t$ es $f(t_1,\dots ,t_n)$} 
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

A continuación se introducen los tipos de datos necesarios para la definición de las reglas de la deducción natural:

\begin{code}
data Reglas = Suponer Form 
            | IntroConj Form Form 
            | ElimConjI Form  
            | ElimConjD Form  
            | ElimDobleNeg Form 
            | IntroDobleNeg Form 
            | ElimImpl Form Form 
            | MT Form Form
            | IntroImpl Form Form 
            | IntroDisyI Form Form 
            | IntroDisyD Form Form 
            | ElimDisy Form Form
            | ElimNeg Form  
            | IntroNeg Form 
            | ElimContrad Form 
            | IntroEquiv Form 
            | ElimEquivI Form
            | ElimEquivD Form 
            | ElimFalso Form
            | RedAbsurdo Form
            | TercioExcl Form
            | ElimUniv Form Sust
            | IntroUniv Sust Form
              deriving Show
\end{code}

Cuando elaboramos una deducción a partir de una serie de premisas, trabajaremos con una lista de ``cosas conocidas'' y ``cosas supuestas''. Para ello definimos el tipo de dato \texttt{Deduccion} de la siguiente forma:

\begin{code}
data Deduccion = D [Form] [Form] [Reglas]
                 deriving Show
\end{code}

Finalmente, se define como un átomo el elemento \texttt{contradicción}, pues nos será necesario en la definición de algunas reglas.

\index{\texttt{contradiccion}}
\begin{code}
contradiccion :: Form
contradiccion = Atom "⊥" []
\end{code}

Implementamos en Haskell un par de funciones auxiliares \texttt{(quita xs ys)} que elimina todos los elementos \texttt{xs} de la lista \texttt{ys}, y \texttt{(elemMap xs ys)} que determina si una lista está contenida en la otra. 

\index{\texttt{quita}}
\index{\texttt{elemMap}}
\begin{code}
quita :: [Form] -> [Form] -> [Form]
quita [] ys = ys
quita (x:xs) ys = quita xs (delete x ys)

elemMap :: [Form] -> [Form] -> Bool
elemMap xs ys = all (`elem` ys) xs
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> quita [p,q] [p,q,contradiccion]
-- [⊥]
-- >>> elemMap [p,q] [p,q,contradiccion]
-- True
-- >>> elemMap [contradiccion,q] [p,contradiccion]
-- False
\end{code}

En las posteriores subsecciones se va a definir la función \texttt{(verifica d)}, donde \texttt{d} será un elemento del tipo de dato \texttt{Deduccion}, y que pretende determinar si un proceso elaborado por deducción natural es correcto.

\begin{code}
verifica :: Deduccion -> Bool
\end{code}


Los primeros casos en la función \texttt{verifica} serán el básico, es decir, en el que determinaremos que el proceso deductivo es correcto, y la regla antes definida en el tipo de dato \texttt{Reglas} como \texttt{Suponer}, cuya función va a ser incluir una fórmula en la lista de las suposiciones. Lo implementamos en la función \texttt{verifica}. 

\begin{code}
verifica (D pr [] []) = True
verifica (D pr sp []) = error "Quedan supuestos"
verifica (D pr sp ((Suponer f):rs)) = verifica (D pr (f:sp) rs)
\end{code}

\subsection{Reglas de la conjunción}

\begin{itemize*}
\item Regla de la introducción de la conjunción:
  $$\frac{F\quad G}{F\wedge G}$$
Cuya implementación en la función \texttt{verifica} es:
\begin{code}
verifica (D pr sp ((IntroConj f g):rs)) 
    | elemMap [f,g] (pr++sp) = 
        verifica (D ((Conj [f,g]):pr) sp rs) 
    | otherwise = error "No se puede aplicar IntroConj"   
\end{code}


\item Regla de la eliminación de la conjunción:
  $$\frac{F_1 \wedge \dots \wedge F_n}{F_1} \text{ y } \frac{F_1\wedge \dots \wedge F_n}{F_n}. $$
Que se implementan de la siguiente forma:

\begin{code}
verifica (D pr sp ((ElimConjI f@(Conj (f1:fs))):rs)) 
    | elem f (pr++sp) = verifica (D (f1:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimConjI"

verifica (D pr sp ((ElimConjD f@(Conj fs)):rs)) 
    | elem f (pr++sp) = verifica (D ((last fs):pr) sp rs)
    | otherwise = error "No se puede aplicar ElimConjD"
\end{code}

\begin{nota}
  La función \texttt{error} permite mostrar un mensaje en el caso de que
  la regla sea aplicada a fórmulas que no son del tipo al que debe aplicarse.
\end{nota}

\end{itemize*}

\subsection{Reglas de eliminación del condicional}

\begin{itemize*}
\item Regla de la eliminación del condicional:
  $$\frac{F\quad F\rightarrow G}{G}$$
  

\begin{code}
verifica (D pr sp ((ElimImpl f1 form@(Impl f2 g)):rs))
    | c = verifica (D (g:pr) sp rs)
    | otherwise = error "No se puede aplicar la ElimImpl"
    where 
      c = elemMap [f1,form] (pr++sp) && f1 == f2
\end{code}
  

\item Regla de introducción del condicional:
$$\frac{\begin{bmatrix}{F}\\{\vdots}\\{G}\end{bmatrix}}{F \to G} $$ 


\begin{code}
verifica (D pr sp ((IntroImpl f g):rs))
    | elem f sp && elem g pr = 
        verifica (D ((Impl f g):pr) (delete f sp) rs)
    | otherwise = error "No se puede aplicar IntroImpl"
\end{code}

\end{itemize*}

\subsection{Reglas de la disyunción}

\begin{itemize*}
\item Reglas de la introducción de la disyunción:
  $$ \frac{F}{F\vee G} \text{ y } \frac{G}{F \vee G} $$
  

\begin{code}
verifica (D pr sp ((IntroDisyI f g):rs)) 
    | elem f (pr++sp) = verifica (D ((Disy [f,g]):pr) sp rs)
    | otherwise = error "No se puede aplicar IntroDisyI"

verifica (D pr sp ((IntroDisyD f g):rs)) 
    | elem g (pr++sp) = verifica (D ((Disy [f,g]):pr) sp rs)
    | otherwise = error "No se puede aplicar IntroDisyD"
\end{code}


\item Regla de la eliminación de la disyunción:
  $$\frac{F \vee G \quad \begin{bmatrix}{F}\\{\vdots}\\{H}\end{bmatrix} \quad
    \begin{bmatrix}{G}\\{\vdots}\\{H}\end{bmatrix}}{H} $$
  
\begin{code}
verifica (D pr sp ((ElimDisy (Disy [f,g]) h):rs)) 
    | c = verifica (D (h:pr) (quita [f,g] sp) rs)
    | otherwise = error "No se puede aplicar ElimDisy"
    where
      c= elemMap [f,g] sp 
         && elem (Conj [f,g]) pr 
         && elem h pr 
         && elem h (delete h pr)
\end{code}

\end{itemize*}

\subsection{Reglas de la negación}

\begin{itemize*}
  
\item Regla de eliminación de lo falso:
  $$ \frac{\perp}{F}$$

\begin{code}
verifica (D pr sp ((ElimFalso f):rs))
    | elem contradiccion pr = verifica (D (f:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimFalso"
\end{code}

\item Regla de eliminación de la negación
  $$ \frac{F\quad \neg F}{\perp} $$


\begin{code}
verifica (D pr sp ((ElimNeg f):rs))
    | elem f (pr++sp) && elem (Neg f) (pr++sp) = 
        verifica (D (contradiccion:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimNeg"
\end{code}

\end{itemize*}

\subsection{Reglas del bicondicional}
\begin{itemize*}
\item Regla de introducción del bicondicional:
  $$\frac{F \rightarrow G\quad G\rightarrow F}{F\leftrightarrow G} $$
  
\begin{code}
verifica (D pr sp ((IntroEquiv f1@(Impl f g)):rs))
    | elemMap [f1,Impl g f] (pr++sp) = 
        verifica (D ((Equiv f g):pr) sp rs)
    | otherwise = error "No se puede aplicar IntroEquiv"
\end{code}


\item Reglas de la eliminación del bicondicional:
  $$ \frac{F\leftrightarrow G}{F\rightarrow G} \text{ y }
  \frac{F\leftrightarrow G}{G\rightarrow F}$$
 
\begin{code}
verifica (D pr sp ((ElimEquivI f1@(Equiv f g)):rs))
    | elem f1 (pr++sp) = 
        verifica (D ((Impl f g):pr) sp rs)
    | otherwise = error "No se puede aplicar ElimEquivI"
verifica (D pr sp ((ElimEquivD f1@(Equiv f g)):rs))
    | elem f1 (pr++sp) = 
        verifica (D ((Impl g f):pr) sp rs)
    | otherwise = error "No se puede aplicar ElimEquivD"
\end{code}

\end{itemize*}

\subsection{Regla derivada de Modus Tollens(MT)}

\begin{itemize*}
\item Regla derivada de modus Tollens:
  $$\frac{F \rightarrow G\quad \neg G}{\neg F}$$
 
\begin{code}
verifica (D pr sp ((MT f1@(Impl f g) (Neg g1)):rs))
    | elemMap [f1,Neg g1] (pr++sp) && g == g1 = 
        verifica (D ((Neg f):pr) sp rs)
    | otherwise = error "No se puede aplicar MT"

\end{code}

\end{itemize*}

\subsection{Reglas de la doble negación}

\begin{itemize*}
\item Regla de eliminación de la doble negación: 
  $$\frac{\neg \neg F}{F}$$

\begin{code}
verifica (D pr sp ((ElimDobleNeg form@(Neg (Neg f))):rs))
    | elem form pr || elem form sp = verifica (D (f:pr) sp rs)
    | otherwise = error "No se puede aplicar ElimDobleNeg"
\end{code}

\item Regla de la introducción de la doble negación:
  $$\frac{F}{\neg \neg F} $$
 
\begin{code}
verifica (D pr sp ((IntroDobleNeg f):rs)) 
    | elem f pr || elem f sp = verifica (D ((Neg (Neg f)):pr) sp rs)
    | otherwise = error "No se puede aplicar la IntroDobleNeg"
\end{code}

\end{itemize*}

\subsection{Regla de Reducción al absurdo}

\begin{itemize*}
\item Regla de reducción al absurdo:
  $$\frac{\begin{bmatrix}{\neg F}\\{\vdots}\\{\perp}\end{bmatrix}}{F} $$

\begin{code}
verifica (D pr sp ((RedAbsurdo (Neg f)):rs)) 
         | elem (Neg f) sp && elem contradiccion pr =
             verifica (D (f:pr) sp rs)
         | otherwise = error "No se puede aplicar RedAbsurdo"
\end{code}
\end{itemize*}
\comentario{Qué sucede si hemos incluido contradicción previamente?}
\subsection{Ley del tercio excluido}

\begin{itemize*}
\item Ley del tercio excluido:
 $$ \frac{}{F\vee \neg F} $$

\begin{code}
verifica (D pr sp ((TercioExcl f):rs)) =
    verifica (D ((Disy [f,Neg f]):pr) sp rs)
\end{code}

\end{itemize*}


\subsection{Reglas del cuantificador universal}

\begin{itemize*}
\item Regla de eliminación del cuantificador universal:
$$\frac{\forall x F}{F[x/t]}\text{ donde } [x/t] \text{ es libre para }F$$

\begin{code}
verifica (D pr sp ((ElimUniv f@(PTodo v g) s@([(v',t)])):rs)) 
    | elem f (pr++sp) && (v==v') && elem v (variablesLibres f) = 
        verifica (D ((sustitucionForm s g):pr) sp rs)
    | otherwise = error "No se puede aplicar ElimUniv"
\end{code}

\item Regla de la introducción del cuantificador universal: 
$$\frac{\begin{bmatrix}{x_0}\\{\vdots}\\{F[x/x_0]}\end{bmatrix}}{\forall x F} $$
donde $x_0$ es una variable nueva, que no aparece fuera de la caja.
\begin{code}
verifica (D pr sp ((IntroUniv s@([(v,t)]) f):rs))
    | elem (Atom [] [t]) sp && elem f (pr++sp) = 
        verifica (D ((sustitucionForm s f):pr) (delete (Atom [] [t]) sp) rs)
    | otherwise = error "No se puede aplicar IntroUniv"
\end{code}
\end{itemize*}

\subsection{Reglas del cuantificador existencial}
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
-- | Ejemplos
-- >>> let rs = [Suponer p,IntroDobleNeg p, MT (Impl (Neg q) (Neg p))
-- (Neg (Neg p)), IntroImpl p (Neg (Neg q))]
-- >>> rs
-- [Suponer p,IntroDobleNeg p,MT (¬q⟹¬p) ¬¬p,IntroImpl p ¬¬q]
-- >>> verifica (D [Impl (Neg q) (Neg p)] [] rs)
-- True
\end{code}
\end{itemize*}



