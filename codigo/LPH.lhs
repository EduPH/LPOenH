El contenido de esta sección se encuentra en el módulo \texttt{LPH}. En él se
pretende asentar las bases de la lógica de primer orden y su implementación en
Haskell, con el objetivo de construir los cimientos para las posteriores
implementaciones de algoritmos de la lógica de primer orden en siguientes
capítulos.

\begin{code}
module LPH where
import Dominio
import Modelo
import Data.List
import Test.QuickCheck
\end{code}

Los elementos básicos de las fórmulas en la lógica de primer orden, así como en
la lógica proposicional son las variables.

Definimos un tipo de dato para las variables. Una variable estará compuesta
por:

Un \texttt{nombre}, que será una lista de caracteres.

\begin{code}
type Nombre = String
\end{code}

Un \texttt{índice}, lista de enteros.

\begin{code}
type Indice = [Int]
\end{code}

Quedando el tipo de dato \texttt{Variable}

\begin{code}
data Variable = Variable Nombre Indice
  deriving (Eq,Ord)
\end{code}

Para una visualización agradable en pantalla se define su representación en la
clase \texttt{Show}.

\begin{code}
instance Show Variable where
  show (Variable nombre [])  = nombre
  show (Variable nombre [i]) = nombre ++ show i
  show (Variable nombre is)  = nombre ++ showInts is
    where showInts []     = ""
          showInts [i]     = show i
          showInts (i:is') = show i ++ "_" ++ showInts is'
\end{code}

Mostramos algunos ejemplos de definición de variables

\begin{code}
x, y, z :: Variable
x = Variable "x" []
y = Variable "y" []
z = Variable "z" []
\end{code}

Y definimos también variables empleando índices

\begin{code}
a1, a2, a3 :: Variable
a1 = Variable "a" [1]
a2 = Variable "a" [2]
a3 = Variable "a" [3]
\end{code}

De manera que su visualización sería

\begin{sesion}
ghci> x
x
ghci> y
y
ghci> a1
a1
ghci> a2
a2
\end{sesion}

\begin{Def}
  Se dice que \texttt{F} es una \textbf{fórmula} si satisface la siguiente definición
  inductiva
  \begin{enumerate}
  \item Las variables proposicionales son fórmulas atómicas.
  \item Si $F$ y $G$ son fórmulas, entonces $\neg F$, $(F \wedge G)$,
    $(F \vee G)$, $(F \rightarrow G)$ y $(F \leftrightarrow G)$ son fórmulas.
  \end{enumerate}
\end{Def}

Se define un tipo de dato para las fórmulas lógicas de primer orden.

\begin{code}
data Formula = Atomo Nombre [Variable]
             | Igual Variable Variable
             | Negacion Formula
             | Implica Formula Formula
             | Equivalente Formula Formula
             | Conjuncion [Formula]
             | Disyuncion [Formula]
             | ParaTodo Variable Formula
             | Existe Variable Formula
     deriving (Eq,Ord)
\end{code}
   
Y se define una visualización en la clase \texttt{Show}

\begin{code}
instance Show Formula where
    show (Atomo r [])         = r
    show (Atomo r vs)         = r ++ show vs
    show (Igual t1 t2)        = show t1 ++ "≡" ++ show t2
    show (Negacion formula)   = '¬' : show formula
    show (Implica f1 f2)      = "(" ++ show f1 ++ "⟹" ++ show f2 ++ ")"
    show (Equivalente f1 f2)  = "(" ++ show f1 ++ "⟺" ++ show f2 ++ ")"
    show (Conjuncion [])      = "true"
    show (Conjuncion (f:fs))  = "(" ++ show f ++ "⋀" ++ show fs ++ ")" 
    show (Disyuncion [])      = "false"
    show (Disyuncion (f:fs))  = "(" ++ show f ++ "⋁" ++ show fs ++ ")"  
    show (ParaTodo v f)       = "∀" ++ show v ++ (' ': show f) 
    show (Existe v f)         = "∃" ++ show v ++ (' ': show f) 
\end{code}

Como ejemplo podemos representar las propiedades \texttt{reflexiva} y
\texttt{simétrica}.

\index{\texttt{reflexiva}}
\index{\texttt{simetrica}}
\begin{code}
reflexiva, simetrica :: Formula
reflexiva = ParaTodo x (Atomo "R" [x,x])
simetrica = ParaTodo x (ParaTodo y ( Atomo "R" [x,y] `Implica` 
                                     Atomo "R" [y,x]))
\end{code}

Quedando su representación por pantalla

\begin{sesion}
ghci> reflexiva
∀x R[x,x]
ghci> simetrica
∀x ∀y (R[x,y]⟹R[y,x])
\end{sesion}

\begin{Def}
  Una \textbf{estructura del lenguaje} $L$  es un par $\mathcal{I} = (\mathcal{U},I)$
  tal que
  \begin{enumerate}
  \item $\mathcal{U}$ es un conjunto no vacío, denominado universo.
  \item $I$ es una función con dominio el conjunto de símbolos propios de $L$
    $\texttt{Símbolos} \rightarrow \texttt{Símbolos}$ tal que
    \begin{itemize*}
    \item si $c$ es una constante de $L$, entonces $I(c) \in \mathcal{U}$
    \item si $f$ es un símbolo de función n--aria de $L$, entonces
      $I(f):\mathcal{U}^n \rightarrow \mathcal{U}$
    \item si $P$ es un símbolo de relación 0--aria de $L$, entonces
      $I(P)\in \left\{1,\right\}$
    \item si $R$ es un símbolo de relación n--aria de $L$, entonces
      $I(R)\subseteq \mathcal{U}^n$
    \end{itemize*}
  \end{enumerate}
\end{Def}


Definimos el tipo de dato relativo al universo

\begin{code}
type Universo a = [a] 
\end{code}

\begin{Def}
  Una \textbf{asignación} es una función que hace corresponder a cada variable
  un elemento del universo.
\end{Def}

Se define un tipo de dato para las asignaciones

\begin{code}
type Asignacion a = Variable -> a
\end{code}

Necesitamos definir una asignación para los ejemplos. En nuestro
caso, tomamos una asignación constante muy sencilla.

\begin{code}
asignacion :: a -> Entidades
asignacion v = A
\end{code}

\section{Evaluación de fórmulas}

En esta sección se pretende interpretar fórmulas. Una interpretación toma
valores para las variables proposicionales, y se evalúan en una fórmula,
determinando si la fórmula es verdadera o falsa, bajo esa interpretación.

Se definirá mediante la función \texttt{valor}.

Implementamos $s(x|d)$, mediante la función \texttt{(sustituye s x d v)}.
$s(x|d)$ viene dado por la fórmula
\begin{equation*}
\text{sustituye (s(t),x,d,v)}= \left\{
 \begin{array}{ll}
  \text{d}, & \text{si } \text{x} = \text{v} \\
  \text{s(v)}, & \text{ en caso contrario} 
\end{array} \right.
\end{equation*}
donde \texttt{s} es una aplicación que asigna un valor a una variable.

\comentario{Reformular la especificación de $s(x|d)$.}

En Haskell se expresa mediante guardas

\index{\texttt{sustituye}}
\begin{code}
sustituye :: Asignacion a -> Variable -> a -> Asignacion a
sustituye s x d v | x == v    = d 
                  | otherwise = s v
\end{code}

Esta función es auxiliar para la evaluación de fórmulas.

Un par de ejemplos de la función \texttt{(sustituye s x d v)} son
\begin{sesion}
ghci> sustituye asignacion y B z
A
ghci> sustituye asignacion y B y
B
\end{sesion}

\begin{Def}
  Una \textbf{interpretación proposicional} es una aplicación
  $I: VP \rightarrow Bool$, donde $VP$ representa el conjunto de las variables
  proposicionales.
\end{Def}

A continuación, presentamos una tabla de valores de las distintas conectivas
lógicas según las interpretaciones de \texttt{P} y \texttt{Q}. Falso lo
representamos mediante el 0, y verdadero mediante el 1.

\begin{center}
   \begin{tabular}{ | l | c | c | c | c | c | }
     \hline
     $\text{P}$   & $\text{Q}$  & $\text{P} \wedge \text{Q}$ &
     $\text{P} \vee \text{Q}$ & $\text{P} \rightarrow \text{Q}$ &
     $\text{P}\leftrightarrow  \text{Q}$  \\ \hline

      $1$ & $1$ & $1$ & $1$ & $1$ & $1$ \\ \hline
      $1$ & $0$ & $0$ & $1$ & $0$ & $0$ \\ \hline
      $0$ & $1$ & $0$ & $1$ & $1$ & $0$ \\ \hline
      $0$ & $0$ & $0$ & $0$ & $1$ & $1$\\
     \hline
   \end{tabular}
\end{center}

\begin{Def}
  Una \textbf{interpretación de una estructura del lenguaje} es un par
  $(\mathcal{I}, A)$ formado por una estructura del lenguaje y una asignación
  $A$.
\end{Def}

Definimos un tipo de dato para las interpretaciones de los símbolos de
relación.

\begin{code}
type InterpretacionR a = String -> [a] -> Bool
\end{code}

Definimos la función \texttt{(valor u i s form)} que calcula el valor de una
fórmula en un universo \texttt{u}, con una interpretación \texttt{i}, respecto de la
asignación \texttt{s}.

\index{\texttt{valor}}
\begin{code}
valor :: Eq a => 
         Universo a -> InterpretacionR a -> Asignacion a 
                    -> Formula -> Bool
valor _ i s (Atomo str vs)      = i str (map s vs)
valor _ _ s (Igual v1 v2)       = s v1 == s v2
valor u i s (Negacion f)        = not (valor u i s f)
valor u i s (Implica f1 f2)     = valor u i s f1 <= valor u i s f2
valor u i s (Equivalente f1 f2) = valor u i s f1 == valor u i s f2
valor u i s (Conjuncion fs)     = all (valor u i s) fs
valor u i s (Disyuncion fs)     = any (valor u i s) fs
valor u i s (ParaTodo v f)      = and [valor u i (sustituye s v d) f
                                      | d <- u]
valor u i s (Existe v f)        = or  [valor u i (sustituye s v d) f
                                      | d <- u]
\end{code}

Empleando las entidades y los predicados definidos en los módulos
\texttt{Dominio} y \texttt{Modelo}, establecemos un ejemplo del valor de una
interpretación en una fórmula.

Primero definimos la fórmula a interpretar
\begin{code}
formula1 :: Formula
formula1 = ParaTodo x (Disyuncion [Atomo "P" [x],Atomo "Q" [x]])
\end{code}

\begin{sesion}
ghci> formula1
∀x (P[x]⋁[Q[x]])
\end{sesion}

Una interpretación para las propiedades \texttt{P} y \texttt{Q}, es comprobar
si las plantas deben tener o no tener frutos.

\begin{code}
interpretacion1 :: String -> [Entidades] -> Bool
interpretacion1 "P" [x] = angiosperma x
interpretacion1 "Q" [x] = gimnosperma x
interpretacion1 _ _     = False
\end{code}

Una segunda interpretación es si las plantas deben ser o no, acuáticas o
terrestres.

\begin{code}
interpretacion2 :: String -> [Entidades] -> Bool
interpretacion2 "P" [x] = acuatica  x
interpretacion2 "Q" [x] = terrestre x
interpretacion2 _ _     = False
\end{code}

Tomamos como universo todas las entidades menos la que denotamos \texttt{Inespecífico}
\begin{sesion}
ghci> valor (take 26 entidades) interpretacion1 asignacion formula1
False
ghci> valor (take 26 entidades) interpretacion2 asignacion formula1
True
\end{sesion}

Por ahora siempre hemos establecido propiedades, pero podríamos haber definido
relaciones binarias, ternarias, \dots, n--arias.

\section{Términos funcionales}

En la sección anterior todos los términos han sido variables. Ahora
consideraremos cualquier término.

\begin{Def}
  Son \textbf{términos} en un lenguaje de primer orden:
  \begin{enumerate}
  \item Variables
  \item Constantes
  \item $f(t_1,\dots,t_n)$ si $t_i$ son términos $\forall i=1,\dots ,n$
  \end{enumerate}
\end{Def}

Definimos un tipo de dato para los términos que serán la base para la
definición de fórmulas en lógica de primer orden que no esté compuesta sólo por
variables.

\begin{code}
data Termino = Var Variable | Ter Nombre [Termino]
  deriving (Eq,Ord)
\end{code}

Algunos ejemplos de variables como términos

\begin{code}
tx, ty, tz :: Termino
tx = Var x
ty = Var y
tz = Var z
\end{code}

Como hemos introducido, también tratamos con constantes, por ejemplo:

\begin{code}
a, b, c, cero :: Termino
a    = Ter "a" []
b    = Ter "b" []
c    = Ter "c" []
cero = Ter "cero" []
\end{code}

Para mostrarlo por pantalla de manera comprensiva, definimos su representación.

\begin{code}
instance Show Termino where
    show (Var v)      = show v
    show (Ter str []) = str
    show (Ter str ts) = str ++ show ts
\end{code}

Los términos funcionales son representados de la forma

\begin{sesion}
ghci> Ter "f" [tx,ty]
f[x,y]
\end{sesion}

Caracterizamos las funciones mediante la función \texttt{(esVariable x)}, que
determina si un término es una variable

\index{\texttt{esVariable}}
\begin{code}
esVariable :: Termino -> Bool
esVariable (Var _) = True
esVariable _       = False
\end{code}

Por ejemplo,

\begin{sesion}
ghci> esVariable tx
True
ghci> esVariable (Ter "f" [tx,ty])
False
\end{sesion}

Ahora, creamos el tipo de dato \texttt{Form} de manera análoga a como lo
hicimos en la sección anterior considerando simplemente variables, pero en este
caso considerando cualquier término.

\begin{code}
data Form = Atom Nombre [Termino]
          | Ig Termino Termino
          | Neg Form
          | Impl Form Form
          | Equiv Form Form
          | Conj [Form]
          | Disy [Form]
          | PTodo Variable Form
          | Ex Variable Form
     deriving (Eq,Ord)
\end{code}
   
Y seguimos, análogamente a la sección enterior, definiendo la representación de
fórmulas por pantalla.

\begin{code}
instance Show Form where
    show (Atom r [])   = r
    show (Atom r ts)   = r ++ show ts
    show (Ig t1 t2)    = show t1 ++ "≡" ++ show t2
    show (Neg f)       = '¬': show f
    show (Impl f1 f2)  = "(" ++ show f1 ++ "⟹" ++ show f2 ++ ")"
    show (Equiv f1 f2) = "(" ++ show f1 ++ "⟺" ++ show f2 ++ ")"
    show (Conj [])     = "true"
    show (Conj [f])    = show f
    show (Conj (f:fs)) = "(" ++ show f ++ "⋀" ++ show (Conj fs) ++ ")" 
    show (Disy [])     = "false"
    show (Disy [f])    = show f
    show (Disy (f:fs)) = "(" ++ show f ++ "⋁" ++ show (Disy fs) ++ ")"  
    show (PTodo v f)   = "∀" ++ show v ++ (' ': show f) 
    show (Ex v f)      = "∃" ++ show v ++ (' ': show f) 
\end{code}

Algunos ejemplos de fórmulas son

\begin{code}
formula2, formula3 :: Form
formula2 = PTodo x (PTodo y (Impl (Atom "R" [tx,ty]) 
                             (Ex z (Conj [Atom "R" [tx,tz],
                                          Atom "R" [tz,ty]]))))
formula3 = Impl (Atom "R" [tx,ty])
            (Ex z (Conj [Atom "R" [tx,tz],Atom "R" [tz,ty]]))

\end{code}

Dichas funciones serán empleadas en futuros ejemplos. Su representación por
pantalla queda:

\begin{sesion}
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> formula3
(R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
\end{sesion}

Para la interpretación de los símbolos funcionales se define un nuevo tipo de
dato

\begin{code}
type InterpretacionF a = String -> [a] -> a
\end{code}

Para poder hacer las interpretaciones a las fórmulas, se necesita primero
interpretar el valor de los términos.

\begin{Def}
  Dada una estructura $\mathcal{I}=(U,I)$ de $L$ y una asignación $A$ en
  $\mathcal{I}$, se define la \textbf{función de evaluación de términos}
  $\mathcal{I}_A: Term(L) \rightarrow U$ por
  \begin{equation*}
    \mathcal{I}_A(t) = \left\{
      \begin{array}{lll}
        I(c), \text{ si } t \text{ es una constante } c \\
        A(x), \text{ si } t \text{ es una variable } x \\
        I(f)(\mathcal{I}_A(t_1),\dots ,\mathcal{I}_A(t_n)),
        \text{ si } t \text{ es } f(t_1,\dots t_n)
      \end{array} \right.
  \end{equation*}
\end{Def}

\begin{nota}
  $\mathcal{I}_A$ se lee ``el valor de $t$ en $\mathcal{I}$ respecto de $A$''.
\end{nota}

Definimos \texttt{(valorT i a t)}

\index{\texttt{valorT}}
\begin{code}
valorT :: InterpretacionF a -> Asignacion a -> Termino -> a
valorT i a (Var v)    = a v
valorT i a (Ter f ts) = i f (map (valorT i a) ts)
\end{code}

Definimos el tipo de dato \texttt{Interpretación} como un par formado por las
interpretaciones de los símbolos de relación y la de los símbolos funcionales.

\begin{code}
type Interpretacion a = (InterpretacionR a, InterpretacionF a)  
\end{code}

\begin{Def}
  Dada una estructura $\mathcal{I} = (U,I)$ de $L$ y una asignación
  $A$ sobre $\mathcal{I}$, se define la \textbf{función evaluación de fórmulas}
  $\mathcal{I}_A: Form(L) \rightarrow Bool$ por
  \begin{itemize*}
  \item Si $F$ es $t_1=t_2$,  
    $\mathcal{I}_A(F) = H_=(\mathcal{I}_A(t_1),\mathcal{I}_A(t_2)$
  \item Si $F$ es $P(t_1,\dots ,t_n)$,  
    $\mathcal{I}_A(F) = H_{I(P)}(\mathcal{I}_A(t_1), \dots ,\mathcal{I}_A(t_n))$
  \item Si $F$ es $\neg G$, 
    $\mathcal{I}_A(F) = H_{\neg}(\mathcal{I}_A(G))$
  \item Si $F$ es $G*H$, 
    $\mathcal{I}_A(F) = H_*(\mathcal{I}_A(G),\mathcal{I}_A(H))$
  \item Si $F$ es $\forall x G$,
    \begin{equation*}
      \mathcal{I}_A(F) = \left\{
      \begin{array}{ll} 
        1, \text{ si para todo } u \in U \text{ se tiene } \mathcal{I}_{A [ x / u ]} = 1 \\
        0, \text{ en caso contario}.
      \end{array} \right.
    \end{equation*}
  \item Si $F$ es $\exists x G$,
     \begin{equation*}
      \mathcal{I}_A(F) = \left\{
      \begin{array}{ll}
        1, \text{ si existe algún } u \in U \text{ tal que } 
           \mathcal{I}_{A [x / u ]} = 1 \\
        0, \text{ en caso contario}.
      \end{array} \right.
    \end{equation*}
  \end{itemize*}
\end{Def}

Definimos una función que determine el valor de una fórmula. Dicha función la
denotamos por \texttt{(valorF u (iR,iF) a f)}, en la que \texttt{u} denota el
universo, \texttt{iR} es la interpretación de los símbolos de relación,
\texttt{iF} es la interpretación de los símbolos de función, \texttt{a} la
asignación y \texttt{f} la fórmula.

\index{\texttt{valorF}}
\begin{code}
valorF :: Eq a => Universo a -> Interpretacion a -> Asignacion a 
                             -> Form -> Bool
valorF u (iR,iF) a (Atom r ts) =
  iR r (map (valorT iF a) ts)
valorF u (_,iF) a (Ig t1 t2) = 
  valorT iF a t1 == valorT iF a t2
valorF u i a (Neg g) =
  not (valorF u i a g)
valorF u i a (Impl f1 f2) =
  valorF u i a f1 <= valorF u i a f2
valorF u i a (Equiv f1 f2) =
  valorF u i a f1 == valorF u i a f2
valorF u i a (Conj fs) =
  all (valorF u i a) fs
valorF u i a (Disy fs) =
  any (valorF u i a) fs
valorF u i a (PTodo v g) = 
  and [valorF u i (sustituye a v d) g | d <- u]
valorF u i a (Ex v g)  =
  or  [valorF u i (sustituye a v d) g | d <- u]
\end{code}

Para construir un ejemplo tenemos que interpretar los elementos de una
fórmula. Definimos las fórmulas 4 y 5, aunque emplearemos en el ejemplo
sólo la \texttt{formula4}. 

\begin{code}
formula4, formula5 :: Form
formula4 = Ex x (Atom "R" [cero,tx])
formula5 = Impl (PTodo x (Atom "P" [tx])) (PTodo y (Atom "Q" [tx,ty]))
\end{code}

Sus representaciones quedan
\begin{sesion}
ghci> formula4
∃x R[cero,x]
ghci> formula5
(∀x P[x]⟹∀y Q[x,y])
\end{sesion}

En este caso tomamos como universo \texttt{U} los números naturales.
Interpretamos \texttt{R} como la desigualdad $<$. Es decir, vamos a comprobar
si es cierto que existe un número natural mayor que el 0. Por tanto, la
interpretación de los símbolos de relación es

\begin{code}
interpretacionR1 :: String -> [Int] -> Bool
interpretacionR1 "R" [x,y] = x < y  
interpretacionR1 _ _       = False
\end{code}

La interpretación de los símbolos de función es

\begin{code}
interpretacionF1 :: String -> [Int] -> Int
interpretacionF1 "cero" []    = 0
interpretacionF1 "s"    [i]   = succ i
interpretacionF1 "mas"  [i,j] = i + j
interpretacionF1 "por"  [i,j] = i * j
interpretacionF1 _ _          = 0
\end{code}

Empleamos la siguiente asignación
\begin{code}
asignacion1 :: Variable -> Int
asignacion1 _ = 0
\end{code}

Quedando el ejemplo

\begin{sesion}
ghci> valorF [0..] (interpretacionR1,interpretacionF1) asignacion1 formula4
True
\end{sesion}

\begin{nota}
  Haskell es perezoso, así que podemos utilizar un universo infinito. Haskell
  no hace cálculos innecesarios; es decir, para cuando encuentra un elemento
  que cumple la propiedad.
\end{nota}

Dada una fórmula $F$ de $L$ se tienen las siguientes definiciones:

\begin{Def}
  \begin{itemize}
  \item Un \textbf{modelo} de una fórmula \texttt{F} es una interpretación para
    la que \texttt{F} es verdadera.
  \item Una fórmula $F$ es \textbf{válida} si toda interpretación es modelo de
    la fórmula.
  \item Una fórmula $F$ es \textbf{satisfacible} si existe alguna
    interpretación para la que sea verdadera.
  \item Una fórmula es \textbf{insatisfacible} si no tiene ningún modelo.
  \end{itemize}
\end{Def}

\subsection{Generadores}

\comentario{Peniente de revisión.}

Para poder emplear el sistema de comprobación QuickCheck, necesitamos poder
generar elementos aleatorios de los tipos de datos creados hasta ahora.

\entrada{Generadores}

\subsection{Otros conceptos de la lógica de primer orden}

Las funciones \texttt{varEnTerm} y \texttt{varEnTerms} devuelven las variables
que aparecen en un término o en una lista de ellos.

\index{\texttt{varEnTerm}}
\index{\texttt{varEnTerms}}
\begin{code}
varEnTerm :: Termino -> [Variable]
varEnTerm (Var v)    = [v]
varEnTerm (Ter _ ts) = varEnTerms ts

varEnTerms :: [Termino] -> [Variable]
varEnTerms = nub . concatMap varEnTerm
\end{code}

\begin{nota}
  La función \texttt{nub xs} elimina elementos repetidos en una
  lista \texttt{xs}. Se encuentra en el paquete \texttt{Data.List}.
\end{nota}

\begin{nota}
  Se emplea un tipo de recursión cruzada entre funciones. Las funciones se
  llaman la una a la otra.
\end{nota}

Por ejemplo,

\begin{sesion}
ghci> varEnTerm tx
[x]
ghci> varEnTerms [tx,ty,tz]
[x,y,z]
\end{sesion}

La función \texttt{varEnForm} devuelve una lista de las variables que aparecen
en una fórmula.

\index{\texttt{varEnForm}}
\begin{code}
varEnForm :: Form -> [Variable]
varEnForm (Atom _ ts)   = varEnTerms ts
varEnForm (Ig t1 t2)    = nub (varEnTerm t1 ++ varEnTerm t2)
varEnForm (Neg f)       = varEnForm f
varEnForm (Impl f1 f2)  = varEnForm f1 `union` varEnForm f2
varEnForm (Equiv f1 f2) = varEnForm f1 `union` varEnForm f2
varEnForm (Conj fs)     = nub (concatMap varEnForm fs)
varEnForm (Disy fs)     = nub (concatMap varEnForm fs)
varEnForm (PTodo x f)   = nub (x : varEnForm f)
varEnForm (Ex x f)      = nub (x : varEnForm f)
\end{code}

Por ejemplo
\begin{sesion}
varEnForm formula2  ==  [x,y,z]
varEnForm formula3  ==  [x,y,z]
varEnForm formula4  ==  [x]
\end{sesion}

\begin{Def}
  Una variable es \textbf{libre} en una fórmula si no tiene ninguna aparición
  ligada a un cuantificador existencial o universal. ($\forall x, \exists x$)
\end{Def}

La función \texttt{(variablesLibres f} devuelve las variables libres de la
fórmula \texttt{f}.

\begin{code}
variablesLibres :: Form -> [Variable]
variablesLibres (Atom _ ts) =
  varEnTerms ts
variablesLibres (Ig t1 t2) = 
  varEnTerm t1 `union` varEnTerm t2
variablesLibres (Neg f) =
  variablesLibres f
variablesLibres (Impl f1 f2)  = 
  variablesLibres f1 `union` variablesLibres f2
variablesLibres (Equiv f1 f2) = 
  variablesLibres f1 `union` variablesLibres f2
variablesLibres (Conj fs) = 
  nub (concatMap variablesLibres fs)
variablesLibres (Disy fs) = 
  nub (concatMap variablesLibres fs)
variablesLibres (PTodo x f) =
  delete x (variablesLibres f)
variablesLibres (Ex x f) =
  delete x (variablesLibres f)
\end{code}

\begin{Def}
  Una variable $x$ está \textbf{ligada} en una fórmula cuando tiene una
  aparición de la forma $\forall x$ o $\exists x$.
\end{Def}

Se proponen varios ejemplos
\begin{sesion}
variablesLibres formula2  ==  []
variablesLibres formula3  ==  [x,y]
variablesLibres formula4  ==  []
\end{sesion}

\begin{Def}
  Una \textbf{fórmula abierta} es una fórmula con variables libres.
\end{Def}

La función \texttt{(formulaAbierta f)} determina si una fórmula dada es
abierta.

\index{\texttt{formulaAbierta}}
\begin{code}
formulaAbierta :: Form -> Bool
formulaAbierta = not . null . variablesLibres
\end{code}

Como acostumbramos, ponemos algunos ejemplos

\begin{sesion}
formulaAbierta formula2  ==  False
formulaAbierta formula3  ==  True
formulaAbierta formula4  ==  False
\end{sesion}
