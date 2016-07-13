El contenido de esta sección se encuentra en el módulo \texttt{LPH}, en él se
pretende dar representación a variables y fórmulas lógicas para la posterior
evaluación de las mismas.

\begin{code}
module LPH where
import Dominio
import Modelo
import Data.List
import Test.QuickCheck
\end{code}

Se define un tipo de dato para las variables.

\begin{code}
type Nombre   = String

type Indice   = [Int]

data Variable = Variable Nombre Indice
  deriving (Eq,Ord)
\end{code}

Y para su representación en pantalla

\begin{code}
instance Show Variable where
  show (Variable nombre [])  = nombre
  show (Variable nombre [i]) = nombre ++ show i
  show (Variable nombre is)  = nombre ++ showInts is
    where showInts []     = ""
          showInts [i]     = show i
          showInts (i:is') = show i ++ "_" ++ showInts is'
\end{code}

Ejemplos de definición de variables
\begin{code}
x,y,z :: Variable
x = Variable "x" []
y = Variable "y" []
z = Variable "z" []
\end{code}
Empleando índices
\begin{code}
a1,a2,a3 :: Variable
a1 = Variable "a" [1]
a2 = Variable "a" [2]
a3 = Variable "a" [3]
\end{code}
De manera que  el resultado queda
\begin{sesion}
ghci> a1
a1
\end{sesion}

A continuación se define un tipo de dato para las fórmulas

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
Y se emplea \texttt{show} para la visualización por pantalla.
\begin{code}
instance Show Formula where
    show (Atomo str [])       = str
    show (Atomo str vs)       = str ++ show vs
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
Por ejemplo expresemos la propiedad \texttt{reflexiva} y la \texttt{simétrica}
\index{\texttt{reflexiva}}
\index{\texttt{simetrica}}
\begin{code}
reflexiva, simetrica :: Formula
reflexiva = ParaTodo x (Atomo "R" [x,x])
simetrica = ParaTodo x (ParaTodo y ( Atomo "R" [x,y] `Implica` 
                                     Atomo "R" [y,x]))
\end{code}

\begin{sesion}
ghci> reflexiva
∀x R[x,x]
ghci> simetrica
∀x ∀y (R[x,y]==>R[y,x])
\end{sesion}

\section{Evaluación de fórmulas}

Implementamos $s(x|d)$,mediante la función \texttt{(sustituye s x d v)}.
$s(x|d)$ viene dado por la fórmula
\begin{equation*}
\text{sustituye (s(t),x,d,v)}= \left\{
 \begin{array}{ll}
  \text{d}, & \text{si } \text{x} = \text{v} \\
  \text{s(v)}, & \text{ en caso contrario} 
\end{array} \right.
\end{equation*}
donde \texttt{s} es una aplicación que asigna un valor a una variable.
En Haskell se expresa mediante guardas

\index{\texttt{sustituye}}
\begin{code}
sustituye :: (Variable -> a) -> Variable -> a -> Variable -> a
sustituye s x d v | x == v     = d 
                  | otherwise = s v
\end{code}

\begin{Def}
  Una asignación es una función $A: Variable \rightarrow Universo$
  que hace corresponder a cada variable un elemento del universo.
\end{Def}

Definimos una asignación arbitraria para los ejemplos
\begin{code}
asignacion :: a -> Entidades
asignacion v = A
\end{code}

Ejemplos de la función \texttt{(sustituye s x d v)}
\begin{sesion}
ghci> sustituye asignacion y B z
A
ghci> sustituye asignacion y B y
B
\end{sesion}

\begin{code}
type Universo a = [a]

type Interpretacion a = String -> [a] -> Bool   

type Asignacion a = Variable -> a
\end{code}

Definimos la función \texttt{(valor u i s form)} que calcula el valor de una
fórmula en un universo \texttt{u}, con una interpretación \texttt{i} y la
asignación \texttt{s}. Para ello vamos a definir previamente el valor de las
interpretaciones para las distintas conectivas lógicas

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

\index{\texttt{valor}}
\begin{code}
valor :: Eq a => 
         Universo a -> Interpretacion a -> Asignacion a 
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
\texttt{Dominio} y \texttt{Modelo}, establecemos un ejemplo del valor
de una interpretación en una fórmula.

Primero definimos la fórmula a interpretar
\begin{code}
formula_1 :: Formula
formula_1 = ParaTodo x (Disyuncion [Atomo "P" [x],Atomo "Q" [x]])
\end{code}

\begin{sesion}
ghci> formula_1
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

Una segunda interpretación es si las plantas deben ser o no acuáticas o
terrestres.

\begin{code}
interpretacion2 :: String -> [Entidades] -> Bool
interpretacion2 "P" [x] = acuatica  x
interpretacion2 "Q" [x] = terrestre x
interpretacion2 _ _     = False
\end{code}

Tomamos como Universo todas las entidades menos la que denotamos \texttt{Inespecífico}
\begin{sesion}
ghci> valor (take 26 entidades) interpretacion1 asignacion formula_1
False
ghci> valor (take 26 entidades) interpretacion2 asignacion formula_1
True
\end{sesion}

Por ahora siempre hemos establecido propiedades, pero podríamos haber definido
relaciones binarias, ternarias, \dots, n--arias.

\section{Términos funcionales}

En la sección anterior todos los términos han sido variables. Ahora
consideraremos funciones, entre ellas las constantes.

\begin{Def}
  Son términos en un lenguaje de primer orden:
  \begin{enumerate}
  \item Variables
  \item Constantes
  \item $f(t_1,\dots,t_n)$ si $t_i$ son términos $\forall i=1,\dots ,n$
  \end{enumerate}
\end{Def}

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

Para mostrarlo por pantalla de manera comprensiva

\begin{code}
instance Show Termino where
    show (Var v)    = show v
    show (Ter str []) = str
    show (Ter str ts) = str ++ show ts
\end{code}

Una función que puede resultar útil es \texttt{(esVariable x)}, que determina
si un término es una variable

\index{\texttt{esVariable}}
\begin{code}
esVariable :: Termino -> Bool
esVariable (Var _) = True
esVariable _       = False
\end{code}

Ahora, creamos el tipo de dato \texttt{Form} de manera análoga a como lo
hicimos en la sección anterior considerando simplemente variables, pero en este
caso considerándo términos.

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
Y seguimos con la analogía y empleamos la función \texttt{show}

\begin{code}
instance Show Form where
    show (Atom a [])   = a
    show (Atom f ts)   = f ++ show ts
    show (Ig t1 t2)    = show t1 ++ "≡" ++ show t2
    show (Neg form)    = '¬': show form
    show (Impl f1 f2)  = "(" ++ show f1 ++ "⟹" ++ show f2 ++ ")"
    show (Equiv f1 f2) = "(" ++ show f1 ++ "⟺" ++ show f2 ++ ")"
    show (Conj [])     = "true"
    show (Conj (f:fs)) = "(" ++ show f ++ "⋀" ++ show fs ++ ")" 
    show (Disy [])     = "false"
    show (Disy (f:fs)) = "(" ++ show f ++ "⋁" ++ show fs ++ ")"  
    show (PTodo v f)   = "∀" ++ show v ++ (' ': show f) 
    show (Ex v f)      = "∃" ++ show v ++ (' ': show f) 
\end{code}

Ejemplo de fórmulas

\begin{code}
formula_2, formula_3 :: Form
formula_2 = PTodo x (PTodo y (Impl (Atom "R" [tx,ty]) 
                             (Ex z (Conj [Atom "R" [tx,tz],
                                          Atom "R" [tz,ty]]))))
formula_3 = Impl (Atom "R" [tx,ty])
            (Ex z (Conj [Atom "R" [tx,tz],Atom "R" [tz,ty]]))

\end{code}
Quedando
\begin{sesion}
ghci> formula_2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀[R[z,y]]))
ghci> formula_3
(R[x,y]⟹∃z (R[x,z]⋀[R[z,y]]))
\end{sesion}

Para poder hacer las interpretaciones necesitamos primero una función auxiliar
que extienda los valores de las variables a términos. Esta función es
\texttt{(conversion s f str)}

\index{\texttt{conversion}}
\begin{code}
conversion :: (Variable -> a) -> (String -> [a] -> a) -> (Termino -> a)
conversion s f (Var v)    = s v
conversion s f (Ter str ts) = f str (map (conversion s f) ts)
\end{code}

Siguiendo la linea de la sección anterior, definimos una función que determine
el valor de una interpretación aplicada a una fórmula dada.  Dicha función la
denotamos por \texttt{(val u i f s form)}, en la que \texttt{u} denota el
universo, \texttt{i} es la interpretación de las propiedades o relaciones,
\texttt{f} es la interpretación del término funcional, \texttt{s} la
asignación, y \texttt{form} una fórmula.

\index{\texttt{val}}
\begin{code}
val :: Eq a =>
    [a] -> (String -> [a] -> Bool) -> (String -> [a] -> a)
        -> (Variable -> a)  -> Form -> Bool
val u i f s (Atom str ts) = i str (map (conversion s f) ts)
val u i f s (Ig t1 t2)    = 
    conversion s f t1 == conversion s f t2
val u i f s (Neg g)       = not (val u i f s g)
val u i f s (Impl f1 f2)  =
    not (val u i f s f1 && not (val u i f s f2))
val u i f s (Equiv f1 f2) = val u i f s f1 == val u i f s f2
val u i f s (Conj fs)     = all (val u i f s) fs
val u i f s (Disy fs)     = any (val u i f s) fs
val u i f s (PTodo v g)   = 
    and [ val u i f (sustituye s v d) g | d <- u]
val u i f s (Ex v g)      =
    or  [ val u i f (sustituye s v d) g | d <- u]
\end{code}

Veamos un ejemplo. Para ello tenemos que interpretar los elementos de una
fórmula, por ejemplo la \texttt{formula 4}.

\begin{code}
formula_4 :: Form
formula_4 = Ex x (Atom "R" [cero,tx])
\end{code}

\begin{sesion}
ghci> formula_4
∃x R[cero,x]
\end{sesion}

En este caso tomamos como universo \texttt{u} los números naturales.
Interpretamos \texttt{R} como la desigualdad $<$. Es decir, vamos a comprobar
si es cierto que existe un número natural mayor que el 0.

\begin{code}
interpretacion3:: String -> [Int] -> Bool
interpretacion3 "R" [x,y] = x < y  
interpretacion3 _ _       = False
\end{code}

Interpretamos los símbolos; es decir, las interpretaciones de la \texttt{f}
\begin{code}
interpretacionDef :: String -> [Int] -> Int
interpretacionDef "cero" []    = 0
interpretacionDef "s"    [i]   = succ i
interpretacionDef "mas"  [i,j] = i + j
interpretacionDef "por"  [i,j] = i * j
interpretacionDef _ _          = 0
\end{code}

Empleamos la asignación

\begin{code}
asignacion1 :: Variable -> Int
asignacion1 x = 0
\end{code}

Quedando el ejemplo

\begin{sesion}
ghci> val [0..] interpretacion3 interpretacionDef asignacion1 formula_4
True
\end{sesion}

\begin{description}
\item[Nota :] Haskell es perezoso, así que podemos utilizar un universo
  infinito. Haskell no hace cálculos innecesarios, es decir, para cuando
  encuentra un elemento que cumple la propiedad.
\end{description}

\subsection{Generadores}

Para poder emplear el sistema de comprobación \texttt{QuickCheck}, necesitamos
poder generar elementos aleatorios de los tipos de datos creados hasta ahora.

\entrada{Generadores}

\subsection{Funciones útiles en el manejo de fórmulas}

La función \texttt{varEnTerm} y \texttt{varEnTerms} devuelve las variables
que aparecen en un término o en una lista de ellos.

\index{\texttt{varEnTerm}}
\index{\texttt{varEnTerms}}
\begin{code}
varEnTerm :: Termino -> [Variable]
varEnTerm (Var v)    = [v]
varEnTerm (Ter str ts) = varEnTerms ts

varEnTerms :: [Termino] -> [Variable]
varEnTerms = nub . concatMap varEnTerm
\end{code}

\begin{description}
\item[Nota 1:] La función \texttt{nub xs} elimina elementos repetidos en una
  lista \texttt{xs}, se encuentra en el paquete \texttt{Data.List}.
\item[Nota 2:] Se emplea un tipo de recursión cruzada entre funciones. Las
  funciones se llaman la una a la otra.
\end{description}

Por ejemplo

\begin{sesion}
ghci> varEnTerm tx
[x]
ghci> varEnTerms [tx,ty,tz]
[x,y,z]
\end{sesion}

La función \texttt{varEnForm} devuelve una lista de las variables
que aparecen en una fórmula.
\index{\texttt{varEnForm}}
\begin{code}
varEnForm :: Form -> [Variable]
varEnForm (Atom str terms)    = varEnTerms terms
varEnForm (Ig term1 term2)    = nub (varEnTerm term1 ++ varEnTerm term2)
varEnForm (Neg form)          = varEnForm form
varEnForm (Impl form1 form2)  = nub (varEnForm form1 ++ varEnForm form2)
varEnForm (Equiv form1 form2) = nub (varEnForm form1 ++ varEnForm form2)
varEnForm (Conj forms)        = nub (concatMap varEnForm forms)
varEnForm (Disy forms)        = nub (concatMap varEnForm forms)
varEnForm (PTodo x form)      = nub (x : varEnForm form)
varEnForm (Ex x form)         = nub (x : varEnForm form)
\end{code}

Por ejemplo
\begin{sesion}
ghci> varEnForm formula_2
[x,y,z]
ghci> varEnForm formula_3
[x,y,z]
ghci> varEnForm formula_4
[x]
\end{sesion}

\begin{Def}
  Una variable es libre en una fórmula si tiene una aparición ligada a un
  cuantificador existencial o universal. ($\forall x, \exists x$)
\end{Def}

La función \texttt{variablesLibres} devuelve las variables libres de una
formula dada.

\begin{code}
variablesLibres :: Form -> [Variable]
variablesLibres (Atom str terms)    = varEnTerms terms
variablesLibres (Ig term1 term2)    = 
    nub (varEnTerm term1 ++ varEnTerm term2)
variablesLibres (Neg form)          = variablesLibres form
variablesLibres (Impl form1 form2)  = 
    nub (variablesLibres form1 ++ variablesLibres form2)
variablesLibres (Equiv form1 form2) = 
    nub (variablesLibres form1 ++ variablesLibres form2)
variablesLibres (Conj forms)        = 
    nub (concatMap variablesLibres forms)
variablesLibres (Disy forms)        = 
    nub (concatMap variablesLibres forms)
variablesLibres (PTodo x form)     = delete x (variablesLibres form)
variablesLibres (Ex x form)        = delete x (variablesLibres form)
\end{code}

Se proponen varios ejemplos
\begin{sesion}
ghci> variablesLibres formula_2
[]
ghci> variablesLibres formula_3
[x,y]
ghci> variablesLibres formula_4
[]
\end{sesion}

\begin{Def}
  Una fórmula abierta es una fórmula con variables libres.
\end{Def}

La función \texttt{formulaAbierta} determina si una fórmula dada es abierta.

\index{\texttt{formulaAbierta}}
\begin{code}
formulaAbierta :: Form -> Bool
formulaAbierta = not. null . variablesLibres
\end{code}

Como acostumbramos, ponemos algunos ejemplos

\begin{sesion}
ghci> formulaAbierta formula_2
False
ghci> formulaAbierta formula_3
True
ghci> formulaAbierta formula_4
False
\end{sesion}
