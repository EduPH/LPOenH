

Descubrimientos de gran interés se han realizado al estudiar la relación existente entre campos a primera vista distintos. Algunos ejemplos nombrados Philip Walder en su artículo Propositions as types son los ejes coordenados de Descartes que une geometría y álgebra, la teoría cuántica de Planck que relaciona particulas y ondas, entre otras teorías. En nuestro caso establecemos una relación entre la lógica y la computación, estableciendo ``Proposiciones como tipos''. 

Esta correspondencia fue observada en 1934 por Curry, y mejorada posteriormente por Howard en 1969. 

Comencemos un módulo en Haskell, donde escribiremos nuestros ejemplos.

\begin{code}
module CHC where
import LPH 
import Data.Void
import Data.Either
\end{code}

Como hemos dicho, el primer resultado que establecemos es:

\begin{center}
  \textit{Proposiciones como tipos.}
\end{center}

En Haskell, podemos definir una gran diversidad de funciones que manejan tipos distintos, por ejemplo:

\begin{code}
-- >>> :t map
-- map :: (a -> b) -> [a] -> [b]
-- >>> :t curry
-- curry :: ((a, b) -> c) -> a -> b -> c
-- >>> :t elem
-- elem :: (Eq a, Foldable t) => a -> t a -> Bool
\end{code}

Posteriormente, dadas las proposiciones lógicas, hay que determinar si son ciertas, es decir, si podemos demostrarlas. Se establece la siguiente relación:

\begin{center}
  \textit{Demostraciones como programas.}
\end{center}

Lo que indica que existirá una función de un determinado tipo si dicho tipo, interpretado como una proposición lógica, es cierto. 

Podemos seguir indagando, una función implementada en Haskell puede ser evaluada, lo que nos lleva a:

\begin{center}
  \textit{Simplificación de demostraciones como evaluación de programas.}
\end{center}

A cada forma de simplificar una prueba le corresponde una forma de evaluar el programa.

\vspace{3mm}

Concretemos las relaciones establecidas por la correspondencia de Curry-Howard para elementos propios de la lógica:

\begin{itemize*}
  \item La conjunción entre dos elementos $A$ y $B$ corresponde al producto cartesiano, es decir un par. Una prueba de $A\wedge B$ requiere de una prueba de $A$ y de una prueba de $B$ lo que de manera equivalente será que, dado el par $(A,B)$, un valor para dicho tipo $(A,B)$ requiere de un valor de tipo $A$ y otro tipo $B$. 

  \item La disyunción entre dos elementos $A$ y $B$ corresponde a la suma disjunta de los dos elementos. Una prueba de $A\vee B$ requiere una prueba de $A$ o una prueba de $B$. Análogamente a lo anterior, la suma disjunta consite en un valor del tipo $A$ o uno del $B$.

  \item El condicional $A\rightarrow B$ establece que dada una prueba de $A$ se infiera la prueba de $B$, y se establece una correspondencia con las funciones que dado un valor del tipo $A$ devuelven uno del $B$. 
\end{itemize*}

Si lo particularizamos en Haskell, obtenemos la siguiente tabla:

  \begin{center}
   \begin{tabular}{| l | l |}
     \hline
     \textbf{Lógica}  &  \textbf{Haskell} \\ \hline
     $\rightarrow $   & \texttt{ ->} \\ \hline
     \texttt{a}$\wedge$ \texttt{b}      & \texttt{(a,b)} \\ \hline
     \texttt{a}$\vee$\texttt{b} & \texttt{Either a b}\\  \hline
     $T$ & \texttt{()} \\ \hline
     $F$ & \texttt{Void} \\ \hline
     $\neg $ & \texttt{not} \\ \hline
     Modus ponens        & Aplicación de funciones \\ \hline
   \end{tabular}
 \end{center}
 Veamos en el siguiente ejemplo el isomorfismo de Curry-Howard, así como la interpretación que se infiere de él.
 Por ejemplo, si tenemos la proposición lógica
 $$ a \rightarrow a$$
 
 En Haskell, dicha proposición equivale al tipo de programa 

 \begin{center}
   \texttt{f :: a -> a}
 \end{center}

 Dicho tipo de dato se puede traducir como que si el tipo \texttt{a} ``está habitado'' entonces, como es evidente, \texttt{a} también lo está. Y la prueba de dicha proposición lógica equivale a la existencia de una función con dicho tipo, en este caso la función identidad \texttt{(id :: a -> a)}. Otro ejemplo sencillo puede ser la función \texttt{show}, cuyo tipo de dato si preguntamos a Haskell es

\begin{code}
-- >>> :t show
-- show :: Show a => a -> String   
\end{code}

Que no es más que la proposición lógica $(\forall a\in P. \quad a \rightarrow b)$.En este caso, $a$ es cualquier tipo que tenga la propiedad $P$, $P$ es la clase de los datos que se pueden mostrar y $b$ es el tipo de dato \texttt{String}.

 \vspace{3mm}
 Pensemos ahora en dirección contraria. Si tenemos la función composición \texttt{(.)} y preguntamos a Haskell por su tipo de dato obtenemos lo siguiente:
\begin{code}
-- >>> :t (.)
-- (.) :: (b -> c) -> (a -> b) -> a -> c
\end{code}

 Que con una ligera reflexión, no es más que la proposición lógica que afirma que
 $$\forall a,b,c\in P. \quad(b\rightarrow c)\rightarrow (a\rightarrow b) \rightarrow (a\rightarrow c) $$
