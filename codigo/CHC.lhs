Comencemos un módulo en Haskell, donde escribiremos nuestros ejemplos.

\begin{code}
module CHC where
import LPH 
import Data.Void
import Data.Either
\end{code}

En Haskell, podemos definir una gran diversidad de funciones que manejan tipos distintos, por ejemplo:

\begin{code}
-- >>> :t map
-- map :: (a -> b) -> [a] -> [b]
-- >>> :t curry
-- curry :: ((a, b) -> c) -> a -> b -> c
-- >>> :t elem
-- elem :: (Eq a, Foldable t) => a -> t a -> Bool
\end{code}

Por ello, cabe preguntarnos si existen funciones para todo tipo que nos podamos inventar. Ahí entra en juego la correspondencia de Curry- Howard, estableciendo las siguientes equivalencias:

\begin{itemize*}
\item Los tipos son teoremas.
\item Los programas son demostraciones.
\end{itemize*}

Lo que indica que existirá una función de un determinado tipo si dicho tipo, interpretado como una proposición lógica, es cierto. 

Mostremos en una tabla, aunque posteriormente tratemos con ejemplos y más detenimiento, las correspondencias entre elementos propios de la lógica y elementos del $\lambda -$cálculo, en concreto Haskell. 

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

 
 Saquemos una serie de conclusiones de los ejemplos y, posteriormente, tratemos los distintas entradas de la tabla anterior en secciones separadas.

\begin{itemize}
\item Dada una proposición lógica podemos inferir un tipo de dato equivalente a ella.
\item Demostrar un teorema es equivalente a encontrar una función del tipo de dato adecuado.
\comentario{Referencia a clases en Haskell}
\end{itemize}

