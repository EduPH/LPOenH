Comencemos un módulo en Haskell, donde escribiremos nuestros ejemplos y construiremos distintas correspondencias entre lógica y programación. 
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

 Por ejemplo, si tenemos la proposición lógica
 $$\forall a\in P. a \Rightarrow a$$

 En Haskell, dicha proposición equivale al tipo de programa 

 \begin{center}
   \texttt{f :: a -> a}
 \end{center}

 Y la prueba de dicha proposición lógica equivale a la existencia de una función con dicho tipo, en este caso, la función identidad \texttt{(id :: a -> a)}.

\vspace{3mm}
 Pensemos ahora en dirección contraria. Si tenemos la función composición \texttt{(.)} ,y preguntamos a Haskell por su tipo de dato, obtenemos:
 \begin{code}
-- >>> :t (.)
-- (.) :: (b -> c) -> (a -> b) -> a -> c
 \end{code}

 Que con cierta reflexión, no es más que la proposición lógica que afirma que
 $$\forall a,b,c.\quad  (b\Rightarrow c)\Rightarrow (a\Rightarrow b) \Rightarrow (a\Rightarrow c) $$

