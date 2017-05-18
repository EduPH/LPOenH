\begin{code}
module Generadores where
import PFH
import Test.QuickCheck
import Control.Monad
\end{code}


\subsubsection{Teoría básica de generadores}

Cuando se pretende realizar pruebas aleatorias mediante QuickCheck, es necesario generar casos aleatorios. Dado un tipo de dato, se puede hacer miembro de la llamada clase \texttt{Arbitrary}.

\begin{sesion}
class Arbitrary a where
 arbitrary :: Gen a
\end{sesion}

\begin{nota}
\texttt{Gen a} es un generador del tipo de dato \texttt{a}.
\end{nota}

Cuando tenemos un generador de un determinado tipo de dato podemos hacerlo funcionar mediante

\begin{sesion}
generate :: Gen a -> IO a
\end{sesion}

Veamos algunos ejemplos fáciles de tipos de datos que ya pertenecen a la clase \texttt{Arbitrary}:

\begin{code}
-- >>> generate arbitrary :: IO Int
-- 28
-- >>> generate arbitrary :: IO Char
-- '\228'
-- >>> generate arbitrary :: IO [Int]
-- [5,-9,-27,15,-10,-23,20,-23,5,6,-29,-6,25,-3,-1,4,20,15,7,15]
\end{code}

Para construir generadores que dependan del tamaño, como por ejemplo los
árboles que dependen de la profundidad, empleamos \texttt{sized}:

\begin{sesion}
sized :: (Int -> Gen a) -> Gen a
\end{sesion}

Veamos un ejemplo de generadores que dependen del tamaño en los árboles
binarios. En el caso de que no tuvieramos en cuenta el tamaño, el generador podría no acabar al generar un árbol infinito. 

Primero definimos el tipo de dato abstracto del árbol binario:

\begin{code}
data Arbol a = Hoja | Nodo Int  (Arbol a) (Arbol a)
               deriving (Show,Eq)

\end{code}

Posteriormente añadimos el tipo \texttt{(Arbol a)} a la clase \texttt{Arbitrary}:

\begin{code}
instance Arbitrary a => Arbitrary (Arbol a) where
arbitrary = sized arbol
            
\end{code}

Finalmente se construye el generador de árboles:
\begin{code}
arbol 0 = return Hoja
arbol n = do
        x <- Test.QuickCheck.arbitrary 
        t1 <- subarbol
        t2 <- subarbol
        return (Nodo x t1 t2)
            where subarbol = arbol (n `div` 2)
\end{code}

A continuación, introduzcamos una serie de funciones 

\begin{center}
\begin{tabular}{  |c | l | }
  \hline
  \texttt{choose} & Escoge de manera pseudoaleatoria un elemento de un intervalo \texttt{(a,b)}. \\
  \hline
  \texttt{oneof}& Escoge de manera pseudoaleatoria un elemento de una lista. \\
  \hline
  \texttt{listOf} & Elabora una lista de elementos pseudoaleatorios de un tipo determinado. \\
  \hline
  \texttt{liftM} & Convierte una función en una mónada.\\
  \hline
  \texttt{liftM2} & Convierte una función en una mónada escaneando los argumentos \\
   & de izquierda a derecha.\\
  \hline
 \end{tabular}
\end{center}

\begin{sesion}
ghci> let g = choose (0,20)
ghci> generate g :: IO Int
14
ghci> let h =listOf g
ghci> generate h :: IO [Int]
[2,6,9,2,3,12,18,13,19,2,14,0,10,13,10,4,13,1,8]
ghci> let i = oneof [h,h]
ghci> generate i :: IO [Int]
[18,15,7,6,12,5,9,1,2,12,8,5,12,0,12,14,6,1,3]
\end{sesion}

En una futura sección se implementarán generadores de los distintos tipos de datos que se establecen para las fórmulas de la lógica,y así poder hacer comprobaciones con QuickCheck de todo aquello que implementemos.

