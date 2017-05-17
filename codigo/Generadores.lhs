\begin{code}
module Generadores where
import PFH
import Modelo
import LPH
import Dominio
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
  \texttt{liftM} & \\
  \hline
  \texttt{liftM2} &  \\
  \hline
 \end{tabular}
\end{center}


\subsubsection{Generador de Nombres}


\begin{code}
abecedario :: Nombre
abecedario = "abcdefghijklmnopqrstuvwxyz"

genLetra :: Gen Char
genLetra = elements abecedario
\end{code}

Ejemplo de generación de letras

\begin{sesion}
ghci> sample genLetra
'w'
'r'
'l'
'o'
'u'
'z'
'f'
'x'
'k'
'q'
'b'
\end{sesion}

\begin{code}
genNombre :: Gen Nombre
genNombre = liftM (take 1) (listOf1 genLetra)  
\end{code}

Se puede definir \texttt{genNombre} como sigue

\begin{code}
genNombre2 :: Gen Nombre
genNombre2 = do
  c <- elements ['a'..'z']
  return [c]
\end{code}

Ejemplo de generación de nombres

\begin{sesion}
ghci> sample genNombre2
"z"
"u"
"j"
"h"
"v"
"w"
"v"
"b"
"e"
"d"
"s"
\end{sesion}

\subsubsection{Generador de Índices}

\begin{code}
genNumero :: Gen Int
genNumero = choose (0,100)

genIndice :: Gen Indice
genIndice =  liftM (take 1) (listOf1 genNumero)
\end{code}

Ejemplo

\begin{sesion}
ghci> sample genIndice
[98]
[62]
[50]
[89]
[97]
[6]
[14]
[87]
[14]
[92]
[1]
\end{sesion}

\subsubsection{Generador de variables}

\begin{code}
generaVariable :: Gen Variable
generaVariable = liftM2 Variable (genNombre) (genIndice)

instance Arbitrary (Variable) where
    arbitrary = generaVariable
\end{code}

Ejemplo

\begin{sesion}
ghci> sample generaVariable
q10
e5
m97
n92
h15
a52
c58
s74
t30
g78
i75
\end{sesion}

\subsubsection{Generador de Fórmulas}

\begin{code}

instance Arbitrary (Formula) where
    arbitrary = sized formula
        where
          formula 0 = liftM2 Atomo genNombre (listOf generaVariable)
          formula n = oneof [liftM  Negacion generaFormula,
                             liftM2 Implica generaFormula generaFormula,
                             liftM2 Equivalente generaFormula generaFormula,
                             liftM Conjuncion (listOf generaFormula),
                             liftM Disyuncion (listOf generaFormula),
                             liftM2 ParaTodo generaVariable generaFormula,
                             liftM2 Existe   generaVariable generaFormula]
              where
                generaFormula = formula (n-1)
\end{code}

\subsubsection{Generador de Términos}
\begin{code}

instance Arbitrary (Termino) where
    arbitrary = sized termino
        where
          termino 0 = liftM Var generaVariable
          termino n = liftM2 Ter genNombre (listOf generaTermino)
              where
              generaTermino = termino (n-1)
\end{code}
