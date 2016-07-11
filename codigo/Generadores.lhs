\begin{code}
module Generadores where
import PFH
import Modelo
import LPH
import Dominio
import PTLP
import Test.QuickCheck
import Control.Monad
\end{code}

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
Hay que solucionar problema de infinitud.
\begin{code}
generaFormula :: Gen Formula
generaFormula = oneof [liftM2 Atomo genNombre (listOf generaVariable),
                       liftM  Negacion generaFormula,
                       liftM2 Implica generaFormula generaFormula,
                       liftM2 Equivalente generaFormula generaFormula,
                       liftM Conjuncion (listOf generaFormula),
                       liftM Disyuncion (listOf generaFormula),
                       liftM2 ParaTodo generaVariable generaFormula,
                       liftM2 Existe   generaVariable generaFormula]

instance Arbitrary (Formula) where
    arbitrary = generaFormula

generaFormula2 :: Gen Formula
generaFormula2 = frequency [(5,liftM2 Atomo genNombre (listOf generaVariable)),
                       (1,liftM  Negacion generaFormula2),
                       (1,liftM2 Implica generaFormula2 generaFormula2),
                       (1,liftM2 Equivalente generaFormula2 generaFormula2),
                       (1,liftM Conjuncion (listOf generaFormula2)),
                       (0,liftM Disyuncion (listOf generaFormula2)),
                       (0,liftM2 ParaTodo generaVariable generaFormula2),
                       (0,liftM2 Existe   generaVariable generaFormula2)]
\end{code}

\subsubsection{Generador de Términos}
\begin{code}
generaTermino :: Gen Termino
generaTermino = oneof [liftM  Var generaVariable,
                       liftM2 Ter genNombre (listOf generaTermino)]

instance Arbitrary (Termino) where
    arbitrary = generaTermino
\end{code}
