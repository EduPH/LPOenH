\begin{code}
module GeneradoresForm where
import PFH
import LPH
import Test.QuickCheck
import Control.Monad
\end{code}

Nuestro primer objetivo será la generación de variables. Recordemos cómo estaban definidas las variables:

\begin{sesion}
data Variable = Variable Nombre Indice
  deriving (Eq,Ord,Generic)  
\end{sesion}

Comprobamos que una variable está compuesta de un nombre y un índice.
Así que comenzamos generando el nombre y, con este fin, generamos letras al azar
del abecedario, y cada una compondrá un nombre para una variable.


\begin{code}
abecedario :: Nombre
abecedario =  ['a'..'z']

genLetra :: Gen Char
genLetra = elements abecedario
\end{code}

Podemos emplear como dijimos en la sección introductoria a los generadores
de tipos la función \texttt{generate} para generar algunas letras al azar.

\begin{sesion}
ghci> generate genLetra :: IO Char
'r'
ghci> generate genLetra :: IO Char
'p'
\end{sesion}

Con esto podemos definir el generador de nombres \texttt{genNombre}.

\begin{code}
genNombre :: Gen Nombre
genNombre = liftM (take 1) (listOf1 genLetra)  
\end{code}

Una definición alternativa a la anterior es \texttt{genNombre2} como sigue

\begin{code}
genNombre2 :: Gen Nombre
genNombre2 = do
  c <- elements ['a'..'z']
  return [c]
\end{code}

Finalmente, generemos algunos ejemplos de nombres para variables.

\begin{sesion}
ghci> generate genNombre :: IO Nombre
"i"
ghci> generate genNombre :: IO Nombre
"y"
ghci> generate genNombre2 :: IO Nombre
"y"
\end{sesion}

Una vez que tenemos los nombres de nuestras variables, podemos generar índices. En nuestro caso limitaremos los índices al rango del 0 al 100, pues no necesitamos una cantidad mayor de variables.

Definimos un generador de enteros \texttt{genNumero} en el rango requerido.

\begin{code}
genNumero :: Gen Int
genNumero = choose (0,100)
\end{code}

Y construimos el generador de índices \texttt{genIndice}.

\begin{code}
genIndice :: Gen Indice
genIndice =  liftM (take 1) (listOf1 genNumero)
\end{code}

Comprobemos que podemos tomar índices al azar.

\begin{sesion}
ghci> generate genIndice :: IO Indice
[52]
ghci> generate genIndice :: IO Indice
[70]
ghci> generate genIndice :: IO Indice
[89]
\end{sesion}

Una vez que hemos establecido generadores de los tipos abstractos que componen las variables,
podemos combinarlos en un generador de variables \texttt{generaVariable}.

\begin{code}
generaVariable :: Gen Variable
generaVariable = liftM2 Variable (genNombre) (genIndice)
\end{code}

Introducimos nuestro generador en la clase \texttt{Arbitrary}.
\begin{code}
instance Arbitrary (Variable) where
    arbitrary = generaVariable
\end{code}

Ya podemos generar variables pseudoaleatorias, comprobemos lo que obtenemos.

\begin{sesion}
ghci> generate generaVariable :: IO Variable
a94
ghci> generate generaVariable :: IO Variable
x85
ghci> generate generaVariable :: IO Variable
j56
ghci> generate generaVariable :: IO Variable
x54
ghci> generate generaVariable :: IO Variable
a82
\end{sesion}

\comentario{Faltan términos y fórmulas}
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

