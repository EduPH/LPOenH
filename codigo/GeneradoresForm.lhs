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
entre unas cuantas elegidas de la \texttt{x} a la \texttt{w}, y cada una compondrá
un nombre para una variable.


\begin{code}
vars :: Nombre
vars =  "xyzuvw"

genLetra :: Gen Char
genLetra = elements vars
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
  c <- elements vars
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

Una vez que tenemos los nombres de nuestras variables, podemos generar índices. En nuestro caso limitaremos los índices al rango del 0 al 10, pues no necesitamos una cantidad mayor de variables.

Definimos un generador de enteros \texttt{genNumero} en el rango requerido.

\begin{code}
genNumero :: Gen Int
genNumero = choose (0,10)
\end{code}

Y construimos el generador de índices \texttt{genIndice}.

\begin{code}
genIndice :: Gen Indice
genIndice =  liftM (take 1) (listOf1 genNumero)
\end{code}

Comprobemos que podemos tomar índices al azar.

\begin{sesion}
ghci> generate genIndice :: IO Indice
[2]
ghci> generate genIndice :: IO Indice
[0]
ghci> generate genIndice :: IO Indice
[9]
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
t4
ghci> generate generaVariable :: IO Variable
x5
ghci> generate generaVariable :: IO Variable
y6
ghci> generate generaVariable :: IO Variable
x4
ghci> generate generaVariable :: IO Variable
z2
\end{sesion}

Como ya vimos al definir las bases de la lógica, una vez que hemos definido las variables, el siguiente nivel es trabajar con términos.

Incluimos el tipo de dato \texttt{Termino} en la clase \texttt{Arbitrary}.
\begin{code}

instance Arbitrary (Termino) where
    arbitrary = resize 3 (sized termino)

\end{code}    

Definimos el generador de términos que tiene en cuenta el tamaño \texttt{termino n}. 
\begin{code}
termino :: (Num a, Ord a) => a -> Gen Termino
termino 0 = liftM Var generaVariable
termino n | n <=1 = liftM2 Ter genNombre (resize 3 (listOf1 (generaTermino)))
          | n > 1 = termino 1
              where
              generaTermino = termino (n-1)
\end{code}

\begin{nota}
 \texttt{resize n} redimensiona un generador para ajustarlo a una escala.
\end{nota}
\begin{nota}
  Se ha acotado tanto la dimensión del generador porque no nos compensa tener
  términos de gran cantidad de variables o con muchos términos dentros unos de otros.
\end{nota}

Generemos algunos términos que nos sirvan de ejemplo para comprobar el funcionamiento de nuestro
generador.
\begin{sesion}
ghci> generate (termino 0) :: IO Termino
z7
ghci> generate (termino 1) :: IO Termino
v[z1,u6]
ghci> generate (termino 2) :: IO Termino
x[z0,z10]
ghci> generate (termino 3) :: IO Termino
y[v2]
ghci> generate (termino 4) :: IO Termino
u[x0,z5,z9]
\end{sesion}


Para finalizar debemos implementar un generador de fórmulas

\begin{code}

instance Arbitrary (Form) where
    arbitrary = sized formula
        
formula 0 = liftM2 Atom genNombre (listOf (termino 3))
formula n = oneof [liftM  Neg generaFormula,
                   liftM2 Impl generaFormula generaFormula,
                   liftM2 Equiv generaFormula generaFormula,
                   liftM Conj (listOf generaFormula),
                   liftM Disy (listOf generaFormula),
                   liftM2 PTodo generaVariable generaFormula,
                   liftM2 Ex   generaVariable generaFormula]
              where
                generaFormula = formula (div n 4)
\end{code}

