\begin{code}
module PFH where 
import Data.List
\end{code}

\section{Introducción a Haskell}

Para hacer una introducción intuitiva a Haskell, se proponen a
una serie de funciones ejemplo.
A continuación se muestra la definición de una función en Haskell. 
\texttt{(cuadrado x)} es el cuadrado de \texttt{x}. Por ejemplo,
\begin{sesion}
ghci> cuadrado 3
9
ghci> cuadrado 4
16
\end{sesion}
La definición es
\index{\texttt{cuadrado}}
\begin{code}
cuadrado :: Int -> Int
cuadrado x = x * x
\end{code}

Definimos otra función en Haskell. \texttt{(raizCuadrada x)} es la raiz
cuadrada entera de \texttt{x}. Por ejemplo, 
\begin{sesion}
ghci> raizCuadrada 9
3
ghci> raizCuadrada 8
2
\end{sesion}

La definición es

\index{\texttt{raizCuadrada}}
\begin{code}
raizCuadrada :: Int -> Int
raizCuadrada x = last [y | y <- [1..x], y*y <= x]
\end{code}

Posteriormente, definimos funciones que determinen si un elemento \texttt{x}
cumple una cierta propiedad. Este es el caso de la propiedad 'ser divisible
por $n$', donde $n$ será un número cualquiera.

\begin{sesion}
ghci> 15 `divisiblePor` 5
True
\end{sesion}

La definición es

\index{\texttt{divisiblePor}}
\begin{code}
divisiblePor :: Int -> Int -> Bool
divisiblePor x n =  x `rem` n == 0
\end{code}

Hasta ahora hemos trabajado con los tipos de datos \texttt{Int} y
\texttt{Bool}; es decir, números y booleanos respectivamente. Pero también se
puede trabajar con otro tipo de dato como son cadenas de caracteres, que son tipo
\texttt{[Char]} o \texttt{String}. \texttt{(contieneLaLetra xs l)}
identifica si una palabra contiene una cierta letra \texttt{l} dada. Por
ejemplo,

\begin{sesion}
ghci>  "descartes" `contieneLaLetra` 'e'
True
ghci>  "topologia" `contieneLaLetra` 'm'
False
\end{sesion}

Y su definición es

\index{\texttt{contieneLaLetra}}
\begin{code}
contieneLaLetra :: String -> Char -> Bool 
contieneLaLetra [] _     = False
contieneLaLetra (x:xs) l = x == l || contieneLaLetra xs l
\end{code}

\subsection{Comprensión de listas}

Las listas son una representación de un conjunto ordenado de elementos. Dichos
elementos pueden ser de cualquier tipo, ya sean \texttt{Int}, \texttt{Bool},
\texttt{Char}, \dots Siempre y cuando todos los elementos de dicha lista
compartan tipo. En Haskell las listas se representan
\begin{sesion}
ghci> [1,2,3,4]
[1,2,3,4]  
ghci> [1..4]
[1,2,3,4]
\end{sesion}

Una lista por comprensión es parecido a su expresión como conjunto:

$$\{ x | x \in A, P(x) \} $$

Se puede leer de manera intuitiva como: "tomar aquellos $x$ del conjunto $A$
tales que cumplen una cierta propiedad $P$". En Haskell se representa
$$[x | x \leftarrow \texttt{lista}, \texttt{ condiciones que debe cumplir} ]$$

Algunos ejemplos son:
\begin{sesion}
ghci> [n | n <- [0 .. 10], even n]
[0,2,4,6,8,10]
ghci> [x | x <- ["descartes","pitagoras","gauss"], x `contieneLaLetra` 'e']
["descartes"]
\end{sesion}

\begin{nota}
  En los distintos ejemplos hemos visto que se pueden componer
  funciones ya definidas.
\end{nota}

Otro ejemplo que nos será importante es poder construir subconjuntos
de una lista.

\begin{code}
subconjuntos :: [t] -> [[t]]
subconjuntos [] = [[]]
subconjuntos (x:xs) = zss++[x:ys | ys <- zss]
    where zss = subconjuntos xs
subconjuntosTam :: Int -> [a] -> [[a]]
subconjuntosTam n xs = concat [permutations x | x <- subconjuntos xs, length x == n]
\end{code}
\subsection{Funciones map y filter}

Introducimos un par de funciones de mucha relevancia en el uso de listas en
Haskell. Son funciones que se denominan de orden superior.

La función \texttt{(map f xs)} aplica una función \texttt{f} a cada uno de
los elementos de la lista \texttt{xs}. Por ejemplo,

\begin{sesion}
ghci> map (`divisiblePor` 4) [8,12,3,9,16]
[True,True,False,False,True]
ghci> map (`div` 4) [8,12,3,9,16]
[2,3,0,2,4]
ghci> map (`div` 4) [x | x <- [8,12,3,9,16], x `divisiblePor` 4]
[2,3,4]
\end{sesion}

Dicha función está predefinida en el paquete \texttt{Data.List}, nosotros
daremos una definición denotándola con el nombre \texttt{(aplicafun f xs)}, y
su definición es

\index{\texttt{aplicafun}}
\begin{code}
aplicafun :: (a -> b) -> [a] -> [b]
aplicafun f []     = []
aplicafun f (x:xs) = f x : aplicafun f xs
\end{code}

La función \texttt{(filter p xs)} es la lista de los elementos de \texttt{xs}
que cumplen la propiedad \texttt{p}. Por ejemplo,
\begin{sesion}
ghci> filter (<5) [1,5,7,2,3]
[1,2,3]
\end{sesion}
La función \texttt{filter} al igual que la función \texttt{map} está definida
en el paquete \texttt{Data.List}, pero nosotros la denotaremos como
\texttt{(aquellosQuecumplen p xs)}. Y su definición es
\index{\texttt{aquellosQuecumplen}}
\begin{code}
aquellosQuecumplen :: (a -> Bool) -> [a] -> [a]
aquellosQuecumplen p [] = []
aquellosQuecumplen p (x:xs) | p x       = x: aquellosQuecumplen p xs
                            | otherwise = aquellosQuecumplen p xs
\end{code}
En esta última definición hemos introducido las ecuaciones por guardas,
representadas por \texttt{|}. Otro ejemplo más simple del uso de guardas es el
siguiente 
\begin{equation*}
g(x)= \left\{
 \begin{array}{ll}
  5, & \text{si } x \neq 0 \\
  0, & \text{en caso contrario} 
\end{array} \right.
\end{equation*}
Que en Haskell sería
\begin{code}
g :: Int -> Int
g x | x /= 0    = 5
    | otherwise = 0
\end{code}
  
\subsection{n-uplas}

Una n-upla es un elemento del tipo $(a_1,\dots,a_n)$ y existen una serie de funciones
para el empleo de las dos-uplas $(a_1,a_2)$. Dichas funciones están predefinidas bajo
los nombres \texttt{fst} y \texttt{snd}, y las redefinimos como \texttt{(primerElemento)}
y \texttt{(segundoElemento)} respectivamente.
\index{\texttt{primerElemento}}
\index{\texttt{segundoElemento}}
\begin{code}
primerElemento :: (a,b) -> a
primerElemento (x,_) = x
segundoElemento :: (a,b) -> b
segundoElemento (_,y) = y
\end{code}

\subsection{Conjunción, disyunción y cuantificación}

En Haskell, la conjunción está definida mediante el operador \texttt{\&\&}, y se
puede generalizar a listas mediante la función predefinida \texttt{(and xs)}
que nosotros redefinimos denotándola \texttt{(conjuncion xs)}. Su definición es
\index{\texttt{conjuncion}}
\begin{code}
conjuncion :: [Bool] -> Bool
conjuncion []     = True
conjuncion (x:xs) = x && conjuncion xs
\end{code}

Dicha función es aplicada a una lista de booleanos y ejecuta una conjunción
generalizada.

La disyunción en Haskell se representa mediante el operador \texttt{||}, y se
generaliza a listas mediante una función predefinida \texttt{(or xs)} que
nosotros redefinimos con el nombre \texttt{(disyuncion xs)}. Su definición es
\index{\texttt{disyuncion}}
\begin{code}
disyuncion :: [Bool] -> Bool
disyuncion []     = False
disyuncion (x:xs) = x || disyuncion xs
\end{code}

Posteriormente, basándonos en estas generalizaciones de operadores lógicos se
definen los siguientes cuantificadores, que están predefinidos como 
\texttt{(any p xs)} y \texttt{(all p xs)} en Haskell, y que nosotros redefinimos bajo los
nombres \texttt{(algun p xs)} y \texttt{(todos p xs)}. Se definen
\index{\texttt{algun}} \index{\texttt{todos}}
\begin{code}
algun, todos :: (a -> Bool) -> [a] -> Bool
algun p = disyuncion . aplicafun p
todos p = conjuncion . aplicafun p
\end{code}

\begin{nota}
  Hemos empleando composición de funciones para la definición de
  \texttt{(algun)} y \texttt{(todos)}. Se representa mediante \texttt{.},y
  se omite el argumento de entrada común a todas las funciones.
\end{nota}

En matemáticas, estas funciones representan los cuantificadores lógicos
$\exists$ y $\forall$, y determinan si alguno de los elementos de una lista
cumple una cierta propiedad, y si todos los elementos cumplen una determinada
propiedad respectivamente. Por ejemplo.
$$ \forall x \in  \{ 0,...,10\}  \texttt{ se cumple que } x<7. \texttt{ Es Falso } $$
En Haskell se aplicaría la función \texttt{(todos p xs)} de la siguiente forma
\begin{sesion}
ghci> todos (<7) [0..10]
False
\end{sesion}

Finalmente, definimos las funciones \texttt{(pertenece x xs)} y
\texttt{(noPertenece x xs)} 
\index{\texttt{pertenece}}
\index{\texttt{noPertenece}}
\begin{code}
pertenece, noPertenece :: Eq a => a -> [a] -> Bool
pertenece   = algun . (==)
noPertenece = todos . (/=)
\end{code}
Estas funciones determinan si un elemento \texttt{x} pertenece a una lista
\texttt{xs} o no. 

\subsection{Plegados especiales foldr y foldl}

No nos hemos centrado en una explicación de la recursión pero la hemos empleado
de forma intuitiva. En el caso de la recursión sobre listas, hay que distinguir
un caso base; es decir, asegurarnos de que tiene fin. Un ejemplo de recursión
es la función \texttt{(factorial x)}, que definimos
\index{\texttt{factorial}}
\begin{code}
factorial :: Int -> Int
factorial 0 = 1
factorial x = x*(x-1)
\end{code}
Añadimos una función recursiva sobre listas, como puede ser
\texttt{(sumaLaLista xs)}
\index{\texttt{sumaLaLista}}
\begin{code}
sumaLaLista :: Num a => [a] -> a
sumaLaLista []     = 0  
sumaLaLista (x:xs) = x + sumaLaLista xs
\end{code}  

Tras este preámbulo sobre recursión, introducimos la función 
\texttt{(foldr f z xs)} que no es más que una recursión sobre listas o plegado
por la derecha, la definimos bajo el nombre \texttt{(plegadoPorlaDerecha f z xs)}
\index{\texttt{plegadoPorlaDerecha}}
\begin{code}
plegadoPorlaDerecha :: (a -> b -> b) -> b -> [a] -> b
plegadoPorlaDerecha f z []     = z
plegadoPorlaDerecha f z (x:xs) = f x (plegadoPorlaDerecha f z xs)
\end{code}
Un ejemplo de aplicación es el producto de los elementos o la suma de los
elementos de una lista
\begin{sesion}
ghci> plegadoPorlaDerecha (*) 1 [1,2,3]
6
ghci> plegadoPorlaDerecha (+) 0 [1,2,3]
6
\end{sesion}

Un esquema informal del funcionamiento de \texttt{plegadoPorlaDerecha} es
$$ \texttt{plegadoPorlaDerecha} \ (\otimes) \ z \ [x_1,x_2,\dots , x_n] := 
   x_1 \otimes (x_2 \otimes (\cdots (x_n \otimes z) \cdots )) $$

\begin{nota}
  $\otimes$ representa una operación cualquiera.
\end{nota}

Por lo tanto, podemos dar otras definiciones para las funciones
\texttt{(conjuncion xs)} y \texttt{(disyuncion xs)}
\begin{code}
conjuncion1, disyuncion1 :: [Bool] -> Bool
conjuncion1 = plegadoPorlaDerecha (&&) True
disyuncion1 = plegadoPorlaDerecha (||) False
\end{code}
Hemos definido \texttt{plegadoPorlaDerecha}, ahora el lector ya intuirá que
\texttt{(foldl f z xs)} no es más que una función que pliega por la izquiera.
Definimos \texttt{(plegadoPorlaIzquiera f z xs)}
\index{\texttt{plegadoPorlaIzquierda}}
\begin{code}
plegadoPorlaIzquierda :: (a -> b -> a) -> a -> [b] -> a
plegadoPorlaIzquierda f z []     = z
plegadoPorlaIzquierda f z (x:xs) = plegadoPorlaIzquierda f (f z x) xs
\end{code}
De manera análoga a \texttt{foldr} mostramos un esquema informal para facilitar
la comprensión
$$ \texttt{plegadoPorlaIzquierda} \ (\otimes) \ z \ [x_1,x_2,\dots , x_n] :=
   (\cdots ((z \otimes x_1) \otimes x_2) \otimes \cdots) \otimes x_n $$

Definamos una función ejemplo como es la inversa de una lista. Está
predefinida bajo el nombre \texttt{(reverse xs)} y nosotros la redefinimos
como \texttt{(listaInversa xs)}
\index{\texttt{listaInversa}}
\begin{code}
listaInversa :: [a] -> [a]
listaInversa = plegadoPorlaIzquierda (\xs x -> x:xs) []
\end{code}
Por ejemplo
\begin{sesion}
ghci> listaInversa [1,2,3,4,5]
[5,4,3,2,1]
\end{sesion}  
Podríamos comprobar por ejemplo si la frase 
\texttt{'Yo dono rosas, oro no doy'} es un palíndromo
\begin{sesion}
ghci> listaInversa "yodonorosasoronodoy"
"yodonorosasoronodoy"
ghci> listaInversa "yodonorosasoronodoy" == "yodonorosasoronodoy"
True
\end{sesion}

\subsection{Teoría de tipos}

\subsubsection{Notación $\lambda$}

Cuando hablamos de notación lambda simplemente nos referimos  a
expresiones del tipo \texttt{$\backslash$x -> x+2}. La notación viene del
\emph{$\lambda$ Calculus} y se escribiría \texttt{$\lambda$x. x+2}.  Los
diseñadores de Haskell tomaron el símbolo $\backslash$ debido a su parecido con
$\lambda$ y por ser fácil y rápido de teclear. Una función ejemplo es
\texttt{(divideEntre2 xs)} \index{\texttt{divideEntre2}}
\begin{code}
divideEntre2 :: Fractional b => [b] -> [b]
divideEntre2 xs = map (\x -> x/2) xs
\end{code}
Para una información más amplia recomiendo consultar (\cite{Serrano-14})

\subsubsection{Representación de un dominio de entidades}

\begin{Def}
  Un \textbf{dominio de entidades} es un conjunto de individuos cuyas propiedades
  son objeto de estudio para una clasificación
\end{Def}

Construimos un ejemplo de un dominio de entidades compuesto por las letras del
abecedario, declarando el tipo de dato \texttt{Entidades} contenido en el módulo
\texttt{Dominio}
\entrada{Dominio}

\subsection{Generador de tipos en Haskell: Descripción de funciones}

En esta sección se introducirán y describirán funciones útiles en la generación
de ejemplos en tipos de datos abstractos. Estos generadores son útiles
para las comprobación de propiedades con QuickCheck
