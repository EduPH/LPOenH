
Para terminar veamos algunos ejemplos entre la lógica y la
programación en Haskell, se pueden ver más ejemplo, así como análisis sobre la correspondencia en \cite{Wikibooks16}, \cite{Gonzalez-17} y \cite{HaskellWiki2010}  . Para ello, creemos un módulo que contenga
nuestro ejemplos.

\begin{code}
module CHC where
import Data.Either  
\end{code}

Vayamos escalando la montaña con mesura. Si tenemos la implicación $a \rightarrow a$, no es dificil intuir la función que la demuestra y el tipo que define la proposición en Haskell, no es más que la función \texttt{identidad}.

\begin{code}
identidad :: a -> a
identidad x = x
\end{code}

Sigamos componiendo conectivas para ir construyendo ejemplos poco a poco más complejos. La implicación $a \rightarrow b \rightarrow a \wedge b$ se vería representada en Haskell por el tipo

\begin{sesion}
a -> b -> (a, b)
\end{sesion}

Y demostrada por la existencia de una función con ese tipo, en este caso
el operador \texttt{(,)}.

\begin{sesion}
 (,) :: a -> b -> (a, b)
 (,) x y = (x,y) 
\end{sesion}

Otro ejemplo podría ser la regla de la eliminación de la conjunción por la izquierda, es decir, $a \wedge b \rightarrow a$ cuya representación y demostración ponemos a continuación.

\begin{sesion}
fst :: (a,b) -> a
fst (x,y) = x
\end{sesion}

Hasta ahora hemos demostrado distintas proposiciones encontrando la función adecuada pero, ¿qué sucede si tomamos una que no sea cierta? Por ejemplo, $a \rightarrow a \wedge b$, ¿existe alguna función con el tipo de dato \texttt{a -> (a,b)}? La respuesta es no, un alivio porque en caso contrario no sería consistente la teoría.

Procedamos ahora con la siguiente proposición $(a \rightarrow b \rightarrow c) \rightarrow (b \rightarrow a \rightarrow c) $ siendo su tipo y función demostradora los siguientes.

\begin{sesion}
flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x  
\end{sesion}

¿ Existirá alguna función con el tipo análogo a la proposición $a \wedge b \rightarrow a$? El tipo de la función buscada sería.

\begin{sesion}
Either a b -> a
\end{sesion}

Y podemos pasarlo por nuestro demostrador basado en tableros semánticos y determinar si debería existit o no una función con este tipo.

\begin{sesion}
ghci> esTeorema 5 (Impl (Disy [p,q]) q)
False
\end{sesion}

Por lo tanto, no debería y, de hecho, no existe ninguna función con el tipo buscado.

Anteriormente no hemos hablado anteriormente del análogo de la negación lógica en Haskell. Para ello, primero tenemos que añadir las siguientes líneas y así extender el lenguaje.

\begin{code}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
\end{code}

Posteriormente definimos el tipo \texttt{Not} como que para cualquier \texttt{a} se puede inferir cualquier cosa.

\begin{code}
type Not x = (forall a. x -> a)
\end{code}

Ahora podemos definir una serie de ejemplos que nos convenzan de la correspondencia.

Nuestro primer ejemplo consistirá en las leyes de deMorgan, cuya formalización matemática es:

$$\neg(A\wedge B)  \leftrightarrow (\neg A) \vee (\neg B) \text{ y } \neg (A\vee B) \leftrightarrow (\neg A) \vee (\neg B)$$

A estas proposiciones les corresponde un tipo de dato en Haskell.


\begin{nota}
  Nosotros nos limitaremos a una de las implicaciones.
\end{nota}

\begin{code}
leydeMorgan1 :: (Not a, Not b) -> Not (Either a b)
  
leydeMorgan2 :: Either (Not a) (Not b) -> Not (a,b)
\end{code}

Y podríamos demostrar dichas proposiciones pero eso será equivalente a la existencia de
un programa asociado a los tipos de datos antes señalados.

\begin{code}
leydeMorgan1 (noA, _) (Left a) = noA a
leydeMorgan1 (_, noB) (Right b) = noB b
 
leydeMorgan2 (Left noA) (a, _) = noA a
leydeMorgan2 (Right noB) (_, b) = noB b
\end{code}

Veamos un último ejemplo con motivación inversa. Si tenemos la función implementada en Haskell \texttt{curry f a b}, intentemos deducir su análogo lógico. Veamos primero su uso con unos ejemplos:

\begin{code}
-- | Ejemplos
-- >>> curry fst 2 3
-- 2
-- >>> curry fst 'a' 'b'
-- 'a'
-- >>> curry snd 'a' 'b'
-- 'b'
\end{code}

\begin{nota}
\texttt{curry} `currifica` una función, es decir, dada una función
\texttt{f} y dos elementos \texttt{a} y \texttt{b} se da la igualdad
informal \texttt{curry (f,a,b) = f(a,b)}.
\end{nota}

Una vez conocido su uso, preguntemos a Haskell cuál es su tipo:

\begin{sesion}
ghci> :t curry
curry :: ((a, b) -> c) -> a -> b -> c
\end{sesion}

Vista la respuesta de Haskell no es dificil inferir la proposición asociada,

$$((A\wedge B)\rightarrow C) \rightarrow (A \rightarrow B \rightarrow C) $$

Por lo tanto, hemos establecido de nuevo una correspondencia entre lógica y, en este caso, el lenguaje de programación funcional Haskell. 
