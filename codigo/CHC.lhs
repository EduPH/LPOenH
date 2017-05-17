Para terminar veamos algunos ejemplos entre la lógica y la
programación en Haskell. Para ello, creemos un módulo que contenga
nuestro ejemplos.

\begin{code}
module CHC where
import Data.Either  
\end{code}

Nuestra primera correspondencia serán las leyes de deMorgan:

$$\neg(A\wedge B)=(\neg A) \vee (\neg B) $$

que en Haskell será:

\begin{code}
type Not x = (forall a. x -> a)
leydeMorgan1 :: (Not a, Not b) -> Not (Either a b)
leydeMorgan1 (noA, _) (Left a) = noA a
leydeMorgan1 (_, noB) (Right b) = noB b
 
leydeMorgan2 :: Either (Not a) (Not b) -> Not (a,b)
leydeMorgan2 (Left noA) (a, _) = noA a
leydeMorgan2 (Right noB) (_, b) = noB b
\end{code}
\comentario{En proceso. Falta completar ejemplos} 