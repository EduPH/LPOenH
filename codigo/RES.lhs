\begin{code}
module RES where
import Data.List
import LPH
import DNH
import PTLP
\end{code}

\section{Ampliación de la forma clausal}

La resolución requiere del uso de las formas clausales definidas anteriormente. Definamos algunas cuestiones:

Primero implementemos un tipo de dato adecuado para las interpretaciones de cláusulas, \texttt{InterpretacionC}.

\begin{code}
type InterpretacionC = [(Form,Int)]
\end{code}

\begin{Def}
  El \textbf{valor} de una cláusula $C$ en una interpretación $I$ es
   \begin{equation*}
    I(C)= \left\{
      \begin{array}{ll}
        1, & \text{si existe un } L\in C \text{ tal que } I(L)=1, \\
        0, & \text{en caso contrario} 
      \end{array} \right.
  \end{equation*}
\end{Def}

Implementamos el valor de una cláusula $C$ mediante la función \texttt{(valorC c is)}

\index{\texttt{valorC}}

\begin{code}
valorC :: Clausula -> InterpretacionC -> Int
valorC (C fs) is = 
    if ([1 | (f,1) <- is, elem f fs] ++
        [1 | (f,0) <- is, elem (Neg f) fs]) /= [] 
    then 1 else 0
\end{code}



\begin{Def}
  El \textbf{valor} de un conjunto de cláusulas $S$ en una interpretación $I$ es
   \begin{equation*}
    I(S)= \left\{
      \begin{array}{ll}
        1, & \text{si para toda } C\in S,I(C)=1, \\
        0, & \text{en caso contrario} 
      \end{array} \right.
  \end{equation*}
\end{Def}

Implementamos el valor de un conjunto de cláusulas mediante la función \texttt{(valorCs s is)}

\index{\texttt{valorCs}}

\begin{code}
valorCs :: Clausulas -> InterpretacionC -> Int
valorCs (Cs cs) is = 
    if (all (==1) [valorC c is | c <- cs]) then 1 else 0
\end{code}

\begin{nota}
  Cualquier interpretación de la cláusula vacía es 0.
\end{nota}

\begin{Def}
  Una cláusula $C$ y una fórmula $F$ son \textbf{equivalentes} si $I(C)=I(F)$ para cualquier interpretación $I$. 
\end{Def}

Veamos algunos ejemplos que nos ilustren lo definido hasta ahora:

\begin{code}
-- | Ejemplos
-- >>> let c = Cs [C [Neg p,p],C [Neg p,Neg r]]
-- >>> c
-- {{¬p,p},{¬p,¬r}}
-- >>> valorCs c [(p,1),(r,0)]
-- 1
-- >>> valorCs c [(p,1),(r,1)]
-- 0
\end{code}

\begin{Def}
  Una interpretación $I$ es \textbf{modelo} de un conjunto de cláusulas $S$ si $I(S)=1$. 
\end{Def}

Caracterizamos el concepto de modelo de un conjunto de cláusulas mediante la función \texttt{(is `esModeloDe` cs)}

\index{\texttt{esModeloDe}}
\begin{code}
esModeloDe :: InterpretacionC -> Clausulas -> Bool
esModeloDe is cs = valorCs cs is  == 1
\end{code}

\begin{code}
-- | Ejemplos
-- >>> let c = Cs [C [Neg p,p],C [Neg p,Neg r]]
-- >>> let is = [(p,1),(r,0)]
-- >>> is `esModeloDe` c
-- True
\end{code}

\begin{Def}
  Un conjunto de cláusulas es \textbf{consistente} si tiene modelos e \textbf{inconsistente}, en caso contrario. 
\end{Def}

Definamos una serie de funciones necesarias para determinar si un conjunto de cláusulas es consistente.

Primero definimos la función \texttt{(atomosC c)} y \texttt{(atomosCs cs)} que obtienen una lista de los átomos que aparecen en la cláusula o conjuntos de cláusulas \texttt{c} y \texttt{cs}, respectivamente.

\index{\texttt{atomosC}}

\index{\texttt{atomosCs}}

\begin{code}
atomosC :: Clausula -> [Form]
atomosC (C fs) = nub ([f | f <- fs, esAtomo f] ++ [f | (Neg f) <- fs])
    where
      esAtomo (Atom _ _) = True
      esAtomo _ = False

atomosCs :: Clausulas -> [Form]
atomosCs (Cs cs) = nub (concat [atomosC c | c <- cs])
\end{code}

A continuación, mediante la implementación de \texttt{(interPosibles cs)} obtenemos una lista de todas las posibles interpretaciones que podemos obtener de los átomos de \texttt{cs}.

\index{\texttt{interPosibles}}
\begin{code}
interPosibles :: Clausulas -> [InterpretacionC]
interPosibles = sequence . aux2 . aux1 . atomosCs
    where
      aux1 fs = [(a,b) | a <- fs, b <- [0,1]]
      aux2 [] = []
      aux2 fs = [take 2 fs] ++ (aux2 (drop 2 fs))
\end{code}

Finalmente, comprobamos con la función \texttt{(esConsistente cs)} que alguna de las interpretaciones posibles es modelo del conjunto de cláusulas. 

\index{\texttt{esConsistente}}
\begin{code}
esConsistente :: Clausulas -> Bool
esConsistente cs = or [i `esModeloDe` cs | i <- is]
    where
      is = interPosibles cs
\end{code}

Ahora, como acostumbramos, veamos algunos ejemplos de las funciones definidas.

\begin{code}
-- | Ejemplos
-- >>> let c = Cs [C [Neg p,p],C [Neg p,Neg r]]
-- >>> atomosCs c
-- [p,r]
-- >>> interPosibles c
-- [[(p,0),(r,0)],[(p,0),(r,1)],[(p,1),(r,0)],[(p,1),(r,1)]]
-- >>> esConsistente c
-- True
\end{code}
