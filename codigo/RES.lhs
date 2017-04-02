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
    if ([1 | (f,1) <- is, elem f fs]++[1 | (f,0) <- is, 
                                       elem (Neg f) fs]) /= [] 
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

\index{\textttt{valorCs}}
\begin{code}
valorCs :: Clausulas -> InterpretacionC -> Int
valorCs (Cs cs) is = if (all (==1) [valorC c is | c <- cs]) then 1 else 0
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
-- | Ejemplo
-- >>> let c = Cs [C [Neg p,p],C [Neg p,Neg r]]
-- >>> let is = [(p,1),(r,0)]
-- >>> is `esModeloDe` c
-- True
\end{code}

\begin{Def}
  Un conjunto de cláusulas es \textbf{consistente} si tiene modelos e \textbf{inconsistente}, en caso contrario. 
\end{Def}

\begin{code}
interPosibles :: Clausulas -> [InterpretacionC]
interPosibles cs = undefined
\end{code}
