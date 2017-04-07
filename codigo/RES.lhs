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

Primero definimos las funciones \texttt{(atomosC c)} y \texttt{(atomosCs cs)} que obtienen una lista de los átomos que aparecen en la cláusula o conjuntos de cláusulas \texttt{c} y \texttt{cs}, respectivamente.

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
-- >>> let c' = Cs [C [p],C [Neg p,q],C [Neg q]]
-- >>> c'
-- {{p},{¬p,q},{¬q}}
-- >>> esConsistente c'
-- False
\end{code}

\begin{Def}
  $S\models C$ si para todo modelo $I$ de $S$, $I(C)=1$. 
\end{Def}

Para su implementación en Haskell definimos la lista de las interpretaciones que son modelo de un conjunto de cláusulas mediante la función \texttt{(modelosDe cs)}

\index{\texttt{modelosDe}}

\begin{code}
modelosDe :: Clausulas -> [InterpretacionC]
modelosDe cs = [i | i <- is, i `esModeloDe` cs]
    where
      is = interPosibles cs
\end{code}

Caracterizamos cuando una cláusula es consecuencia de un conjunto de cláusulas mediante la función \texttt{(c `esConsecuenciaDe` cs)}

\index{\texttt{esConsecuenciaDe}}
\begin{code}
esConsecuenciaDe :: Clausula -> Clausulas ->  Bool
esConsecuenciaDe c cs = and [i `esModeloDe` (Cs [c]) |i <-  modelosDe cs]
\end{code}

\begin{Prop}
Sean $S_1,\dots,S_n$ formas clausales de las fórmulas $F_1,\dots,F_n$:
\begin{itemize}
\item $\{ F_1,\dots,F_n\}$ es consistente si y sólo si $S_1\cup \dots S_n$ es consistente.
\item Si $S$ es una forma clausal de $\neg G$, entonces son equivalentes:
  \begin{enumerate}
  \item $\{F_1,\dots,F_n\} \models G$.
  \item $\{F_1,\dots,F_n,\neg G\}$ es inconsistente.
  \item $S_1\cup \dots \cup S_n \cup S$ es inconsistente. 
  \end{enumerate}
\end{itemize}
\end{Prop}

\section{Demostraciones por resolución (Lógica Proposicional)}

\begin{Def}
  Sean $C_1$ una cláusula, $L$ un literal de $C_1$ y $C_2$ una cláusula que contiene el complementario de $L$. La \textbf{resolvente de $C_1$ y $C_2$ respecto de $L$} es 
  $$Res_L(C_1,C_2)=(C_1 \backslash \{L\})\cup (C_2\backslash \{L^c\}) $$
\end{Def}

Implementamos la función \texttt{(res c1 c2 l)} que calcula la resolvente de \texttt{c1} y \texttt{c2} respecto del literal \texttt{l}. 

\index{\texttt{res}}
\begin{code}
res :: Clausula -> Clausula -> Form -> Clausula
res (C fs) (C gs) l | p = C (nub (delete (Neg l) ((delete l (fs++gs)))))
                    | otherwise = 
                        error "l no pertenece a alguna de las cláusulas"
                    where
                      p = ((elem l fs) && (elem (Neg l) gs)) ||
                          ((elem l gs) && (elem (Neg l) fs))
\end{code}
\begin{nota}
  Consideraremos que \texttt{l} siempre será un átomo.
\end{nota}

\begin{code}
-- | Ejemplos 
-- >>> res (C [p,q]) (C [Neg q,r]) q
-- {p,r}
-- >>> res (C [p]) (C [Neg p]) p
-- []
\end{code}


\begin{Def}
  Sean $C_1$ y $C_2$ cláusulas, se define $Res(C_1,C_2)$ como el conjunto de las resolventes entre $C_1$ y $C_2$. 
\end{Def}

Se define la función \texttt{(ress c1 c2)} que calcula el conjunto de las resolventes de las cláusulas \texttt{c1} y \texttt{c2}.

\index{\texttt{ress}}
\begin{code}
ress :: Clausula -> Clausula -> [[Form]]
ress (C []) (C gs) = []
ress (C ((Neg f):fs)) (C gs) | elem f gs = [f,Neg f]:(ress (C fs) (C
                                                                   gs))
                             | otherwise = ress (C fs) (C gs)
ress (C (f:fs)) (C gs) | elem (Neg f) gs = [f,Neg f]:(ress (C fs) (C
                                                                   gs))
                       | otherwise = ress (C fs) (C gs)
\end{code}

Algunos ejemplos

\begin{code}
-- | Ejemplos
-- >>> ress (C [p,q,Neg r]) (C [Neg q,r]) 
-- [[q,¬q],[r,¬r]]
-- >>> ress (C [p]) (C [Neg q,r]) 
-- []
\end{code}

\section{Demostración por resolución (Lógica de primer orden)}
\comentario{Toda la sección sobre resolución está en proceso, tanto de estructuración como de programación}
\begin{code}
listaTerms (Atom _ ts) = ts
listaTerms (Neg (Atom _ ts)) = ts
listaTermsCl (C fs) = concat (map listaTerms fs)
--resolucion :: Clausula -> Clausula -> Form -> Clausula
resolucion c1 c2 f = unificadoresListas (listaTermsCl c1) (listaTermsCl c2)
\end{code}
