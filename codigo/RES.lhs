\begin{code}
module RES where
import Data.List
import LPH
import DNH
import PTLP
\end{code}

\section{Forma clausal}

Para la implementación de la resolución, primero debemos definir una serie de conceptos y construir la forma clausal.

\begin{Def}
  Un \textbf{literal} es un átomo o la negación de un átomo.
\end{Def}

\begin{Def}
  Una \textbf{cláusula} es un conjunto finito de literales.
\end{Def}

\begin{Def}
  Una \textbf{forma clausal} de una fórmula $F$ es un conjunto de cláusulas
  equivalente a $F$.
\end{Def}

\begin{Prop}
  Si $(p_1\vee \dots \vee p_n) \wedge \dots \wedge (q_1 \vee \dots \vee q_m)$ es una forma
  normal conjuntiva de la fórmula $F$. Entonces, una forma clausal de $F$ es
  $\left\{ (p_1\vee \dots \vee p_n) , \dots , (q_1 \vee \dots \vee q_m) \right\}$.
\end{Prop}

\begin{nota}
Una forma clausal de $\neg (p \wedge (q \rightarrow r))$
es $\left\{ \left\{ \neg p, q \right\},\left\{\neg p,\neg r\right\} \right\}$.
\end{nota}

\vspace{5mm}


Ahora que ya conocemos los conceptos básicos, debemos comenzar la implementación.

Definimos los tipos de dato \texttt{Clausula} y \texttt{Clausulas} para la representación una cláusula o un conjunto de ellas, respectivamente.

\begin{code}

data Clausula  = C [Form]
data Clausulas = Cs [Clausula]

\end{code}

Definimos su representación en la clase \texttt{Show}

\begin{code}
instance Show Clausula where
    show (C []) = "[]"
    show (C fs) = "{" ++  init (tail (show fs)) ++ "}"
instance Show Clausulas where
    show (Cs []) = "[]"
    show (Cs cs) = "{" ++  init (tail (show cs)) ++ "}"

\end{code}

Si consideramos la siguiente fórmula,

\begin{code}
-- | Fórmula
-- >>> Neg (Conj [p,Impl q r])
-- ¬(p⋀(q⟹r))
\end{code}

Su forma clausal sería la siguiente:

\begin{code}
-- | Forma clausal
-- >>> Cs [C [Neg p,q], C [Neg p, Neg r]]
-- {{¬p,q},{¬p,¬r}}
\end{code}

Para el cálculo de la forma clausal tenemos el siguiente algoritmo:

\parbox{130mm}{
\begin{enumerate}
\item Sea $F_1 = \exists y_1 \dots \exists y_n F$, donde $y_i$ con $i=1,\dots ,n$
  son las variables libres de F.
\item Sea $F_2$ una forma normal prenexa conjuntiva rectificada de $F_1$.
\item Sea $F_3= \texttt{ Skolem }(F_2)$, que tiene la forma
  $$\forall x_1 \dots \forall x_p [(L_1\vee \dots \vee L_n)
  \wedge \dots \wedge (M_1\vee \dots \vee M_m)]$$
\end{enumerate}}

Entonces, una forma clausal es

$$ S=
\left\{
  \left\{ L_1, \dots ,L_n \right\}
  ,\dots ,
  \left\{ M_1, \dots ,M_m \right\}
\right\} $$

  
Dada una fórmula que está en la forma del paso 3 del algoritmo, es decir,

 $$\texttt{ f } =\forall x_1 \dots \forall x_p [(L_1\vee \dots \vee L_n)
  \wedge \dots \wedge (M_1\vee \dots \vee M_m)]$$
, podemos convertirla
a su forma causal por medio de la función \texttt{(form3AC f)}

\index{\texttt{form3CAC}}
\begin{code}
form3CAC :: Form -> Clausulas
form3CAC (Disy fs) = Cs [C fs]
form3CAC p@(Atom _ _) = Cs [C [p]]
form3CAC (PTodo x f) = form3CAC f
form3CAC (Conj fs) = Cs (map disyAClau fs)
    where
      disyAClau p@(Atom _ _) = C [p]
      disyAClau p@(Neg (Atom _ _)) = C [p]
      disyAClau (Disy fs) = C fs
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplo
-- >>> Conj [p, Disy [q,r]]
-- (p⋀(q⋁r))
-- >>> form3CAC (Conj [p, Disy [q,r]])
-- {{p},{q,r}}
\end{code}

Definimos \texttt{(formaClausal f)} que transforma una fórmula \texttt{f}
a su forma clausal.

\index{\texttt{formaClausal}}
\begin{code}

formaClausal :: Form -> Clausulas
formaClausal  = form3CAC . skolem .formaNPConjuntiva
    

\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> formaClausal (Neg (Conj [p, Impl q r]))
-- {{¬p,q},{¬p,¬r}}
-- >>> formaClausal (Disy [PTodo x (Atom "P" [tx]),Ex y (Atom "Q" [ty])])
-- {{P[x0],Q[sk0[x0]]}}
-- >>> let f = Neg (PTodo x (Ex y (Neg (Equiv (Atom "P" [ty,tx]) (Neg (Atom
-- "P" [ty,ty]))))))
-- >>> let f = Neg (PTodo x (Ex y (Neg (Equiv (Atom "P" [ty,tx]) (Neg (Atom "P" [ty,ty]))))))
-- >>> formaClausal f
-- {{¬P[sk0[x0],x0],¬P[sk0[x0],sk0[x0]]},{P[sk0[x0],sk0[x0]],P[sk0[x0],x0]}}
\end{code}


Definimos la unión clausal mediante el operador infijo \texttt{(++!)}. 

\begin{code}
(++!) :: Clausulas -> Clausulas -> Clausulas
(Cs cs) ++! (Cs cs') = Cs (cs++cs')  
\end{code}

\begin{code}
-- | Ejemplo
-- >>> let c1 = formaClausal (Impl p q)
-- >>> let c2 = formaClausal (Impl q r)
-- >>> c1 ++! c2
-- {{¬p,q},{¬q,r}}
\end{code}

\section{Otras implementaciones de la forma clausal}


Primero implementemos un tipo de dato adecuado para las interpretaciones de cláusulas,
\texttt{InterpretacionC}.

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

Implementamos el valor de una cláusula \texttt{c} por una interpretación \texttt{is}
mediante la función \texttt{(valorC c is)}.

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

Implementamos el valor de un conjunto de cláusulas mediante la función \texttt{(valorCs cs is)}

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
  Una cláusula $C$ y una fórmula $F$ son \textbf{equivalentes} si $I(C)=I(F)$
  para cualquier interpretación $I$. 
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

Caracterizamos el concepto ``modelo de un conjunto de cláusulas'' mediante la función \texttt{(is `esModeloDe` cs)}.

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
esConsecuenciaDe :: Clausulas -> Clausulas ->  Bool
esConsecuenciaDe c cs = and [i `esModeloDe` c |i <-  modelosDe cs]
\end{code}

Veamos por ejemplo que si tenemos $p \rightarrow q$ y $q \rightarrow r$ se tiene como consecuencia que $p \rightarrow r$. 

\begin{code}
-- | Ejemplo 
-- >>> let c1 = formaClausal (Impl p q)
-- >>> let c2 = formaClausal (Impl q r)
-- >>> let c3 = formaClausal (Impl p r)
-- >>> esConsecuenciaDe c3 (c1++!c2)
-- True
\end{code}


\begin{Prop}
Sean $S_1,\dots,S_n$ formas clausales de las fórmulas $F_1,\dots,F_n$:
\begin{itemize}
\item $\{ F_1,\dots,F_n\}$ es consistente si y sólo si $S_1\cup \dots \cup S_n$ es consistente.
\item Si $S$ es una forma clausal de $\neg G$, entonces son equivalentes:
  \begin{enumerate}
  \item $\{F_1,\dots,F_n\} \models G$.
  \item $\{F_1,\dots,F_n,\neg G\}$ es inconsistente.
  \item $S_1\cup \dots \cup S_n \cup S$ es inconsistente. 
  \end{enumerate}
\end{itemize}
\end{Prop}

Si continuamos con el ejemplo anterior, una aplicación de esta proposición sería ver que
$$\{p\rightarrow q, q\rightarrow r \} \models p \rightarrow r \Leftrightarrow   \{\{\neg p,q\},\{\neg q,r\},\{p\},\{\neg r\}\} \text{ es inconsistente.}$$

Hemos comprobado que lo primero es cierto, es decir, que se tiene la consecuencia. Nos faltaría comprobar
que la expresión a la derecha del ``si y sólo si'' es inconsistente. Lo comprobamos a continuación.

\begin{code}
-- | Ejemplo
-- >>> let c1 = formaClausal (Impl p q)
-- >>> let c2 = formaClausal (Impl q r)
-- >>> let c3 = Cs [C [p],C [Neg r]]
-- >>> c1++!c2++!c3
-- {{¬p,q},{¬q,r},{p},{¬r}}
-- >>> esConsistente (c1++!c2++!c3)
-- False
\end{code}


\section{Resolución proposicional}

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

\subsection{Resolvente binaria}

En esta sección implementaremos la resolución binaria entre dos cláusulas. Con este objetivo definimos inicialmente la función \texttt{(listaTerms f)} que calcula los términos de una fórmula dada.

\begin{nota}
  La fórmula de entrada siempre será un literal, pues se aplicará a formas clausales.
\end{nota}

\index{\texttt{listaTerms}}
\begin{code}
listaTerms :: Form -> [Termino]
listaTerms (Atom _ ts) = ts
listaTerms (Neg (Atom _ ts)) = ts
\end{code}

Ahora calculamos la resolución entre dos cláusulas mediante la función \texttt{(resolucion c1 c2 f1 f2)}, donde \texttt{c1} y \texttt{c2} son cláusulas y, \texttt{f1} y \texttt{f2} serán fórmulas de \texttt{c1} y \texttt{c2}, respectivamente, tales que se podrá efectuar resolución entre ellas mediante la unificación adecuada.

\index{\texttt{resolucion}}
\begin{code}
resolucion :: Clausula -> Clausula -> Form -> Form -> Clausula
resolucion c1@(C fs) c2@(C gs) f1 f2 =  aux c1' c2'
    where
      sust = unificadoresListas (listaTerms f1) (listaTerms f2)
      c1' = C (sustitucionForms (head sust) fs)
      c2' = C (sustitucionForms (head sust) gs)
      aux (C ((Neg f):fs)) (C gs) | elem f gs = C (fs++(delete f gs))
                                  | otherwise = aux (C fs) (C gs)
      aux (C (f:fs)) (C gs) | elem (Neg f) gs = C (fs ++ (delete (Neg f) gs))
                            | otherwise = aux (C fs) (C gs)
\end{code}

\begin{code}
-- | Ejemplos
-- >>> let c1 = C [Neg (Atom "P" [tx, Ter "f" [tx,ty]])]
-- >>> c1
-- {¬P[x,f[x,y]]}
-- >>> let c2 = C [Atom "P" [a,tz],Neg (Atom "Q" [tz,tu])]
-- >>> c2
-- {P[a,z],¬Q[z,u]}
-- >>> resolucion c1 c2 (Neg (Atom "P" [tx, Ter "f" [tx,ty]])) (Atom "P" [a,tz]) 
-- {¬Q[f[a,y],u]}
\end{code}

Definimos un operador infijo que puede resultar útil al hacer resolución en un conjunto de cláusulas. \texttt{(!!!)} devuelve la cláusula n-ésima de un conjunto de cláusulas. 

\begin{code}
(!!!) :: Clausulas -> Int -> Clausula
(Cs cs) !!! n = cs !! n
\end{code}

\section{Resolución de primer orden}

\comentario{Pendiente de escritura}
