\begin{code}
{-# LANGUAGE DeriveGeneric #-}
module PTLP where
import LPH
import DNH
import Data.List
import Test.QuickCheck -- Para ejemplos
import Generadores     -- Para ejemplos
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty 
\end{code}


\section{Unificación}

\begin{Def}
  Un \textbf{unificador} de dos términos $t_1$ y $t_2$ es una sustitución $S$ tal que
  $S(t_1) = S(t_2)$.
\end{Def}

\begin{code}
unificadoresTerminos :: Termino -> Termino -> [Sust]
unificadoresTerminos (Var x) (Var y)   
  | x == y    = [identidad]
  | otherwise = [[(x,Var y)]]
unificadoresTerminos (Var x) t =
  [[(x,t)] | x `notElem` varEnTerm t]
unificadoresTerminos t (Var y) =
  [[(y,t)] | y `notElem` varEnTerm t]
unificadoresTerminos (Ter f ts) (Ter g rs) = 
  [u | f == g, u <- unificadoresListas ts rs]
\end{code}

El valor de \texttt{(unificadoresListas ts rs)} es un unificador de las listas
de términos \texttt{ts} y \texttt{rs}; es decir, una sustitución \texttt{s} tal
que si \texttt{ts = [t1,...,tn]} y \texttt{rs = [r1,...,rn]} entonces
\texttt{s(t1) = s(r1)}, \dots, \texttt{s(tn) = s(rn)}.

\begin{code}
unificadoresListas :: [Termino] -> [Termino] -> [Sust]
unificadoresListas [] [] = [identidad]
unificadoresListas [] _  = []
unificadoresListas _ []  = []
unificadoresListas (t:ts) (r:rs) = 
  [composicion u1 u2
  | u1 <- unificadoresTerminos t r
  , u2 <- unificadoresListas (susTerms u1 ts) (susTerms u1 rs)]   
\end{code}

Por ejemplo,

\begin{sesion}
unificadoresListas [tx] [ty]  ==  [[(x,y)]]
unificadoresListas [tx] [tx]  ==  [[]]
\end{sesion}


\section{Skolem}

\subsection{Formas normales}
\begin{Def}
  Una fórmula está en \textbf{forma normal conjuntiva} si es una conjunción de
  disyunciones de literales.
  $$(p_1\vee \dots \vee p_n) \wedge \dots \wedge (q_1 \vee \dots \vee q_m)$$
\end{Def}

\begin{nota}
La forma normal conjuntiva es propia de la lógica proposicional. Por ello las fórmulas
aquí definidas sólo se aplicaran a fórmulas sin cuantificadores.
\end{nota}

Definimos la función \texttt{(enFormaNC f)} para determinar si una fórmula
está en su forma normal conjuntiva.

\index{\texttt{enFormaNC}}
\begin{code}
enFormaNC :: Form -> Bool
enFormaNC (Atom _ _) = True
enFormaNC (Conj fs) = and [(literal f) || (esConj f) | f <- fs]
    where
      esConj (Disy fs) = all (literal) fs
      esConj _ = False
enFormaNC _ = False
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplos
-- >>> enFormaNC (Conj [p, Disy [q,r]])             
-- True
-- >>> enFormaNC (Conj [Impl p r, Disy [q, Neg r]]) 
-- False
-- >>> enFormaNC (Conj [p, Disy [q, Neg r]])        
-- True
\end{code}

Aplicando a una fórmula $F$ el siguiente algoritmo se obtiene
una forma normal conjuntiva de $F$.

\begin{enumerate*}
\item Eliminar los bicondicionales usando la equivalencia
  $$ A \leftrightarrow B \equiv (A \rightarrow B) \wedge (B \rightarrow A)$$
\item Eliminar los condicionales usando la equivalencia
  $$ A \rightarrow B \equiv \neg A \vee B  $$
\item Interiorizar las negaciones usando las equivalencias
  $$ \neg (A \wedge B) \equiv \neg A \vee \neg B$$
  $$ \neg (A \vee B) \equiv \neg A \wedge \neg B$$
  $$ \neg \neg A \equiv A $$
\item Interiorizar las disyunciones usando las equivalencias
  $$ A\vee (B \wedge C) \equiv (A \vee B) \wedge (A \vee C)  $$
  $$ (A \wedge B) \vee C \equiv (A \vee C) \wedge (B \vee C) $$
\end{enumerate*}

Implementamos estos pasos en Haskell

Definimos la función \texttt{(elimImpEquiv f)}, para obtener fórmulas
equivalentes sin equivalencias ni implicaciones.

\index{\texttt{elimImpEquiv}}
\begin{code}
elimImpEquiv :: Form -> Form
elimImpEquiv (Atom f xs) =
  Atom f xs
elimImpEquiv (Ig t1 t2) =
  Ig t1 t2
elimImpEquiv (Equiv f1 f2) =
  Conj [elimImpEquiv (Impl f1 f2),
        elimImpEquiv (Impl f2 f1)]
elimImpEquiv (Impl f1 f2) =
  Disy [Neg (elimImpEquiv f1), (elimImpEquiv f2)]
elimImpEquiv (Neg f) =
  Neg (elimImpEquiv f)
elimImpEquiv (Disy fs) =
  Disy (map elimImpEquiv fs)
elimImpEquiv (Conj fs) =
  Conj (map elimImpEquiv fs)
elimImpEquiv (Ex x f) = 
    Ex x (elimImpEquiv f)
elimImpEquiv (PTodo x f) = 
    PTodo x (elimImpEquiv f)
\end{code}

\begin{nota}
  Se aplica a fórmulas con cuantificadores pues la función será
  empleada en la sección de la forma de skolem.
\end{nota}

Por ejemplo,

\begin{code}
-- | Ejemplo
-- >>> elimImpEquiv (Neg (Conj [p, Impl q r]))
-- ¬(p⋀(¬q⋁r))
\end{code}

Interiorizamos las negaciones mediante la función \texttt{(interiorizaNeg f)}.

  
\index{\texttt{interiorizaNeg}}
\begin{code}
interiorizaNeg :: Form -> Form 
interiorizaNeg p@(Atom f xs) = p
interiorizaNeg (Equiv f1 f2) = 
    Equiv (interiorizaNeg f1) (interiorizaNeg f2)
interiorizaNeg (Impl f1 f2) = Impl (interiorizaNeg f1) (interiorizaNeg f2)
interiorizaNeg (Neg (Disy fs)) = Conj (map (interiorizaNeg) (map (Neg) fs))
interiorizaNeg (Neg (Conj fs)) = Disy (map (interiorizaNeg) (map (Neg) fs))
interiorizaNeg (Neg (Neg f)) = interiorizaNeg f
interiorizaNeg (Neg f) = Neg (interiorizaNeg f)
interiorizaNeg (Disy fs) = Disy (map interiorizaNeg fs)
interiorizaNeg (Conj fs) = Conj (map interiorizaNeg fs)

\end{code}

Definimos \texttt{(interiorizaDisy f)} para interiorizar las disyunciones

\begin{code}
interiorizaDisy :: Form -> Form
interiorizaDisy (Disy fs)  
    | all (literal) fs = Disy fs
    | otherwise =
        Conj (map (aux2) (map (Disy) (concat (aux [ aux1 f | f <- fs]))))
            where
              aux [] = []
              aux (xs:xss) = map (combina xs) xss ++ aux xss
              aux1 p | literal p = [p]
              aux1 (Conj xs) = xs
              aux1 (Disy xs) = xs
              combina [] ys = []
              combina xs [] = []
              combina xs ys = [[x,y] | x <- xs, y <- ys]
              aux2 f | enFormaNC f = f
                     | otherwise = interiorizaDisy f
                                                          
interiorizaDisy f = f
\end{code}


\begin{nota}
  Explicación de las funciones auxiliares
  \begin{itemize*}
  \item La función \texttt{aux} aplica la función \texttt{combina}
    las listas de las conjunciones.
  \item La función \texttt{aux1} toma las listas de las conjunciones,
    construye una lista de un literal o unifica disyunciones.
  \item La función \texttt{combina xs ys} elabora listas de dos elementos
    de las listas \texttt{xs} e \texttt{ys}.
  \item La función \texttt{aux2} itera para interiorizar todas las disyunciones.
  \end{itemize*}
  
\end{nota}

Debido a la representación que hemos elegido, pueden darse conjunciones
de conjunciones, lo cual no nos interesa. Por ello, definimos \texttt{unificacionConjuncion}
que extrae la conjunción al exterior.

\index{\texttt{unificaConjuncion}}
\begin{code}
unificaConjuncion :: Form -> Form
unificaConjuncion p@(Atom _ _) = p
unificaConjuncion (Disy fs) = Disy fs
unificaConjuncion (Conj fs) = Conj (concat (map (aux) (concat xs)))
    where 
      xs = [ aux f | f <- fs]
      aux (Conj xs) = xs
      aux f = [f]
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> let f1 = Conj [p, Conj [r,q]]
-- >>> f1
-- (p⋀(r⋀q))
-- >>> unificaConjuncion f1
-- (p⋀(r⋀q))
-- >>> unificaConjuncion f1 == (Conj [p, Conj [r,q]])
-- False
-- >>> unificaConjuncion f1 == (Conj [p,r,q])
-- True
\end{code}

\begin{nota}
  La representación ``visual'' por pantalla de una conjunción de conjunciones
  y su unificación puede ser la misma, como en el ejemplo anterior.
\end{nota}


Así, hemos construido el algoritmo para el cálculo de formas normales
conjuntivas. Definimos la función \texttt{(formaNormalConjuntiva f)}


\begin{code}

formaNormalConjuntiva :: Form -> Form
formaNormalConjuntiva = 
    unificaConjuncion . interiorizaDisy . interiorizaNeg . elimImpEquiv

\end{code}

Por ejemplo

\begin{code}
-- | Ejemplos
-- >>> let f1 = Neg (Conj [p, Impl q r])
-- >>> f1
-- ¬(p⋀(q⟹r))
-- >>> formaNormalConjuntiva f1
-- ((¬p⋁q)⋀(¬p⋁¬r))
-- >>> enFormaNC (formaNormalConjuntiva f1)
-- True
--
-- >>> let f2 = Neg (Conj [Disy [p,q],r])
-- >>> f2
-- ¬((p⋁q)⋀r)
-- >>> formaNormalConjuntiva f2
-- ((¬p⋁¬r)⋀(¬q⋁¬r))
-- >>> enFormaNC (formaNormalConjuntiva f2)
-- True
-- >>> let f3 = (Impl (Conj [p,q]) (Disy [Conj [Disy [r,q],Neg p], Neg r]))
-- >>> f3
-- ((p⋀q)⟹(((r⋁q)⋀¬p)⋁¬r))
-- >>> formaNormalConjuntiva f3
-- ((¬p⋁r)⋀((¬p⋁q)⋀((¬p⋁¬p)⋀((¬p⋁¬r)⋀((¬q⋁r)⋀((¬q⋁q)⋀((¬q⋁¬p)⋀(¬q⋁¬r))))))))
-- >>> enFormaNC (formaNormalConjuntiva f3)
-- True
\end{code}

\begin{Def}
  Una fórmula está en \textbf{forma normal disyuntiva} si es una disyunción de
  conjunciones de literales.
  $$(p_1 \wedge \dots \wedge p_n) \vee \dots \vee (q_1\wedge \dots \wedge q_m)$$
\end{Def}

\subsection{Forma rectificada}

\begin{Def}
  Una fórmula $F$ está en forma \textbf{rectificada} si ninguna variable
  aparece, de manera simultánea, libre y ligada ,y cada cuantificador se 
  refiere a una variable diferente.
\end{Def}

Para proceder a su implementación definimos una función auxiliar
previa que denotamos \texttt{(sustAux n v f)} que efectúa una
sustitución de la variable \texttt{v}  por $x_n$.

\index{\texttt{sustAux}}
\begin{code}
sustAux :: Int -> Variable -> Form -> Form
sustAux n v (PTodo var f) 
    | var == v = 
        PTodo (Variable "x" [n]) 
      (sustAux n v (sustitucionForm [(v, Var (Variable "x" [n]))] f))
    | otherwise = sustAux (n+1) var (PTodo var f)
sustAux n v (Ex var f)  
    | var == v = 
        Ex (Variable "x" [n]) 
      (sustAux n v (sustitucionForm [(v, Var (Variable "x" [n]))] f))
    | otherwise = sustAux (n+1) var (Ex var f)
sustAux n v (Impl f1 f2) = 
    Impl (sustAux n v f1) (sustAux (n+k) v f2)
    where
      k = length (varEnForm f1)
sustAux n v (Conj fs) = Conj (map (sustAux n v) fs)
sustAux n v (Disy fs) = Disy (map (sustAux n v) fs)
sustAux n v (Neg f) = Neg (sustAux n v f)
sustAux n v f = sustitucionForm [(v, Var (Variable "x" [n]))] f
\end{code}

Añadimos ejemplos

\begin{code}
-- | Ejemplo
-- >>> let f1 = PTodo x (Impl (Atom "P" [tx]) (Atom "Q" [tx,ty]))
-- >>> f1
-- ∀x (P[x]⟹Q[x,y])
-- >>> sustAux 0 x f1
-- ∀x0 (P[x0]⟹Q[x0,y])
\end{code}

Definimos \texttt{(formRec n f)} que calcula la forma rectificada
de la fórmula \texttt{f} empezando a renombrar las variables desde el índice \texttt{n}.

\index{\texttt{formRec}}
\begin{code}

formRec :: Int -> Form -> Form
formRec n (PTodo v form) = sustAux n v (PTodo v (formRec (n+1) form))
formRec n (Ex v form) = sustAux n v (Ex v (formRec (n+1) form))
formRec n (Impl f1 f2) = Impl (formRec n f1) (formRec (n+k) f2)
    where
      k = length (recolectaCuant f1)
formRec n (Conj fs) = Conj [formRec (n+(k f fs)) f | f <- fs]
    where
      k f fs = length (concat (map (recolectaCuant) (takeWhile (/=f)
                                                               fs)))
formRec n (Disy fs) = Disy [formRec (n+(k f fs)) f | f <- fs]
    where
      k f fs = length (concat (map (recolectaCuant) (takeWhile (/=f)
                                                               fs)))
formRec n (Neg f) = Neg (formRec n f)
formRec n f = f

\end{code}

Por ejemplo

\begin{code}
-- | Ejemplos
-- >>> formula2
-- ∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- >>> formRec 0 formula2
-- ∀x0 ∀x1 (R[x0,x1]⟹∃x4 (R[x0,x4]⋀R[x4,x1]))
-- >>> formula3
-- (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- >>> formRec 0 formula3
-- (R[x,y]⟹∃x0 (R[x,x0]⋀R[x0,y]))
\end{code}

\subsection{Forma normal prenexa}

\begin{Def}
  Una fórmula $F$ está en forma \textbf{normal prenexa} si es de la forma
  $Q_1x_1 \dots Q_nx_nG$ donde $Q_i \in \{\forall ,\exists \}$ y $G$ no tiene
  cuantificadores.
\end{Def}

Para la definición de la forma normal prenexa requerimos de dos funciones
previas. Una que elimine los cuantificadores, \texttt{(eliminaCuant f)}, y otra
que los recolecta en una lista ,\texttt{(recolectaCuant f)}.

La definición de \texttt{eliminaCuant f} es

\index{\texttt{eliminaCuant}}
\begin{code}
eliminaCuant :: Form -> Form
eliminaCuant (Ex x f) = eliminaCuant f
eliminaCuant (PTodo x f) = eliminaCuant f
eliminaCuant (Conj fs) = Conj (map eliminaCuant fs)
eliminaCuant (Disy fs) = Disy (map eliminaCuant fs)
eliminaCuant (Neg f) = Neg (eliminaCuant f)
eliminaCuant (Impl f1 f2) = Impl (eliminaCuant f1) (eliminaCuant f2)
eliminaCuant (Equiv f1 f2) = Equiv (eliminaCuant f1) (eliminaCuant f2)
eliminaCuant p@(Atom _ _) = p
\end{code}

Algunos ejemplos

\begin{code}
-- | Ejemplos
-- >>> eliminaCuant formula2
-- (R[x,y]⟹(R[x,z]⋀R[z,y]))
-- >>> eliminaCuant formula3
-- (R[x,y]⟹(R[x,z]⋀R[z,y]))
\end{code}

La implementación de \texttt{(recolectaCuant f)} es

\index{\texttt{recolectaCuant}}
\begin{code}
recolectaCuant :: Form -> [Form]
recolectaCuant (Ex x f) = (Ex x p): recolectaCuant f
recolectaCuant (PTodo x f) = (PTodo x p): recolectaCuant f
recolectaCuant (Conj fs) = concat (map recolectaCuant fs)
recolectaCuant (Disy fs) = concat (map recolectaCuant fs)
recolectaCuant (Neg f) = recolectaCuant f
recolectaCuant (Impl f1 f2) = recolectaCuant f1 ++ recolectaCuant f2
recolectaCuant p@(Atom _ _) = []
recolectaCuant (Equiv f1 f2) = recolectaCuant f1 ++ recolectaCuant f2
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> recolectaCuant formula2
-- [∀x p,∀y p,∃z p]
-- >>> recolectaCuant formula3
-- [∃z p]
\end{code}

Definimos la función \texttt{formaNormalPrenexa f} que calcula
la forma normal prenexa de la fórmula \texttt{f}

\index{\texttt{formaNormalPrenexa}}
\begin{code}
formaNormalPrenexa :: Form -> Form
formaNormalPrenexa f = aplica cs (eliminaCuant (formRec 0 f))
    where
      aplica [] f = f
      aplica ((PTodo x _):fs) f = aplica fs (PTodo x f)
      aplica ((Ex x _):fs) f = aplica fs (Ex x f)
      cs = reverse (recolectaCuant (formRec 0 f))
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> formaNormalPrenexa formula2
-- ∀x0 ∀x1 ∃x4 (R[x0,x1]⟹(R[x0,x4]⋀R[x4,x1]))
-- >>> formaNormalPrenexa formula3
-- ∃x0 (R[x,y]⟹(R[x,x0]⋀R[x0,y]))
\end{code}  
 

\subsection{Forma normal prenexa conjuntiva}

\begin{Def}
  Una fórmula $F$ está en \textbf{forma normal prenexa conjuntiva} si está en forma normal prenexa con $G$ en forma normal conjuntiva.
\end{Def}

La implementamos en \texttt{Haskell} mediante la función \texttt{(formaNPConjuntiva f)}

\index{\texttt{formaNPConjuntiva}}
\begin{code}
formaNPConjuntiva :: Form -> Form
formaNPConjuntiva f = aux (formaNormalPrenexa f)
    where
      aux (PTodo v f) = PTodo v (aux f)
      aux (Ex v f) = Ex v (aux f)
      aux f = formaNormalConjuntiva f
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> formula2
-- ∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- >>> formaNPConjuntiva formula2
-- ∀x0 ∀x1 ∃x4 ((¬R[x0,x1]⋁R[x0,x4])⋀(¬R[x0,x1]⋁R[x4,x1]))
-- >>> formula3
-- (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
-- >>> formaNPConjuntiva formula3
-- ∃x0 ((¬R[x,y]⋁R[x,x0])⋀(¬R[x,y]⋁R[x0,y]))
\end{code}

\subsection{Forma de Skolem}

\begin{Def}
  La fórmula \texttt{F} está en \textbf{forma de Skolem} si es de la forma
  $\forall x_1 \dots \forall x_n G$, donde $n \geq 0$ y $G$ no tiene
  cuantificadores.
\end{Def}

Para transformar una fórmula en forma de Skolem emplearemos sustituciones y
unificaciones. Además, necesitamos eliminar las equivalencias e implicaciones.
Para ello definimos la equivalencia y equisatisfacibilidad entre fórmulas.

\begin{Def}
  Las fórmulas \texttt{F} y \texttt{G} son \textbf{equivalentes} si para toda
  interpretación valen lo mismo.
\end{Def}

\begin{Def}
  Las fórmulas \texttt{F} y \texttt{G} son \textbf{equisatisfacibles} si se cumple
  que ambas son satisfacibles o ninguna lo es.
\end{Def}



Finalmente, definamos una cadena de funciones, para finalizar con
\texttt{(skolem f)} que transforma \texttt{f} a su forma de Skolem.

Se define la función \texttt{(skol k vs)} que convierte una lista de variables
a un término de Skolem. Al calcular la forma de skolem de una fórmula, las variables
cuantificadas son sustituidas por lo que denotamos \textbf{término de skolem} para obtener
una fórmula libre. Los términos de skolem estan compuestos por las siglas ``sk''
y un entero que lo identifique. 

\begin{nota}
  El término de skolem está expresado con la misma
  estructura que los términos funcionales.
\end{nota}


\index{\texttt{skol}}
\begin{code}
skol :: Int -> [Variable] -> Termino
skol k vs = Ter ("sk" ++ show k) [Var x | x <- vs]
\end{code}

Por ejemplo,

\begin{sesion}
skol 1 [x]  ==  sk1[x]
\end{sesion}

Definimos la función \texttt{(skf f vs pol k)}, donde
\begin{enumerate}
\item \texttt{f} es la fórmula que queremos convertir.
\item \texttt{vs} es la lista de los cuantificadores (son necesarios
  en la recursión).
\item \texttt{pol} es la polaridad, es de tipo \texttt{Bool}.
\item \texttt{k} es de tipo \texttt{Int} y sirve como identificador
  de la forma de Skolem.
\end{enumerate}

\begin{Def}
  La \textbf{Polaridad} cuantifica las apariciones de las variables cuantificadas
  de la siguiente forma:
  \begin{itemize*}
  \item  Una cantidad de apariciones impar de $x$ en la subfórmula $F$ de
    $\exists x F$ indica que $x$ tiene una polaridad negativa en la fórmula.
  \item  Una cantidad de apariciones par de $x$ en la subfórmula $F$ de
    $\forall x F$ indica que $x$ tiene una polaridad positiva en la fórmula. 
  \end{itemize*}
\end{Def}

\index{\texttt{skf}}
\begin{code}
skf :: Form -> [Variable] -> Bool -> Int -> (Form,Int)
skf (Atom n ts) _ _ k =
  (Atom n ts,k)
skf (Conj fs) vs pol k =
  (Conj fs',j)
  where (fs',j) = skfs fs vs pol k
skf (Disy fs) vs pol k =
  (Disy fs', j)
  where (fs',j) = skfs fs vs pol k
skf (PTodo x f) vs True k =
  (PTodo x f',j)
  where vs'    = insert x vs
        (f',j) = skf f vs' True k
skf (PTodo x f) vs False k =
  skf (sustitucionForm b f) vs False (k+1)
  where b = [(x,skol k vs)]
skf (Ex x f) vs True k =
  skf (sustitucionForm b f) vs True (k+1)
  where b = [(x,skol k vs)]
skf (Ex x f) vs False k =
  (Ex x f',j)
  where vs' = insert x vs
        (f',j) = skf f vs' False k
skf (Neg f) vs pol k =
  (Neg f',j)
  where (f',j) = skf f vs (not pol) k
\end{code}

donde la skolemización de una lista está definida por  

\index{\texttt{skfs}}
\begin{code}
skfs :: [Form] -> [Variable] -> Bool -> Int -> ([Form],Int)
skfs [] _ _ k        = ([],k)
skfs (f:fs) vs pol k = (f':fs',j)
  where (f',j1) = skf  f  vs pol k
        (fs',j) = skfs fs vs pol j1
\end{code}

La skolemización de una fórmula sin equivalencias ni implicaciones se define
por \index{\texttt{sk}}

\begin{code}
sk :: Form -> Form
sk f = fst (skf f [] True 0)
\end{code}

La función \texttt{(skolem f)} devuelve la forma de Skolem de la fórmula
\texttt{f}.

\index{\texttt{skolem}}
\begin{code}
skolem :: Form -> Form
skolem  = aux. sk . elimImpEquiv 
    where
      aux (Neg (Neg f)) = f
      aux (Neg (Ex v f)) = (PTodo v f)
      aux (Disy fs) = Disy (map aux fs)
      aux f = f
\end{code}

Por ejemplo,

\begin{code}
-- | Ejemplos
-- >>> skolem formula2
-- ∀x ∀y (¬R[x,y]⋁(R[x,sk0[x,y]]⋀R[sk0[x,y],y]))
-- >>> skolem formula3
-- (¬R[x,y]⋁(R[x,sk0]⋀R[sk0,y]))
-- >>> skolem formula4
-- R[cero,sk0]
-- >>> skolem formula5
-- (¬P[sk0]⋁∀y Q[x,y])
-- >>> skolem (Neg (Ex x (Impl (Atom "P" [tx]) (PTodo x (Atom "P" [tx])))))
-- ∀x (¬P[x]⋁P[sk0[x]])
-- >>> let f1 = Impl (Neg (Disy [PTodo x (Impl (Atom "P" [tx]) (Atom "Q" [tx])),PTodo x (Impl (Atom "Q" [tx]) (Atom "R" [tx]))])) (PTodo x (Impl (Atom "P" [tx]) (Atom "R" [tx])))
-- >>> skolem f1
-- ((∀x (¬P[x]⋁Q[x])⋁∀x (¬Q[x]⋁R[x]))⋁∀x (¬P[x]⋁R[x]))
\end{code}



\section{Forma clausal}
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
  normal conjuntiva de la fórmula $F$. Entonces, es una forma clausal de $F$ es
  $\left\{ (p_1\vee \dots \vee p_n) , \dots , (q_1 \vee \dots \vee q_m) \right\}$
\end{Prop}

Por ejemplo una forma clausal de $\neg (p \wedge (q \rightarrow r))$
es $\left\{ \left\{ \neg p, q \right\},\left\{\neg p,\neg r\right\} \right\}$

Se definen los tipos de dato \texttt{Clausula} y \texttt{Clausulas},
para representar una cláusula o un conjunto de ellas respectivamente.
\begin{code}

data Clausula  = C [Form]
data Clausulas = Cs [Clausula]

\end{code}

Definimos su representación

\begin{code}
instance Show Clausula where
    show (C []) = "[]"
    show (C fs) = "{" ++  init (tail (show fs)) ++ "}"
instance Show Clausulas where
    show (Cs []) = "[]"
    show (Cs cs) = "{" ++  init (tail (show cs)) ++ "}"

\end{code}

Por ejemplo de

\begin{code}
-- | Fórmula
-- >>> Neg (Conj [p,Impl q r])
-- ¬(p⋀(q⟹r))
\end{code}

su forma clausal es

\begin{code}
-- | Forma clausal
-- >>> Cs [C [Neg p,q], C [Neg p, Neg r]]
-- {{¬p,q},{¬p,¬r}}
\end{code}

El algoritmo del cálculo de la forma clausal de una fórmula
\texttt{F} es:

\begin{enumerate}
\item Sea $F_1 = \exists y_1 \dots \exists y_n F$, donde $y_i$ con $i=1,\dots ,n$
  son las variables libres de F.
\item Sea $F_2$ una forma normal prenexa conjuntiva rectificada de $F_1$.
\item Sea $F_3= \texttt{ Skolem }(F_2)$, que tiene la forma
  $$\forall x_1 \dots \forall x_p [(L_1\vee \dots \vee L_n)
  \wedge \dots \wedge (M_1\vee \dots \vee M_m)]$$
\end{enumerate}

Entonces, una forma clausal es

$$ S=
\left\{
  \left\{ L_1, \dots ,L_n \right\}
  ,\dots ,
  \left\{ M_1, \dots ,M_m \right\}
\right\} $$

  
Dada una fórmula que está en la forma del paso 3 del algoritmo, es decir
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
      disyAClau (Disy fs) = C fs
\end{code}

Por ejemplo

\begin{code}
-- | Ejemplo
-- >>> Conj [p, Disy [q,r]]
-- (p⋀(q⋁r))
-- >>> form3CAC (Conj [p, Disy [q,r]])
-- {{p},{q,r}}
\end{code}

Definimos \texttt{(formaClausal f)} que transforma \texttt{f}
a su forma clausal.

\begin{code}

formaClausal :: Form -> Clausulas
formaClausal  = form3CAC . skolem .formaNPConjuntiva
    

\end{code}

Por ejemplo

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

\section{Tableros semánticos}

\begin{Def}
  Un conjunto de fórmulas es \textbf{consistente} si tiene algún modelo. En
  caso contrario, se denomina \textbf{inconsistente}.
\end{Def}

\comentario{Distinguir el caso de fórmulas con variables libres.}

La idea de obtener fórmulas equivalentes nos hace introducir los tipos de
fórmulas alfa, beta, gamma y delta. No son más que equivalencias ordenadas por
orden teórico en el que se pueden acometer para una simplicación eficiente de
una fórmula, a otra cuyas únicas conectivas lógicas sean disyunciones y
conjunciones.

\begin{itemize}
\item Fórmulas alfa
 
   \vspace*{1ex}

   $\begin{array}{|l|l| } \hline
     \neg (F_1 \rightarrow F_2) & F_1 \wedge F_2               \\ \hline
     \neg(F_1 \vee F_2)         & F_1 \wedge \neg F_2          \\ \hline
     F_1 \leftrightarrow F_2    & (F_1 \rightarrow F_2) \wedge 
                                  (F_2 \rightarrow F_1)        \\ \hline
   \end{array}$

\vspace*{2ex}
Las definimos en Haskell

\index{\texttt{alfa}}
\begin{code}
alfa :: Form -> Bool
alfa (Conj _)       = True
alfa (Neg (Disy _)) = True
alfa _              = False
\end{code}

\vspace*{2ex}

\item Fórmulas beta 
  
  \vspace*{1ex}

  $\begin{array}{|l|l|} \hline
    F_1 \rightarrow F_2             & \neg F_1 \vee F_2                \\ \hline
    \neg (F_1 \wedge F_2)           & \neg F_1 \vee \neg F_2           \\ \hline
    \neg (F_1 \leftrightarrow F_2)  & \neg (F_1 \rightarrow F_2 ) \vee 
                                      (\neg F_2 \rightarrow F_1)       \\ \hline
   \end{array}$
   
  \vspace*{2ex}
Las definimos en Haskell

\index{\texttt{beta}}
\begin{code}
beta :: Form -> Bool
beta (Disy _)       = True
beta (Neg (Conj _)) = True
beta _              = False
\end{code}

\vspace*{2ex}
  
\item Fórmulas gamma 

  \vspace*{1ex}

  $\begin{array}{|l|c|} \hline
    \forall x F      & F [x/t]       \\ \hline
    \neg \exists x F & \neg F [x/t ] \\ \hline
  \end{array}$

\vspace*{1ex}

Notar que $t$ es un término básico.

  \vspace*{2ex}
  
Las definimos en Haskell
  
  \index{\texttt{gamma}}
\begin{code}
gamma :: Form -> Bool
gamma (PTodo _ _)    = True
gamma (Neg (Ex _ _)) = True
gamma _              = False
\end{code}
\vspace*{2ex}
  
\item Fórmulas delta 

  \vspace*{1ex}

  $\begin{array}{|l|l|} \hline
    \exists x F    & F[x / a]       \\ \hline
    \neg \forall F & \neg F [x / a] \\ \hline
  \end{array}$

  \vspace*{1ex}

  Notar que $a$ es una constante nueva.
  
  \vspace*{2ex}
  
Las definimos en Haskell
  
  \index{\texttt{delta}}
\begin{code}
delta :: Form -> Bool
delta  (Neg (PTodo _ _))    = True
delta  (Ex _ _)             = True
delta _                     = False
\end{code}
\vspace*{2ex}
  
\end{itemize}

\begin{nota}

  Cada elemento de la izquierda de las tablas es equivalente a la
  entrada de la derecha de la tabla que esté en su misma altura.
  Es decir, considerando las tablas como matrices $a_{i,1}\equiv a_{i,2} \forall i$.
  
\end{nota}

Mediante estas equivalencias se procede a lo que se denomina método de los
tableros semánticos. Uno de los objetivos del método de los tableros es
determinar si una fórmula es consistente, así como la búsqueda de modelos.

\begin{Def}
  Un \textbf{literal} es un átomo o la negación de un átomo.
\end{Def}

Lo definimos en haskell

\index{\texttt{literal}}
\begin{code}
atomo, negAtomo, literal :: Form -> Bool

atomo (Atom _ _)          = True
atomo _                   = False

negAtomo (Neg (Atom _ _)) = True
negAtomo  _               = False

literal f = atomo f || negAtomo f
\end{code}

El método de tableros de un conjunto de fórmulas $S$ sigue el siguiente
algoritmo:

\begin{itemize*}
\item El árbol cuyo único nodo tiene como etiqueta $S$ es
  un tablero de $S$.
\item Sea $\mathcal{T}$ un tablero de $S$ y $S_1$ la etiqueta de
  una hoja  de $\mathcal{T}$.
  \begin{enumerate}
  \item Si $S_1$ contiene una fórmula y su negación, entonces el árbol
    obtenido añadiendo como hijo de $S_1$ el nodo etiquetado con
    $\left\{ \perp \right\}$ es un tablero de $S$.
  \item Si $S_1$ contiene una doble negación $\neg \neg F$, entonces
    el árbol obtenido añadiendo como hijo de $S_1$ el nodo etiquetado
    con $(S_1 \backslash \left\{\neg \neg F \right\})\cup \left\{ F \right\}$
    es un tablero de $S$.
  \item Si $S_1$ contiene una fórmula alfa $F$ de componentes $F_1$ y $F_2$,
    entonces el árbol obtenido añadiendo como hijo de $S_1$ el nodo etiquetado
    con $(S_1 \backslash \left\{ F \right\})\cup \left\{ F_1,F_2 \right\}$
    es un tablero de $S$.
  \item Si $S_1$ contiene una fórmula beta de $F$ de componentes $F_1$ y $F_2$,
    entonces el árbol obtenido añadiendo como hijos de $S_1$ los nodos
    etiquetados con $(S_1 \backslash \left\{ F \right\}) \cup \left\{ F_1 \right\}$ y
    $(S_1 \backslash \left\{ F \right\})\cup \left\{ F_2 \right\}$ es un tablero
    de $S$.
  \end{enumerate}
\end{itemize*}


\begin{Def}
  Se dice que una hoja es \textbf{cerrada} si contiene una fórmula y su negación.
  Se representa $\bot$
\end{Def}

\begin{Def}
  Se dice que una hoja es \textbf{abierta} si es un conjunto de literales y no contiene
  un literal y su negación.
\end{Def}

\begin{Def}
  Un \textbf{tablero completo} es un tablero tal que todas sus hojas son abiertas o
  cerradas.
\end{Def}

Ejemplo de tablero completo

\begin{center}
  \begin{tikzpicture}[every node/.style = {shape=rectangle, rounded corners,
    draw, align=center,
    top color=white}, 
  level 1/.style={sibling distance=10em},
  level 2/.style={sibling distance=20em},
  level 3/.style={sibling distance=10em},
  level 4/.style={sibling distance=10em}
]]
  \node {1. $\neg (p \vee q \rightarrow p \wedge q)$}
  child { node {2. $p\vee q$ , $\neg (p \wedge q)$ (1)}
    child { node {3. $p$ , $\neg (p\wedge q)$ (2)}
      child { node {5. $p$, $\neg p$ (3)}
        child { node {7. $\perp$ (5)}}}
      child { node {6. $p$ , $\neg q$ (3)}}}
    child { node {4.  $q$ , $\neg (p\wedge q)$ (2)}
      child { node {8. $q$ , $\neg p$ (4)}}
      child { node {9. $q$ , $\neg q$ (4)}
        child { node {10. $\perp$ (9)}}}}}
  ;
  \end{tikzpicture}
\end{center}

Representamos la fórmula de este tablero en Haskell.

\begin{code}
tab1 = Neg (Impl (Disy [p,q]) (Conj [p,q]))

-- | Representación
-- >>> tab1
-- ¬((p⋁q)⟹(p⋀q))
\end{code}


\begin{Def}
  Un tablero es \textbf{cerrado} si todas sus hojas son cerradas.
\end{Def}

Un ejemplo de tablero cerrado es

\begin{center}
\begin{tikzpicture}[sibling distance=15em,
  every node/.style = {shape=rectangle, rounded corners,
    draw, align=center, top color=white}]]
  \node {1. $ (p \rightarrow q) \wedge (q \rightarrow r)
    \wedge  \neg (p \rightarrow r)$  }
  child { node {2. $p \rightarrow q$, $q \rightarrow r$,
      $p$, $ \neg r$ (1) }
    child { node {3. $p \rightarrow q$ , $\neg p$ ,
        $p$, $\neg r$ (2)}
      child { node {5. $ \neg p$ , $ \neg q$ ,
          $p$ , $ \neg r$ (3)}
        child { node {7. $ \perp $ (5)}}}
      child { node {6. $q$ , $ \neg q$ ,
          $p$ , $ \neg r$ (3)}
        child { node {8. $ \perp $ (6)}}}}
    child { node {4. $p \rightarrow q$ , $r$ ,
        $p$ , $ \neg r$ (2)}
      child { node {9. $ \perp $ (4)} }}};
\end{tikzpicture}
\end{center}

La fórmula del tablero se representa en Haskell

\begin{code}
tab2 = Conj [Impl p q, Impl q r, Neg (Impl p r)]
-- | Representación
-- >>> tab2
-- ((p⟹q)⋀((q⟹r)⋀¬(p⟹r)))
\end{code}


\begin{Teo}
  Si una fórmula $F$ es consistente, entonces cualquier tablero de $F$ tendrá
  ramas abiertas.
\end{Teo}

Nuestro objetivo es definir en Haskell un método para el cálculo de tableros
semánticos. El contenido relativo a tableros semánticos se encuentra en el
módulo \texttt{Tableros}.



\entrada{Tableros}


