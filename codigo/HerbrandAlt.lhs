\chapter{Modelos de Herbrand alternativo}

En este capítulo se da una definición alternativa del
universo de Herbrand que simplifica su representación.
El contenido de este capítulo se encuentra en el módulo
\texttt{HerbrandAlt}

\comentario{Se ha definido la alternativa en un capítulo aparte para               
luego decidir si mantenemos ambos capítulos complementándose o nos
quedamos solo con este.}

\begin{code}
module Herbrand where
import Data.List
import Text.PrettyPrint.GenericPretty
import PFH                           
import LPH                           
import PTLP
\end{code}

\section{Universo de Herbrand}

\begin{Def}
  El \textbf{universo de Herbrand} de $L$ es el conjunto de términos básicos de
  $F$. Se reprenta por $\mathcal{UH}(L)$.
\end{Def}

\begin{Def}
  Una \textbf{signatura} es una terna formada por las constantes, símbolos funcionales
  y símbolos de relación. Teniendo en cuenta la aridad tanto de los símbolos funcionales
  como los de relación.
\end{Def}

Se define un tipo de dato para la signatura.

\begin{code}
type Signatura = ([Nombre],[(Nombre,Int)],[(Nombre,Int)])
\end{code}

Dada una signatura, se procede a definir la función \texttt{(unionSignatura s1 s2)}
que une las signaturas \texttt{s1} y \texttt{s2}.

\index{\texttt{unionSignatura}}
\begin{code}
unionSignatura :: Signatura -> Signatura -> Signatura
unionSignatura (cs1,fs1,rs1) (cs2,fs2,rs2) =
    ( cs1 `union` cs2
    , fs1 `union` fs2
    , rs1 `union` rs2 )
\end{code}

Por ejemplo,

\begin{sesion}
>>> let s1 = (["a"],[("f",1)],[])
>>> let s2 = (["b","c"],[("f",1),("g",2)],[("R",2)])
>>> unionSignatura s1 s2
(["a","b","c"],[("f",1),("g",2)],[("R",2)])
\end{sesion}

Generalizamos la función anterior a la unión de una lista de signaturas
mediante la función \texttt{(unionSignaturas ss)}.

\index{\texttt{unionSignaturas}}
\begin{code}
unionSignaturas :: [Signatura] -> Signatura
unionSignaturas = foldr unionSignatura ([], [], [])
\end{code}

Por ejemplo

\begin{sesion}
>>> let s1 = (["a"],[("f",1)],[])
>>> let s2 = (["b","c"],[("f",1),("g",2)],[("R",2)])
>>> let s3 = (["a","c"],[],[("P",1)])
>>> unionSignaturas [s1,s2,s3]
(["a","b","c"],[("f",1),("g",2)],[("R",2),("P",1)])
\end{sesion}

Se define la función \texttt{(signaturaTerm t)} que determina la
signatura del término t.

\index{\texttt{signaturaTerm}}
\begin{code}
signaturaTerm :: Termino -> Signatura 
signaturaTerm (Var _) = ([], [], [])
signaturaTerm (Ter c []) = ([c], [], [])
signaturaTerm (Ter f ts) = (cs,[(f,n)] `union` fs, rs)
    where
      (cs,fs,rs) = unionSignaturas (map signaturaTerm ts)
      n          = length ts
\end{code}

A continuación, algunos ejemplos

\begin{sesion}
>>> signaturaTerm tx
([],[],[])
>>> signaturaTerm a
(["a"],[],[])
>>> let t1 = Ter "f" [a,tx,Ter "g" [b,a]]
>>> t1
f[a,x,g[b,a]]
>>> signaturaTerm t1
(["a","b"],[("f",3),("g",2)],[])
\end{sesion}

Se define la signatura de una fórmula \texttt{f} mediante la función
\texttt{(signaturaForm f)}.

\index{\texttt{signaturaForm}}
\begin{code}
signaturaForm :: Form -> Signatura
signaturaForm (Atom r ts) =
  (cs,fs, [(r,n)] `union` rs)
  where (cs,fs,rs) = unionSignaturas (map signaturaTerm ts)
        n          = length ts
signaturaForm (Neg f) =
  signaturaForm f
signaturaForm (Impl f1 f2) =
  signaturaForm f1 `unionSignatura` signaturaForm f2
signaturaForm (Equiv f1 f2) =
  signaturaForm f1 `unionSignatura` signaturaForm f2
signaturaForm (Conj fs) =
  unionSignaturas (map signaturaForm fs)
signaturaForm (Disy fs) =
  unionSignaturas (map signaturaForm fs)
signaturaForm (PTodo _ f) =
  signaturaForm f
signaturaForm (Ex _ f) =
  signaturaForm f
\end{code}

Por ejemplo,

\begin{sesion}
-- >>> let f1 = Atom "R" [a,tx,Ter "g" [b,a]]
>>> f1
R[a,x,g[b,a]]
>>> signaturaForm f1
(["a","b"],[("g",2)],[("R",3)])
>>> signaturaForm (Neg f1)
(["a","b"],[("g",2)],[("R",3)])
>>> let f2 = Atom "P" [b]
>>> let f3 = Impl f1 f2
>>> f3
(R[a,x,g[b,a]]⟹P[b])
>>> signaturaForm f3
(["a","b"],[("g",2)],[("R",3),("P",1)])
>>> let f4 = Conj [f1,f2,f3]
>>> f4
(R[a,x,g[b,a]]⋀(P[b]⋀(R[a,x,g[b,a]]⟹P[b])))
>>> signaturaForm f4
(["a","b"],[("g",2)],[("R",3),("P",1)])
>>> let f5 = PTodo x f4
>>> f5
∀x (R[a,x,g[b,a]]⋀(P[b]⋀(R[a,x,g[b,a]]⟹P[b])))
>>> signaturaForm f5
(["a","b"],[("g",2)],[("R",3),("P",1)])
\end{sesion}

Generalizamos la función anterior a una lista de fórmulas con la
función \texttt{(signaturaForms fs)}.

\index{\texttt{signaturaForms}}
\begin{code}
signaturaForms :: [Form] -> Signatura
signaturaForms fs =
  unionSignaturas (map signaturaForm fs)
\end{code}

Por ejemplo,

\begin{sesion}
>>> let f1 = Atom "R" [Ter "f" [tx]]
>>> let f2 = Impl f1 (Atom "Q" [a,Ter "f" [b]])
>>> let f3 = Atom "S" [Ter "g" [a,b]]
>>> signaturaForms [f1,f2,f3]
(["a","b"],[("f",1),("g",2)],[("R",1),("Q",2),("S",1)])
\end{sesion}

\begin{Def}
  El \textbf{universo de Herbrand} de $L$ es el conjunto de términos básicos de
  $F$. Se reprenta por $\mathcal{UH}(L)$.
\end{Def}

\begin{Prop}
  $\mathcal{UH}(L) = \bigcup_{i \geq 0} H_i (L)$, donde $H_i(L)$ es el
  nivel $i$ del $\mathcal{UH}(L)$ definido por
  \begin{equation*}
    H_0(L)= \left\{
      \begin{array}{ll}
        C, & \text{si } C \neq \emptyset \\
        {a}, & \text{en caso contrario (a nueva constante)} 
      \end{array} \right.
  \end{equation*}
  $$H_{i+1}(L) = H_i(L)\cup \{f(t_1,\dots,t_n):f\in \mathcal{F}_n \text{ y } t_i\in H_i (L)\}$$
\end{Prop}

Definimos la función \texttt{universoHerbrand n s} que es el universo de
Herbrand de la signatura \texttt{s} a nivel \texttt{n}.

\begin{code}
universoHerbrand :: Int -> Signatura -> [Termino]
universoHerbrand 0 (cs,_,_) 
  | null cs   = [a]
  | otherwise = [Ter c [] | c <- cs]
universoHerbrand n s@(_,fs,_) =
  u `union`
  [Ter f ts | (f,k) <- fs
            , ts <- variacionesR k u]
  where u = universoHerbrand (n-1) s 
\end{code}

Añadimos algunos ejemplos ilustrativos

\begin{sesion}
>>> let s1 = (["a","b","c"],[],[])
>>> universoHerbrand 0 s1 
[a,b,c]
>>> universoHerbrand 1 s1 
[a,b,c]

>>> let s2 = ([],[("f",1)],[])
>>> universoHerbrand 0 s2 
[a]
>>> universoHerbrand 1 s2 
[a,f[a]]
>>> universoHerbrand 2 s2 
[a,f[a],f[f[a]]]
 
>>> let s3 = (["a","b"],[("f",1),("g",1)],[])
>>> universoHerbrand 0 s3 
[a,b]
>>> universoHerbrand 1 s3 
[a,b,f[a],f[b],g[a],g[b]]
>>> pp $ universoHerbrand 2 s3 
[a,b,f[a],f[b],g[a],g[b],f[f[a]],f[f[b]],f[g[a]],
 f[g[b]],g[f[a]],g[f[b]],g[g[a]],g[g[b]]]
>>> universoHerbrand 3 (["a"],[("f",1)],[("R",1)]) 
[a,f[a],f[f[a]],f[f[f[a]]]]
>>> pp $ universoHerbrand 3 (["a","b"],[("f",1),("g",1)],[]) 
a,b,f[a],f[b],g[a],g[b],f[f[a]],f[f[b]],f[g[a]],
 f[g[b]],g[f[a]],g[f[b]],g[g[a]],g[g[b]],f[f[f[a]]],
 f[f[f[b]]],f[f[g[a]]],f[f[g[b]]],f[g[f[a]]],
 f[g[f[b]]],f[g[g[a]]],f[g[g[b]]],g[f[f[a]]],
 g[f[f[b]]],g[f[g[a]]],g[f[g[b]]],g[g[f[a]]],
 g[g[f[b]]],g[g[g[a]]],g[g[g[b]]]]
 
>>> let s4 = (["a","b"],[("f",2)],[])
>>> universoHerbrand 0 s4
[a,b]
>>> universoHerbrand 1 s4
[a,b,f[a,a],f[a,b],f[b,a],f[b,b]]
>>> pp $ universoHerbrand 2 s4 
[a,b,f[a,a],f[a,b],f[b,a],f[b,b],f[a,f[a,a]],
 f[a,f[a,b]],f[a,f[b,a]],f[a,f[b,b]],f[b,f[a,a]],
 f[b,f[a,b]],f[b,f[b,a]],f[b,f[b,b]],f[f[a,a],a],
 f[f[a,a],b],f[f[a,a],f[a,a]],f[f[a,a],f[a,b]],
 f[f[a,a],f[b,a]],f[f[a,a],f[b,b]],f[f[a,b],a],
 f[f[a,b],b],f[f[a,b],f[a,a]],f[f[a,b],f[a,b]],
 f[f[a,b],f[b,a]],f[f[a,b],f[b,b]],f[f[b,a],a],
 f[f[b,a],b],f[f[b,a],f[a,a]],f[f[b,a],f[a,b]],
 f[f[b,a],f[b,a]],f[f[b,a],f[b,b]],f[f[b,b],a],
 f[f[b,b],b],f[f[b,b],f[a,a]],f[f[b,b],f[a,b]],
 f[f[b,b],f[b,a]],f[f[b,b],f[b,b]]]
\end{sesion}

Se define el universo de Herbrand de una fórmula \texttt{f} a nivel
\texttt{n} mediante la función \texttt{(universoHerbrandForm n f)}.

\begin{code}
universoHerbrandForm :: Int -> Form -> [Termino]
universoHerbrandForm n f =
  universoHerbrand n (signaturaForm f)
\end{code}

Por ejemplo,

\begin{sesion}
>>> let f1 = Atom "R" [a,b,c]
>>> universoHerbrandForm 1 f1
[a,b,c]
>>> let f2 = Atom "R" [Ter "f" [tx]]
>>> universoHerbrandForm 2 f2
[a,f[a],f[f[a]]]
>>> let f3 = Impl f2 (Atom "Q" [a,Ter "g" [b]])
>>> f3
(R[f[x]]⟹Q[a,g[b]])
>>> pp $ universoHerbrandForm 2 f3
[a,b,f[a],f[b],g[a],g[b],f[f[a]],f[f[b]],f[g[a]],
 f[g[b]],g[f[a]],g[f[b]],g[g[a]],g[g[b]]]
>>> let f4 = Atom "R" [Ter "f" [a,b]]
>>> signaturaForm f4
(["a","b"],[("f",2)],[("R",1)])
>>> pp $ universoHerbrandForm 2 f4
[a,b,f[a,a],f[a,b],f[b,a],f[b,b],f[a,f[a,a]],
 f[a,f[a,b]],f[a,f[b,a]],f[a,f[b,b]],f[b,f[a,a]],
 f[b,f[a,b]],f[b,f[b,a]],f[b,f[b,b]],f[f[a,a],a],
 f[f[a,a],b],f[f[a,a],f[a,a]],f[f[a,a],f[a,b]],
 f[f[a,a],f[b,a]],f[f[a,a],f[b,b]],f[f[a,b],a],
 f[f[a,b],b],f[f[a,b],f[a,a]],f[f[a,b],f[a,b]],
 f[f[a,b],f[b,a]],f[f[a,b],f[b,b]],f[f[b,a],a],
 f[f[b,a],b],f[f[b,a],f[a,a]],f[f[b,a],f[a,b]],
 f[f[b,a],f[b,a]],f[f[b,a],f[b,b]],f[f[b,b],a],
 f[f[b,b],b],f[f[b,b],f[a,a]],f[f[b,b],f[a,b]],
 f[f[b,b],f[b,a]],f[f[b,b],f[b,b]]]
\end{sesion}

Se generaliza la definición anterior a una lista de fórmulas
mediante la función \texttt{universoHerbrandForms n fs}

\begin{code}
universoHerbrandForms :: Int -> [Form] -> [Termino]
universoHerbrandForms n fs =
  nub (concatMap (universoHerbrandForm n) fs)
\end{code}

\section{Base de Herbrand}
