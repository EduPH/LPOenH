El contenido de este capítulo se encuentra en el módulo
\texttt{Herbrand}.
\begin{code}
module Herbrand where
import Data.List
import LPH
import PTLP
\end{code}

\begin{Def}
  Una \textbf{fórmula básica} es una fórmula sin variables
  ni cuantificadores.
\end{Def}

\section{Universo de Herbrand}

\begin{Def}
  El \textbf{universo de Herbrand} de $L$ es el conjunto de términos
  básicos de $F$. Se reprenta por $\mathcal{UH}(L)$.
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

Para ello, primero necesitamos caracterizar las constantes. Definimos
la función \texttt{(esConstante c)}.

\index{\texttt{esConstante}}
\begin{code}
esConstante :: Termino -> Bool
esConstante (Ter _ []) = True
esConstante _ = False
\end{code}

Un par de ejemplos

\begin{sesion}
ghci> esConstante a
True
ghci> esConstante tx
False
\end{sesion}


Definimos \texttt{(constForm f)} que devuelve las constantes
de \texttt{f}.

\begin{code}
constForm :: Form -> [Termino]
constForm (Atom _ ts)   = nub [ t | t <- ts, esConstante t]
constForm (Neg f)       = constForm f
constForm (Impl f1 f2)  = constForm f1 `union` constForm f2
constForm (Equiv f1 f2) = constForm f1 `union` constForm f2
constForm (Conj fs)     = nub (concatMap constForm fs)
constForm (Disy fs)     = nub (concatMap constForm fs)
constForm (PTodo x f)   = constForm f
constForm (Ex x f)      = constForm f
\end{code}

Definimos \texttt{(esFuncion f)} y \texttt{(funForm f)} para obtener todos los símbolos
funcionales que aparezcan en la fórmula  \texttt{f}.

\begin{code}
esFuncion :: Termino -> Bool
esFuncion (Fun _ _) = True
esFuncion _ = False
\end{code}

\begin{code}
funForm :: Form -> [Termino]
funForm (Atom _ ts)   = nub [ t | t <- ts, esFuncion t]
funForm (Neg f)       = funForm f
funForm (Impl f1 f2)  = funForm f1 `union` funForm f2
funForm (Equiv f1 f2) = funForm f1 `union` funForm f2
funForm (Conj fs)     = nub (concatMap funForm fs)
funForm (Disy fs)     = nub (concatMap funForm fs)
funForm (PTodo x f)   = funForm f
funForm (Ex x f)      = funForm f
\end{code}

\begin{code}
formula_6 = PTodo x (Atom "P" [Fun "f" [tx]])
\end{code}
Así podemos ya obtener el universo de Herbrand de una fórmula
\texttt{f} definiendo \texttt{(univHerbrand f)}

\begin{code}
univHerbrand :: (Eq a, Num a) => a -> Form -> [Termino]
univHerbrand 0 f = constForm form ++ map (Var) (varEnForm form)
    where
      form = skolem f
\end{code}

Por ejemplo

\begin{sesion}
ghci> univHerbrand 0 formula_2
[x,y]
ghci> univHerbrand 0 formula_3
[sk0,x,y]
ghci> univHerbrand 0 formula_4
[cero,sk0]
ghci> univHerbrand 0 formula_5
[sk0,y,x]
\end{sesion}

\begin{Prop}
  $\mathcal{UH}$ es finito si y sólo si no tiene símbolos de
  función.
\end{Prop}

\section{Base de Herbrand}

\begin{Def}
  La \textbf{base de Herbrand} de un lenguaje $L$ es el
  conjunto de átomos básicos de $L$.
\end{Def}
