El contenido de este capítulo se encuentra en el módulo
\texttt{Herbrand}.
\begin{code}
module Herbrand where
import Data.List
import PFH
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

\index{\texttt{constForm}}
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

\index{\texttt{esFuncion}}
\begin{code}
esFuncion :: Termino -> Bool
esFuncion (Ter _ xs) | length xs >= 1 = True
                     | otherwise = False
esFuncion _ = False
\end{code}

\index{\texttt{funForm}}
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

\begin{Def}
  La \textbf{aridad} de una función $f(x_1,\dots,x_n$ es el número número de
  argumentos a los que se aplica.
\end{Def}

Definimos  \texttt{(aridadF f)} de una función en Haskell.

\index{\texttt{aridadF}}
\begin{code}
aridadF :: Termino -> Int
aridadF (Ter _ ts) = length ts
\end{code}

También necesitamos definir dos funciones auxiliares
que apliquen los símbolos funcionales a las constantes del
universo de Herbrand. Las funciones son \texttt{(aplicaFunAConst f c)} 
que aplica el símbolo funcional \texttt{f} a la constante \texttt{c}, y
\texttt{(aplicaFun fs cs)} que es una generalización a listas de la 
anterior.
constante 

\index{\texttt{aplicaFunAConst}}
\index{\texttt{aplicaFun}}
\begin{code}
aplicaFunAConst (Ter s _) ts  = Ter s  ts
aplicaFun [] cs = []
aplicaFun (f:fs) cs = 
    map (aplicaFunAConst f) (subconjuntosTam (aridadF f) cs) 
                            ++ aplicaFun fs cs
\end{code}

Así podemos ya obtener el universo de Herbrand de una fórmula
\texttt{f} definiendo \texttt{(univHerbrand n f)}


\index{\texttt{univHerbrand}}
\begin{code}
univHerbrand :: (Eq a, Num a) => a -> Form -> Universo Termino
univHerbrand 0 f = constForm form ++ map (Var) (varEnForm form)
    where
      form = skolem f
univHerbrand 1 f = 
    nub (univHerbrand 0 f ++ aplicaFun (funForm f) (univHerbrand 0 f))
univHerbrand n f = 
    nub (univHerbrand (n-1) f ++ aplicaFun (funForm f)  (univHerbrand (n-1) f))
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

Definimos  fórmulas con  términos funcionales para el ejemplo

\begin{code}
formula_6,formula_7 :: Form
formula_6 = PTodo x (Atom "P" [Ter "f" [tx]])
formula_7 = PTodo x (Atom "P" [Ter "f" [tx,ty]])
\end{code}

quedando como ejemplo 

\begin{sesion}
ghci> univHerbrand 5 formula_6
[x,f[x],f[f[x]],f[f[f[x]]],f[f[f[f[x]]]],f[f[f[f[f[x]]]]]]
ghci>  univHerbrand 2 formula_7
[x,y,f[x,y],f[y,x],f[f[x,y],f[y,x]],f[f[y,x],f[x,y]],
f[y,f[y,x]],f[f[y,x],y],f[y,f[x,y]],f[f[x,y],y],
f[x,f[y,x]],f[f[y,x],x],f[x,f[x,y]],f[f[x,y],x]]
\end{sesion}

Hay que tener en cuenta que se dispara la cantidad de elementos
del universo de Herbrand ante términos funcionales con aridad grande.
\begin{sesion}
ghci> length (univHerbrand 0 formula_7)
2
ghci> length (univHerbrand 1 formula_7)
4
ghci> length (univHerbrand 2 formula_7)
14
ghci> length (univHerbrand 3 formula_7)
184
\end{sesion}
\section{Base de Herbrand}

\begin{Def}
  La \textbf{base de Herbrand} de un lenguaje $L$ es el
  conjunto de átomos básicos de $L$.
\end{Def}

Con el objetivo de definir una función que obtenga la base
de Herbrand; necesitamos poder calcular el conjunto de símbolos
de predicado de una fórmula.

Definimos \texttt{(aridadP p)} que determina la aridad del
predicado \texttt{p}.
\begin{code}
aridadP :: Form -> Int
aridadP (Atom str xs) = length xs
\end{code}

Definimos \texttt{(esPredicado f)} que determina si \texttt{f}
es un predicado.

\index{\texttt{esPredicado}}
\begin{code}
esPredicado :: Form -> Bool
esPredicado (Atom str []) = False
esPredicado (Atom str ts) = True
esPredicado _ = False
\end{code}

Calculamos el conjunto de los predicados de una fórmula \texttt{f}
definiendo la función \texttt{(predicadosForm f)}.

\index{\texttt{predicadosForm}}
\begin{code}
predicadosForm :: Form -> [Form]
predicadosForm p@(Atom str _) = if esPredicado p then [p] else []
predicadosForm (Neg f)        = predicadosForm f
predicadosForm (Impl f1 f2)   = 
    predicadosForm f1 `union` predicadosForm f2
predicadosForm (Equiv f1 f2)  = 
    predicadosForm f1 `union` predicadosForm f2
predicadosForm (Conj fs)      = nub (concatMap predicadosForm fs)
predicadosForm (Disy fs)      = nub (concatMap predicadosForm fs)
predicadosForm (PTodo x f)    = predicadosForm f
predicadosForm (Ex x f)       = predicadosForm f
\end{code}

Esta función repite el mismo predicado si tiene distintos argumentos,
como por ejemplo 

\begin{sesion}
ghci> predicadosForm formula_2
[R[x,y],R[x,z],R[z,y]]
\end{sesion}

Por lo tanto, definimos \texttt{(predForm f)} que obtiene
los símbolos de predicado sin repeticiones.

\begin{code}
predForm :: Form -> [Form]
predForm = noRep . predicadosForm
    where
      noRep [] = []
      noRep ((Atom st t):ps) = 
          if null ([ Atom str ts  | (Atom str ts) <- ps, str== st] )
          then (Atom st t):(noRep ps) else noRep ps
\end{code}

Así obtenemos

\begin{sesion}
ghci> predForm formula_2
[R[z,y]]
\end{sesion}

Finalmente, necesitamos aplicar los símbolos de predicado al
universo de Herbrand correspondiente.

Definimos las funciones \texttt{(aplicaPred p ts)} y su generalización 
\texttt{(apPred ps ts)} para aplicar los simbolos de predicado.

\index{\texttt{aplicaPred}}
\begin{code}
aplicaPred :: Form -> [Termino] -> Form
aplicaPred (Atom str _) ts = Atom str ts
\end{code}

\index{\texttt{apPred}}
\begin{code}
apPred :: [Form] -> [Termino] -> [Form]
apPred [] ts = []
apPred (p:ps) ts= map (aplicaPred p) (subconjuntosTam (aridadP p) ts) 
                            ++ apPred ps ts
\end{code}

Definimos la función \texttt{(baseHerbrand n f)}

\index{\texttt{baseHerbrand}}
\begin{code}
baseHerbrand :: (Eq a, Num a) => a -> Form -> [Form]
baseHerbrand n f = apPred (predForm f) (univHerbrand n f)
\end{code}
