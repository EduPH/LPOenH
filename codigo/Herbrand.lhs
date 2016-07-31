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
  Una \textbf{fórmula básica} es una fórmula sin variables ni cuantificadores.
\end{Def}

\section{Universo de Herbrand}

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


A continuación caracterizamos las constantes. Definimos la
función \texttt{(esConstante c)}.

\index{\texttt{esConstante}}
\begin{code}
esConstante :: Termino -> Bool
esConstante (Ter _ []) = True
esConstante _          = False
\end{code}

Un par de ejemplos

\begin{sesion}
esConstante a   ==  True
esConstante tx  ==  False
\end{sesion}


Definimos la función \texttt{(constDeTerm t)} que determine las de un
término \texttt{t}.

\index{\texttt{constDeTerm}}
\begin{code}
constDeTerm :: Termino -> [Termino]
constDeTerm (Var _) = []
constDeTerm c@(Ter _ []) = [c]
constDeTerm (Ter str (t:ts)) | esConstante t = t: aux (Ter str ts)
                             | otherwise = 
                                 constDeTerm t ++ aux (Ter str ts)
                             where
                               aux (Ter _ []) = []
                               aux t = constDeTerm t
\end{code}

\begin{nota}
  La función \texttt{aux} evita que en la recursión consideremos
  un término funcional como constante al quedarse vacía la lista
  de elementos a los que se aplica.
\end{nota}

Por ejemplo

\begin{sesion}
ghci> Ter "f" [Ter "a" [] , Ter "b" [] , Ter "g" [tx, Ter "c" []]]
f[a,b,g[x,c]]
ghci> constDeTerm (Ter "f" [Ter "a" [] , Ter "b" [] , Ter "g" [tx, Ter "c" []]])
[a,b,c]
\end{sesion}

Definimos \texttt{(constForm  f)} para determinar las constantes de
\texttt{f}. 

\index{\texttt{constForm}}
\begin{code}
constForm :: Form -> [Termino]
constForm  (Atom _ ts)   =  nub (concat [constDeTerm t | t <- ts])
constForm  (Neg f)       = constForm f
constForm  (Impl f1 f2)  = constForm f1 `union` constForm f2
constForm  (Equiv f1 f2) = constForm f1 `union` constForm f2
constForm  (Conj fs)     = nub (concatMap constForm fs)
constForm  (Disy fs)     = nub (concatMap constForm fs)
constForm  (PTodo x f)   = constForm  f
constForm  (Ex x f)      = constForm  f
\end{code}

Si como función auxiliar de \texttt{constForm} empleamos \texttt{constDeTerm}
obtendremos las constantes de la fórmula. Por ejemplo

\begin{sesion}
ghci> Atom "P" [a,tx]
P[a,x]
ghci> constForm (Atom "P" [a,tx])
[a]
ghci> Conj [Atom "P" [a, Ter "f" [tx,b]], Atom "R" [Ter "g" [tx,ty],c]]
(P[a,f[x,b]]⋀R[g[x,y],c])
ghci> constForm  (Conj [Atom "P" [a, Ter "f" [tx,b]], 
                  Atom "R" [Ter "g" [tx,ty],c]])
[a,b,c]
\end{sesion}


Definimos \texttt{(esFuncion f)} y \texttt{(funForm f)} para obtener todos los
símbolos funcionales que aparezcan en la fórmula \texttt{f}.

\index{\texttt{esFuncion}}
\begin{code}
esFuncion :: Termino -> Bool
esFuncion (Ter _ xs) | not (null xs) = True
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

Por ejemplo

\begin{sesion}
ghci> funForm (Conj [Atom "P" [a, Ter "f" [tx,b]], Atom "R" [Ter "g" [tx,ty],c]])
[f[x,b],g[x,y]]
\end{sesion}


\begin{Def}
  La \textbf{aridad} de un operador $f(x_1,\dots,x_n)$ es el número número de
  argumentos a los que se aplica.
\end{Def}

Definimos  \texttt{(aridadF t)} para calcular la aridad del término \texttt{t}.

\index{\texttt{aridadF}}
\begin{code}
aridadF :: Termino -> Int
aridadF (Ter _ ts) = length ts
\end{code}

También necesitamos definir dos funciones auxiliares que apliquen los símbolos
funcionales a las constantes del universo de Herbrand. Las funciones son
\texttt{(aplicaFunAConst f c)} que aplica el símbolo funcional \texttt{f} a la
constante \texttt{c} y \texttt{(aplicaFun fs cs)} que es una generalización a
listas de la anterior.

\index{\texttt{aplicaFunAConst}}
\index{\texttt{aplicaFun}}
\begin{code}
aplicaFunAConst (Ter s _) = Ter s  

aplicaFun [] cs = []
aplicaFun (f:fs) cs = 
    map (aplicaFunAConst f) (variacionesR (aridadF f) cs) 
                            ++ aplicaFun fs cs
\end{code}

Así podemos ya obtener el universo de Herbrand de una fórmula
\texttt{f} definiendo \texttt{(univHerbrand n f)}

\index{\texttt{univHerbrand}}
\begin{code}
univHerbrand :: (Eq a, Num a) => a -> Form -> Universo Termino
univHerbrand 0 f = if  constForm  f /= [] then constForm f
                   else [a]
univHerbrand n f = 
    nub (univHerbrand (n-1) f ++ aplicaFun (funForm f)  
        (univHerbrand (n-1) f))
\end{code}

\comentario{Faltan aquellos elementos funcionales con aridad mayor que 1
            que repitan constante}

Por ejemplo
\begin{code}
u = Variable "u" []
tu = Var u
\end{code}
\begin{sesion}
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> univHerbrand 0 formula2
[a]
ghci> 
ghci> Conj [Disy [Atom "P" [a],Atom "P" [b]],
            Disy [Neg (Atom "P" [b]),Atom "P" [c]],
            Impl (Atom "P" [a]) (Atom "P" [c])]
((P[a]⋁P[b])⋀((¬P[b]⋁P[c])⋀(P[a]⟹P[c])))
ghci> univHerbrand 0 (Conj [Disy [Atom "P" [a],Atom "P" [b]],
                            Disy [Neg (Atom "P" [b]),Atom "P" [c]],
                            Impl (Atom "P" [a]) (Atom "P" [c])])
[a,b,c]

ghci> Conj [PTodo x (PTodo y (Impl (Atom "Q" [b,tx]) 
                    (Disy [Atom "P" [a],Atom "R" [ty]]))),
                     Impl (Atom "P" [b]) (Neg (Ex z (Ex u (Atom "Q" [tz,tu]))))]
(∀x ∀y (Q[b,x]⟹(P[a]⋁R[y]))⋀(P[b]⟹¬∃z ∃u Q[z,u]))
ghci> univHerbrand 0 (Conj [PTodo x (PTodo y (Impl (Atom "Q" [b,tx]) 
                     (Disy [Atom "P" [a],Atom "R" [ty]]))),
                      Impl (Atom "P" [b]) (Neg (Ex z (Ex u (Atom "Q" [tz,tu]))))])
[b,a]
\end{sesion}


\begin{Prop}
  $\mathcal{UH}$ es finito si y sólo si no tiene símbolos de función.
\end{Prop}

Definimos fórmulas con términos funcionales para el ejemplo

\begin{code}
formula6, formula7 :: Form
formula6 = PTodo x (Atom "P" [Ter "f" [tx]])
formula7 = PTodo x (Atom "P" [Ter "f" [a,b]])
\end{code}

quedando como ejemplo 

\begin{sesion}
ghci> formula6
∀x P[f[x]]
ghci> univHerbrand 5 formula6
[a,f[a],f[f[a]],f[f[f[a]]],f[f[f[f[a]]]],f[f[f[f[f[a]]]]]]
ghci> univHerbrand 0 formula7
[a,b]
ghci> univHerbrand 1 formula7
[a,b,f[a,a],f[a,b],f[b,a],f[b,b]]
ghci> univHerbrand 2 formula7
[a,b,f[a,a],f[a,b],f[b,a],f[b,b],f[a,f[a,a]],f[a,f[a,b]],f[a,f[b,a]],f[a,f[b,b]],
f[b,f[a,a]],f[b,f[a,b]],f[b,f[b,a]],f[b,f[b,b]],f[f[a,a],a],f[f[a,a],b],f[f[a,a],
f[a,a]],f[f[a,a],f[a,b]],f[f[a,a],f[b,a]],f[f[a,a],f[b,b]],f[f[a,b],a],f[f[a,b],b],
f[f[a,b],f[a,a]],f[f[a,b],f[a,b]],f[f[a,b],f[b,a]],f[f[a,b],f[b,b]],f[f[b,a],a],
f[f[b,a],b],f[f[b,a],f[a,a]],f[f[b,a],f[a,b]],f[f[b,a],f[b,a]],f[f[b,a],f[b,b]],
f[f[b,b],a],f[f[b,b],b],f[f[b,b],f[a,a]],f[f[b,b],f[a,b]],f[f[b,b],f[b,a]],f[f[b,b],f[b,b]]]
\end{sesion}

Hay que tener en cuenta que se dispara la cantidad de elementos del universo de
Herbrand ante términos funcionales con aridad grande.

\begin{sesion}
length (univHerbrand 0 formula7)  ==  2
length (univHerbrand 1 formula7)  ==  6
length (univHerbrand 2 formula7)  ==  38
length (univHerbrand 3 formula7)  ==  1446
\end{sesion}


\comentario{Comprobar todos los ejemplos}

\section{Base de Herbrand}

\begin{Def}
  La \textbf{base de Herbrand} $\mathcal{BH}(L)$ de un lenguaje $L$ es el
  conjunto de átomos básicos de $L$.
\end{Def}

Con el objetivo de definir una función que obtenga la base de Herbrand;
necesitamos poder calcular el conjunto de símbolos de predicado de una fórmula.

Definimos \texttt{(aridadP f)} que determina la aridad del predicado de la
fórmula atómica \texttt{f}.

\begin{code}
aridadP :: Form -> Int
aridadP (Atom _ xs) = length xs
\end{code}

Definimos \texttt{(esPredicado f)} que determina si \texttt{f} es un predicado.

\index{\texttt{esPredicado}}
\begin{code}
esPredicado :: Form -> Bool
esPredicado (Atom _ []) = False
esPredicado (Atom _ _)  = True
esPredicado _           = False
\end{code}

Calculamos el conjunto de los predicados de una fórmula \texttt{f} definiendo
la función \texttt{(predicadosForm f)}.

\index{\texttt{predicadosForm}}
\begin{code}
predicadosForm :: Form -> [Form]
predicadosForm p@(Atom _ _)   = [p | esPredicado p]
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

Esta función repite el mismo predicado si tiene distintos argumentos, como por
ejemplo

\begin{sesion}
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> predicadosForm formula2
[R[x,y],R[x,z],R[z,y]]
\end{sesion}

Por lo tanto, definimos \texttt{(predForm f)} que obtiene los símbolos de
predicado sin repeticiones.

\begin{code}
predForm :: Form -> [Form]
predForm = noRep . predicadosForm
    where
      noRep [] = []
      noRep (Atom st t : ps) = 
          if null [Atom str ts  | (Atom str ts) <- ps, str== st]
          then Atom st t : noRep ps else noRep ps
\end{code}

Así obtenemos

\begin{sesion}
ghci> predForm formula2
[R[z,y]]
\end{sesion}

Podemos tambien obtener una lista de los símbolos de predicado definiendo
\texttt{(simbolosPred f)}

\index{\texttt{simbolosPred}}
\begin{code}
simbolosPred :: Form -> [Nombre]
simbolosPred f = [str | (Atom str _) <- ps]
    where ps = predForm f
\end{code}

\comentario{Definir directamente simbolosPred sin usar predForm y eliminar
  predForm y predicadosForm. Respuesta a comentario: La razón de no
  haber definido simbolosPred sin predForm y predicadosForm es por la
  necesidad de mantener la aridad del predicado para la definición de
  base de Herbrand.}

Finalmente, necesitamos aplicar los símbolos de predicado al universo de
Herbrand correspondiente.

Definimos las funciones \texttt{(aplicaPred p ts)} y su generalización 
\texttt{(apPred ps ts)} para aplicar los simbolos de predicado.

\index{\texttt{aplicaPred}}
\index{\texttt{apPred}}
\begin{code}
aplicaPred :: Form -> [Termino] -> Form
aplicaPred (Atom str _) = Atom str 

apPred :: [Form] -> [Termino] -> [Form]
apPred [] ts = []
apPred (p:ps) ts = map (aplicaPred p) (variacionesR (aridadP p) ts)
                   ++ apPred ps ts
\end{code}

Algunos ejemplos son

\begin{sesion}
ghci> aplicaPred (Atom "P" [tx]) [ty]
P[y]
ghci> aplicaPred (Atom "R" [tx,ty]) [tz,ty]
R[z,y]
ghci> apPred [Atom "P" [tx]] [tx,ty,tz]
[P[z],P[y],P[x]]
ghci> apPred [Atom "P" [tx], Atom "R" [tx,ty]] [tx,ty,tz]
[P[z],P[y],P[x],R[y,z],R[z,y],R[x,z],R[z,x],R[x,y],R[y,x]]
\end{sesion}

Definimos la función \texttt{(baseHerbrand n f)}

\index{\texttt{baseHerbrand}}
\begin{code}
baseHerbrand :: (Eq a, Num a) => a -> Form -> [Form]
baseHerbrand n f = nub (apPred (predForm f) (univHerbrand n f)) 
\end{code}

Algunos ejemplos

\begin{sesion}
ghci> baseHerbrand 0 (Conj [Disy [Atom "P" [a],Atom "P" [b]],        
                            Disy [Neg (Atom "P" [b]),Atom "P" [c]],                      
                            Impl (Atom "P" [a]) (Atom "P" [c])])
[P[c],P[b],P[a]

ghci> baseHerbrand 0 (Conj [PTodo x (PTodo y (Impl (Atom "Q" [b,tx])  
                  (Disy [Atom "P" [a],Atom "R" [ty]]))),      
                         Impl (Atom "P" [b]) (Neg (Ex z (Ex u (Atom "Q" [tz,tu]))))])
[R[a],R[b],P[a],P[b],Q[b,a],Q[a,b],R[b],R[a],P[b],P[a],Q[b,b],Q[a,a]]
\end{sesion}


Podemos hacer un análisis de la fórmula 6, calculando sus constantes, símbolos
funcionales y símbolos de predicado. Así como el universo de Herbrand y la base
de Herbrand.

\begin{sesion}

\end{sesion}

\comentario{Corregir el análisis de la base de Herbrand.}

\begin{Teo}
  $\mathcal{BH}(L)$ es finita si y sólo si $L$ no tiene símbolos de función.
\end{Teo}

\section{Interpretaciones de Herbrand}

\begin{Def}
  Una \textbf{interpretación de Herbrand} de una fórmula $F$ es una interpretación
  $\mathcal{I} = (\mathcal{U},I)$ tal que
  \begin{itemize}
  \item $\mathcal{U}$ es el universo de Herbrand de $F$.
  \item $I(c) = c$, para constante $c$ de $F$.
  \item $I(f) = f$, para cada símbolo funcional de $F$.
  \end{itemize}
\end{Def}

\section{Modelos de Herbrand}

\begin{Def}
  Un \textbf{modelo de Herbrand} de una fórmula $F$ es una interpretación de
  Herbrand de $F$ que es modelo de $F$.

  Un \textbf{modelo de Herbrand} de un conjunto de fórmulas $S$ es una interpretación de
  Herbrand de $S$ que es modelo de $S$.
\end{Def}

\comentario{Falta la definición de interpretación de Herbrand de un conjunto de fórmulas.}

\begin{nota}
  Los conjuntos de fórmulas pueden ser representados mediante
  \textbf{cláusulas} que no son más que fórmulas entre comas, donde las comas
  representan la conjunción. Posteriormente definiremos las cláusulas pero por
  ahora representamos conjuntos como conjunción de funciones.
\end{nota}

\comentario{Aclarar la nota sobre cláusulas.}

Definimos \texttt{(valHerbrand f)} para determinar si existe algún subconjunto
de la base de Herbrand que sea modelo de la fórmula \texttt{f}.

Para la recursión necesitamos la fórmula \texttt{(valorHerbrand f f)} pues hace
recursión en una de las \texttt{f} para luego calcular la base de Herbrand de
la otra.

\comentario{Aclarar el significado de valorHerbrand y añadir ejemplos.}

\index{\texttt{valorHerbrand}}
\begin{code}
valorHerbrand :: Form -> Form -> Int -> Bool
valorHerbrand p@(Atom str ts) f n =
  p `elem` baseHerbrand n f
valorHerbrand (Neg g) f n =
  not (valorHerbrand g f n)
valorHerbrand (Impl f1 f2) f n = 
  valorHerbrand f1 f n <= valorHerbrand f2 f n
valorHerbrand (Equiv f1 f2) f n =
  valorHerbrand f1 f n == valorHerbrand f2 f n
valorHerbrand (Conj fs) f n =
  all (==True) [valorHerbrand g f n | g <- fs]
valorHerbrand (Disy fs) f n =
  True `elem` [valorHerbrand g f n | g <- fs]
valorHerbrand (PTodo v g) f n =
  valorHerbrand g f n
valorHerbrand (Ex v g)  f n =
  valorHerbrand g f n
\end{code}

\begin{nota}
  Se puede cambiar la \texttt{n} de la base de Herbrand a la que se calcula la
  existencia de modelo. Eso es interesante para fórmulas con símbolos
  funcionales.
\end{nota}

\index{\texttt{valHerbrand}}
\begin{code}
valHerbrand :: Form -> Int -> Bool
valHerbrand g = valorHerbrand f f
  where f = skolem g
\end{code}

Añadimos un par de fórmulas para los ejemplos

\begin{code}
formula8 = Impl (Atom "P" [tx]) (Atom "Q" [tx])
formula9 = Conj [Atom "P" [tx], Neg (Atom "P" [tx])]
\end{code}

\begin{sesion}
ghci> valHerbrand formula8 0
True
ghci> valHerbrand formula9 0
False
ghci> valHerbrand formula6 0
False
ghci> valHerbrand formula6 1
True
ghci> valHerbrand formula2 0
False
ghci> valHerbrand formula2 1
True
\end{sesion}

La fórmula 9 es una contradicción, es decir, no tiene 
ningún modelo. Podemos comprobarlo mediante tableros

\begin{sesion}
ghci> satisfacible 1 formula9
False
\end{sesion}

