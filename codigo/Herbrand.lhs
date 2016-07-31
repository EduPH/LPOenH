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


Para poder construir de manera correcta el universo de Herbrand
necesitamos que la fórmula no tenga variables repetidas entre las
variables libres y las ligadas. Por ello, repetimos la misma estructura
que en la forma de skolem, pero estableciendo los términos de skolem
como constantes, sin indicar la variable de la que dependían.

\begin{code}
terSk :: Show a => a -> t -> Termino
terSk k vs = Ter ("sk" ++ show k) []

skf1 :: Form -> [Variable] -> Bool -> Int -> (Form,Int)
skf1 (Atom n ts) _ _ k =
  (Atom n ts,k)
skf1 (Conj fs) vs pol k =
  (Conj fs',j)
  where (fs',j) = skfs1 fs vs pol k
skf1 (Disy fs) vs pol k =
  (Disy fs', j)
  where (fs',j) = skfs1 fs vs pol k
skf1 (PTodo x f) vs True k =
  (PTodo x f',j)
  where vs'    = insert x vs
        (f',j) = skf1 f vs' True k
skf1 (PTodo x f) vs False k =
  skf (sustitucionForm b f) vs False (k+1)
  where b = [(x,terSk k vs)]
skf1 (Ex x f) vs True k =
  skf (sustitucionForm b f) vs True (k+1)
  where b = [(x,terSk k vs)]
skf1 (Ex x f) vs False k =
  (Ex x f',j)
  where vs' = insert x vs
        (f',j) = skf1 f vs' False k
skf1 (Neg f) vs pol k =
  (Neg f',j)
  where (f',j) = skf1 f vs (not pol) k

skfs1 :: [Form] -> [Variable] -> Bool -> Int -> ([Form],Int)
skfs1 [] _ _ k        = ([],k)
skfs1 (f:fs) vs pol k = (f':fs',j)
  where (f',j1) = skf1  f  vs pol k
        (fs',j) = skfs1 fs vs pol j1


sk1 :: Form -> Form
sk1 f = fst (skf1 f [] True 0)

sinVariablesRep :: Form -> Form
sinVariablesRep = sk1 . elimImpEquiv
\end{code}




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

Definimos \texttt{(constForm fun f)} que según la función \texttt{fun}
que apliquemos tendrá dos funciones posibles. 

\index{\texttt{constForm}}
\begin{code}
constForm :: Eq a => (Termino -> [a]) -> Form -> [a]
constForm fun (Atom _ ts)   =  nub (concat [fun t | t <- ts])
constForm fun (Neg f)       =  constForm fun f
constForm fun (Impl f1 f2)  = (constForm fun f1) `union` (constForm fun f2)
constForm fun (Equiv f1 f2) = (constForm fun f1) `union` (constForm fun f2)
constForm fun (Conj fs)     = nub (concatMap (constForm fun) fs)
constForm fun (Disy fs)     = nub (concatMap (constForm fun) fs)
constForm fun (PTodo x f)   = constForm fun f
constForm fun (Ex x f)      = constForm fun f
\end{code}

Si como función auxiliar de \texttt{constForm} empleamos \texttt{constDeTerm}
obtendremos las constantes de la fórmula. Por ejemplo

\begin{sesion}
ghci> Atom "P" [a,tx]
P[a,x]
ghci> constForm constDeTerm (Atom "P" [a,tx])
[a]
ghci> Conj [Atom "P" [a, Ter "f" [tx,b]], Atom "R" [Ter "g" [tx,ty],c]]
(P[a,f[x,b]]⋀R[g[x,y],c])
ghci> constForm constDeTerm (Conj [Atom "P" [a, Ter "f" [tx,b]], 
                                   Atom "R" [Ter "g" [tx,ty],c]])
[a,b,c]
\end{sesion}

Definimos la función \texttt{termAConst t} que devuelve devuelve las constantes
y las variables como constantes.

\index{\texttt{termAConst}}
\begin{code}
termAConst :: Termino -> [Termino]
termAConst (Var (Variable str i) ) = [Ter str []]
termAConst c@(Ter _ []) = [c]
termAConst (Ter str (t:ts)) | esConstante t = t: aux (Ter str ts)
                            | otherwise = 
                                 termAConst t ++ aux (Ter str ts)
                             where
                               aux (Ter _ []) = []
                               aux t = termAConst t
\end{code}
                           
Si empleamos \texttt{termAConst} como función auxiliar de \texttt{constForm}
obtendremos una lista de las constantes de la fórmula, así como las variables
como constantes nuevas.


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
    map (aplicaFunAConst f) (subconjuntosTam (aridadF f) cs) 
                            ++ aplicaFun fs cs
\end{code}

Así podemos ya obtener el universo de Herbrand de una fórmula
\texttt{f} definiendo \texttt{(univHerbrand n f)}

\index{\texttt{univHerbrand}}
\begin{code}
univHerbrand :: (Eq a, Num a) => a -> Form -> Universo Termino
univHerbrand 0 f =  constForm termAConst (sinVariablesRep f)
univHerbrand 1 f = 
    nub (univHerbrand 0 f ++ aplicaFun (funForm f) (univHerbrand 0 f))
univHerbrand n f = 
    nub (univHerbrand (n-1) f ++ aplicaFun (funForm f)  
        (univHerbrand (n-1) f))
\end{code}


Por ejemplo

\begin{sesion}
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> univHerbrand 0 formula2
[x,y,sk0]
ghci> formula3
(R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> univHerbrand 0 formula3
[x,y,sk0]
ghci> formula4
∃x R[cero,x]
ghci> univHerbrand 0 formula4
[cero,sk0]
λ> formula5
(∀x P[x]⟹∀y Q[x,y])
ghci> univHerbrand 0 formula5
[sk0,x,y]
\end{sesion}

\begin{nota}
  En el universo de Herbrand no aparecen variables. Aunque
  hemos mantenido los nombres de las variables ahora son 
  constantes.
\end{nota}

\begin{Prop}
  $\mathcal{UH}$ es finito si y sólo si no tiene símbolos de función.
\end{Prop}

Definimos fórmulas con términos funcionales para el ejemplo

\begin{code}
formula6, formula7 :: Form
formula6 = PTodo x (Atom "P" [Ter "f" [tx]])
formula7 = PTodo x (Atom "P" [Ter "f" [tx,ty]])
\end{code}

quedando como ejemplo 

\begin{sesion}
ghci> formula6
∀x P[f[x]]
ghci> univHerbrand 5 formula6
[x,f[x],f[f[x]],f[f[f[x]]],f[f[f[f[x]]]],f[f[f[f[f[x]]]]]]
ghci> formula7
∀x P[f[x,y]]
ghci>  univHerbrand 2 formula7
[x,y,f[x,y],f[y,x],f[f[x,y],f[y,x]],f[f[y,x],f[x,y]],
f[y,f[y,x]],f[f[y,x],y],f[y,f[x,y]],f[f[x,y],y],
f[x,f[y,x]],f[f[y,x],x],f[x,f[x,y]],f[f[x,y],x]]
\end{sesion}

Hay que tener en cuenta que se dispara la cantidad de elementos del universo de
Herbrand ante términos funcionales con aridad grande.

\begin{sesion}
length (univHerbrand 0 formula7)  ==  2
length (univHerbrand 1 formula7)  ==  4
length (univHerbrand 2 formula7)  ==  14
length (univHerbrand 3 formula7)  ==  184
\end{sesion}

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
  predForm y preddicadosForm.}

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
apPred (p:ps) ts = map (aplicaPred p) (subconjuntosTam (aridadP p) ts) 
                   ++ apPred ps ts
\end{code}

\comentario{Añadir ejemplos de aplicaPred y apPred.}

Definimos la función \texttt{(baseHerbrand n f)}

\index{\texttt{baseHerbrand}}
\begin{code}
baseHerbrand :: (Eq a, Num a) => a -> Form -> [Form]
baseHerbrand n f = apPred (predForm f) (univHerbrand n f)
\end{code}

Algunos ejemplos

\begin{sesion}
ghci> baseHerbrand 0 formula2
[R[y,sk0],R[sk0,y],R[x,sk0],R[sk0,x],R[x,y],R[y,x]]
ghci> baseHerbrand 0 formula3
[R[y,sk0],R[sk0,y],R[x,sk0],R[sk0,x],R[x,y],R[y,x]]
ghci> baseHerbrand 0 formula4
[R[cero,sk0],R[sk0,cero]]
ghci> baseHerbrand 0 formula5
[P[y],P[x],P[sk0],Q[x,y],Q[y,x],Q[sk0,y],Q[y,sk0],Q[sk0,x],Q[x,sk0]]
ghci> univHerbrand 0 (Conj [(Atom "P" [a]),(Atom "P" [b]),(Atom "P" [c])])
[a,b,c]
ghci> baseHerbrand 0 (Conj [(Atom "P" [a]),(Atom "P" [b]),(Atom "P" [c])])
[P[c],P[b],P[a]]
\end{sesion}

\comentario{Aplicar baseHerbrand a los ejemplos de LMF.}

Podemos hacer un análisis de la fórmula 6, calculando sus constantes, símbolos
funcionales y símbolos de predicado. Así como el universo de Herbrand y la base
de Herbrand.

\begin{sesion}
ghci> formula6
∀x P[f[x]]
ghci> constForm formula6
[]
ghci> funForm formula6
[f[x]]
ghci> predForm formula6
[P[f[x]]]
ghci> univHerbrand 0 formula6
[x]
ghci> univHerbrand 1 formula6
[x,f[x]]
ghci> univHerbrand 2 formula6
[x,f[x],f[f[x]]]
ghci> univHerbrand 3 formula6
[x,f[x],f[f[x]],f[f[f[x]]]]
ghci> univHerbrand 4 formula6
[x,f[x],f[f[x]],f[f[f[x]]],f[f[f[f[x]]]]]
ghci> baseHerbrand 0 formula6
[P[x]]
ghci> baseHerbrand 1 formula6
[P[f[x]],P[x]]
ghci> baseHerbrand 2 formula6
[P[f[f[x]]],P[f[x]],P[x]]
ghci> baseHerbrand 3 formula6
[P[f[f[f[x]]]],P[f[f[x]]],P[f[x]],P[x]]
ghci> baseHerbrand 4 formula6
[P[f[f[f[f[x]]]]],P[f[f[f[x]]]],P[f[f[x]]],P[f[x]],P[x]]
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

