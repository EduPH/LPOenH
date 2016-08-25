\begin{code}
module Tableros where
import DNH
import PTLP
import LPH
import Debug.Trace     
\end{code}

Hemos importado la librería \texttt{Debug.Trace} porque emplearemos la función
\texttt{trace}. Esta función tiene como argumentos una cadena de caracteres,
una función, y un valor sobre el que se aplica la función. Por ejemplo

\begin{sesion}
ghci> trace ("aplicando even a x = " ++ show 3) (even 3)
aplicando even a x = 3
False
\end{sesion}

A lo largo de esta sección trabajaremos con fórmulas en su forma de Skolem.

El método de tableros se suele representar en forma de árbol, por ello
definiremos el tipo de dato \texttt{Nodo}. 

\begin{code}
data Nodo = Nd Indice [Termino] [Termino] [Form]
            deriving Show
\end{code}

Donde la primera lista de términos representa los literales positivos,
la segunda lista de términos representa los negativos, y la lista de fórmulas 
son aquellas ligadas a los términos de las listas anteriores.


Definimos los tableros como una lista de nodos.

\begin{code}
type Tablero = [Nodo]
\end{code}

Necesitamos poder reconocer las dobles negaciones, para ello
definimos la función \texttt{dobleNeg f}.

\index{\texttt{dobleNeg}}
\begin{code}
dobleNeg (Neg (Neg f)) = True
dobleNeg _             = False
\end{code}

Una función auxiliar de conversión de literales a términos es
\texttt{listeralATer t}.

\index{\texttt{literalATer}}
\begin{code}
literalATer :: Form -> Termino
literalATer (Atom n ts)       = Ter n ts
literalATer (Neg (Atom n ts)) = Ter n ts
\end{code}

Definimos la función \texttt{(componentes f)} que determina los componentes de
una fórmula \texttt{f}.

\index{\texttt{componentes}}
\begin{code}
componentes :: Form -> [Form]
componentes (Conj fs)       = fs
componentes (Disy fs)       = fs
componentes (Neg (Conj fs)) = [Neg f | f <- fs]
componentes (Neg (Disy fs)) = [Neg f | f <- fs]
componentes (Neg (Neg f))   = [f]
componentes (PTodo x f)     = [f]
componentes (Neg (Ex x f))  = [Neg f]
\end{code}

Por ejemplo,

\begin{sesion}
ghci> componentes (skolem (tab1))
[¬¬(p⋀[q]),¬(p⋁[q])]
ghci> componentes (skolem (tab2))
[(¬p⋁[q]),(¬q⋁[r]),¬(¬p⋁[r])]
\end{sesion}

Definimos la función \texttt{(varLigada f)} que devuelve la variable ligada de
la fórmula \texttt{f}

\index{\texttt{varLigada}}
\begin{code}
varLigada :: Form -> Variable
varLigada (PTodo x f)    = x
varLigada (Neg (Ex x f)) = x
\end{code}

Definimos la función \texttt{(descomponer f)} que determina los cuantificadores
universales de \texttt{f}.

\index{\texttt{descomponer}}
\begin{code}
descomponer :: Form -> ([Variable],Form)
descomponer = descomp [] where
  descomp xs f | gamma f   = descomp (xs ++ [x]) g
               | otherwise = (xs,f)
    where x   = varLigada f
          [g] = componentes f
\end{code}

Por ejemplo,

\begin{sesion}
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> descomponer formula2
([x,y],(R[x,y]⟹∃z (R[x,z]⋀[R[z,y]])))
ghci> formula3
(R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> descomponer formula3
([],(R[x,y]⟹∃z (R[x,z]⋀[R[z,y]])))
ghci> formula4
∃x R[cero,x]
ghci> descomponer formula4
([],∃x R[cero,x])
\end{sesion}


Definimos \texttt{(ramificacion nodo)} que ramifica un nodo aplicando          
las equivalencias adecuadas.

\index{\texttt{ramificacion}}
\begin{code}
ramificacion :: Nodo -> Tablero
ramificacion (Nd i pos neg []) = [Nd i pos neg []]
ramificacion (Nd i pos neg (f:fs)) 
  | atomo f    = if literalATer f `elem` neg
                 then []
                 else [Nd i ( literalATer f : pos) neg fs]
  | negAtomo f = if literalATer f `elem` pos
                 then []
                 else [Nd i pos (literalATer f : neg) fs]
  | dobleNeg f = [Nd i pos neg (componentes f ++ fs)]
  | alfa f     = [Nd i pos neg (componentes f ++ fs)]
  | beta f     = [Nd (i++[n]) pos neg (f':fs)
                 | (f',n) <- zip (componentes f) [0..]]
  | gamma f    = [Nd i pos neg (f':(fs++[f]))]
  where
    (xs,g) = descomponer f
    b      = [(Variable nombre j, Var (Variable nombre i)) 
             | (Variable nombre j) <- xs]
    f'     = sustitucionForm b g
\end{code}

Debido a que pueden darse la infinitud de un árbol por las fórmulas
gamma, definimos otra función \texttt{(ramificacionP k nodo)} que ramifica
un nodo teniendo en cuenta la profundidad.

\index{\texttt{ramificacionP}}
\begin{code}
ramificacionP :: Int -> Nodo -> (Int,Tablero)
ramificacionP k nodo@(Nd i pos neg []) = (k,[nodo])
ramificacionP k (Nd i pos neg (f:fs))
  | atomo    f = if literalATer f `elem` neg
                 then (k,[])
                 else (k,[Nd i (literalATer f : pos) neg fs])
  | negAtomo f = if literalATer f `elem` neg
                 then (k,[]) 
                 else (k,[Nd i pos (literalATer f : neg) fs])
  | dobleNeg f = (k,[Nd i pos neg (componentes f ++ fs)])
  | alfa     f = (k,[Nd i pos neg (componentes f ++ fs)])
  | beta     f = (k,[Nd (i++[n]) pos neg (f':fs)
                    | (f',n) <- zip (componentes f) [0..] ])
  | gamma    f = (k-1, [Nd i pos neg (f':(fs++[f]))])
  where 
    (xs,g) = descomponer f
    b      = [(Variable nombre j, Var (Variable nombre i))
             | (Variable nombre j) <- xs]
    f'     = sustitucionForm b g
\end{code}

\begin{Def}
  Un nodo está completamente \textbf{expandido} si no se puede seguir ramificando
\end{Def}

Se define en Haskell

\index{\texttt{nodoExpandido}}
\begin{code}
nodoExpandido :: Nodo -> Bool
nodoExpandido (Nd i pos neg []) = True
nodoExpandido _                 = False
\end{code}

Definimos la función \texttt{(expandeTablero n tab)} que desarrolla un tablero
a una profundidad \texttt{n}.

\index{\texttt{expandeTablero}}
\begin{code}
expandeTablero :: Int -> Tablero -> Tablero
expandeTablero 0 tab = tab
expandeTablero _ []  = []
expandeTablero n (nodo:nodos) 
  | nodoExpandido nodo = nodo : expandeTablero n nodos
  | k == n             = expandeTablero n (nuevoNodo ++ nodos)
  | otherwise          = expandeTablero (n-1) (nodos ++ nuevoNodo)
  where (k,nuevoNodo) = ramificacionP n nodo
\end{code}

Para una visualización más gráfica, definimos \texttt{(expandeTableroG)}
empleando la función \texttt{(trace)}.

\index{\texttt{expandeTableroG}}
\begin{code}
expandeTableroG :: Int -> Tablero -> Tablero
expandeTableroG 0 tab = tab
expandeTableroG _ [] = []
expandeTableroG n (nodo:nodos) 
  | nodoExpandido nodo =
      trace (show nodo ++ "\n\n") (nodo : expandeTableroG n nodos)
  | k == n =
      trace (show nodo ++ "\n\n") (expandeTableroG k 
                                  (nuevoNodo ++ nodos))
  | otherwise =
      trace (show nodo ++"\n\n") (expandeTableroG (n-1) 
                                 (nodos ++ nuevoNodo))
  where (k, nuevoNodo) = ramificacionP n nodo
\end{code}

Definimos la función \texttt{(esNodoCerrado)} para comprobar si hay hoja
cerrada.

\index{\texttt{esNodoCerrado}}
\begin{code}
esNodoCerrado :: Nodo -> [Sust]
esNodoCerrado (Nd _ pos neg _) =
    concat [ unificadoresTerminos p n | p <- pos,
                                        n <- neg ]
\end{code}

Definimos las funciones auxiliares \texttt{(sustNodo nd)} y \texttt{(sustTab
  tb)} que aplican sustituciones a nodos y tableros.

\index{\texttt{sustNodo}}
\index{\texttt{susTab}}
\begin{code}
sustNodo :: Sust -> Nodo -> Nodo
sustNodo b (Nd i pos neg f) =
  Nd i (susTerms b pos) (susTerms b neg) (sustitucionForms b f)

susTab :: Sust -> Tablero -> Tablero
susTab = map . sustNodo
\end{code}

Se define \texttt{esCerrado} para determinar si un tablero es cerrado.

\index{\texttt{esCerrado}}
\begin{code}
esCerrado :: Tablero -> [Sust]
esCerrado []     = [identidad]
esCerrado [nodo] = esNodoCerrado nodo
esCerrado (nodo:nodos) = 
  concat [esCerrado (susTab s nodos) | s <- esNodoCerrado nodo ]
\end{code}

Dada una fórmula es necesario crear un tablero inicial para posteriormente
desarrollarlo. Lo hacemos mediante la función \texttt{(tableroInicial f)}.

\index{\texttt{tableroInicial}}
\begin{code}
tableroInicial :: Form -> Tablero
tableroInicial f = [Nd [] [] [] [f]]
\end{code}

Por ejemplo,

\begin{sesion}
ghci> tab1
¬((p⋁q)⟹(p⋀q))
ghci> tableroInicial tab1
[Nd [] [] [] [¬((p⋁[q])⟹(p⋀[q]))]]
\end{sesion}

La función \texttt{(refuta k f)} intenta refutar la fórmula \texttt{f} con un
tablero de profundidad \texttt{k}.

\index{\texttt{refuta}}
\begin{code}
refuta :: Int -> Form -> Bool
refuta k f = esCerrado tab /= []
  where tab = expandeTablero k (tableroInicial f)
\end{code}

\begin{nota}
  Se puede emplear tambien \texttt{expandeTableroG}, por ello se deja comentado
  para su posible uso.
\end{nota}

\begin{Def}
  Una fórmula $F$ es un \textbf{teorema} mediante tableros semánticos
  si tiene una prueba mediante tableros; es decir, si $\neg F$ tiene un
  tablero completo cerrado
\end{Def}
  
Finalmente, podemos determinar si una fórmula es un teorema y si es
satisfacible mediante las funciones \texttt{(esTeorema n f)} y
\texttt{(satisfacible n f)}.

\index{\texttt{esTeorema}}
\index{\texttt{satisfacible}}
\begin{code}
esTeorema, satisfacible :: Int -> Form -> Bool
esTeorema n = refuta n . skolem . Neg
satisfacible n = not . refuta n . skolem
\end{code}

Por ejemplo tomando \texttt{tautologia1} y la ya usada anteriormente
\texttt{formula2}

\begin{code}
tautologia1 :: Form
tautologia1 = Disy [Atom "P" [tx], Neg (Atom "P" [tx])]
\end{code}

se tiene

\begin{sesion}
ghci> tautologia1
(P[x]⋁¬P[x])
ghci> esTeorema 1 tautologia1
True
ghci> formula2
∀x ∀y (R[x,y]⟹∃z (R[x,z]⋀R[z,y]))
ghci> esTeorema 20 formula2
False
ghci> tab1
¬((p⋁q)⟹(p⋀q))
ghci> esTeorema 20 tab1
False
ghci> satisfacible 1 tab1
True
ghci> tab2
((p⟹q)⋀((q⟹r)⋀¬(p⟹r)))
ghci> esTeorema 20 tab2
False
ghci> satisfacible 20 tab2
False
\end{sesion}

\begin{Teo}
  El cálculo de tableros semánticos es adecuado y completo.
\end{Teo}

\begin{Def}
  Una fórmula $F$ es \textbf{deducible} a partir del conjunto de fórmulas $S$
  si exite un tablero completo cerrado de la conjunción de $S$ y $\neg F$. Se
  representa por $S \vdash_{Tab} F$.
\end{Def}

\comentario{Explicar más el método de tableros con polaridad.}

\comentario{Comparar la implementación con la de Ben Ari que se encuentra en  
  \href{https://github.com/motib/mlcs/blob/master/fol/tabl.pro}
       {\url{https://github.com/motib/mlcs/blob/master/fol/tabl.pro}}}
