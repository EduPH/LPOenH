\section{Representación de modelos}

El contenido de esta sección se encuentra en el módulo \texttt{Modelo}.

\begin{code}
module Modelo where
import Dominio
import PFH
\end{code}

Trabajaremos con modelos a través de un dominio de entidades; en concreto,
aquellas del módulo \texttt{Dominio}. Cada entidad de dicho módulo representa
un sujeto. Cada sujeto cumplirá distintos predicados.

\begin{Def}
  Una interpretación es una aplicación $I: VP \rightarrow Bool$, donde $VP$
  representa el conjunto de las variables proposicionales.
\end{Def}

Una interpretación toma valores para las variables proposicionales, y se
evalúan en una fórmula. Determinando si la fórmula es verdadera o falsa. Se
definirá más adelante mediante las funciones \texttt{valor} y \texttt{val}.

\begin{Def}
  Un modelo de una fórmula $F$ es una interpretación en la que el valor de
  $F$ es verdadero.
\end{Def}

\begin{Def}
  Una fórmula es satisfacible si existe alguna interpretación para la que
  sea verdadera, es decir, algún modelo.
\end{Def}

\begin{Def}
  Una fórmula es insatisfacible si no tiene ningún modelo.
\end{Def}

A continuación damos un ejemplo de predicados lógicos para la clasificación
botánica. La cual no es completa, pero da una idea de la potencia de Haskell
para este tipo de uso.

Primero definimos los elementos que pretendemos clasificar, y que cumplirán los
predicados. Para ello, definimos como función cada elemento a clasificar y le
asociamos una entidad.

\begin{code}
adelfas, aloeVera, boletus, cedro, chlorella, girasol, guisante, helecho, 
  hepatica, jaramago, jazmin, lenteja, loto, magnolia, maiz, margarita, 
  musgo, olivo, pino, pita, posidonia, rosa, sargazo, scenedesmus, 
  tomate, trigo
  :: Entidades
adelfas     = U 
aloeVera    = L
boletus     = W 
cedro       = A 
chlorella   = Z
girasol     = Y 
guisante    = S 
helecho     = E 
hepatica    = V
jaramago    = X 
jazmin      = Q
lenteja     = R 
loto        = T 
magnolia    = O 
maiz        = F
margarita   = K 
musgo       = D 
olivo       = C 
pino        = J 
pita        = M 
posidonia   = H 
rosa        = P 
sargazo     = I 
scenedesmus = B
tomate      = N 
trigo       = G 
\end{code}

Una vez que ya tenemos todos los elementos a clasificar definidos, se procede
a la interpretación de los predicados. 

\begin{code}
acuatica, algasVerdes, angiosperma, asterida, briofita, cromista, 
  crucifera, dicotiledonea, gimnosperma, hongo, leguminosa, 
  monoaperturada, monocotiledonea, rosida, terrestre, 
  triaperturada, unicelular
  :: Entidades -> Bool
acuatica        = (`pertenece` [B,H,I,T,Z])
algasVerdes     = (`pertenece` [B,Z])
angiosperma     = (`pertenece` [C,F,G,H,K,L,M,N,O,P,Q,R,S,T,U,X,Y])
asterida        = (`pertenece` [C,K,N,Q,U,Y])
briofita        = (`pertenece` [D,V])
cromista        = (`pertenece` [I])
crucifera       = (`pertenece` [X])
dicotiledonea   = (`pertenece` [C,K,N,O,P,Q,R,S,T,U,X,Y])
gimnosperma     = (`pertenece` [A,J])
hongo           = (`pertenece` [W])
leguminosa      = (`pertenece` [R,S])
monoaperturada  = (`pertenece` [F,G,H,L,M,O])
monocotiledonea = (`pertenece` [F,G,H,L,M])
rosida          = (`pertenece` [P])
terrestre       = 
  (`pertenece` [A,C,D,E,F,G,J,K,L,M,N,O,P,Q,R,S,U,V,W,X,Y])
triaperturada   = (`pertenece` [C,K,N,P,Q,R,S,T,U,X,Y])
unicelular      = (`pertenece` [B,Z])
\end{code}

Por ejemplo, podríamos comprobar si el \texttt{scenedesmus} es gimnosperma

\begin{sesion}
ghci> gimnosperma scenedesmus
False
\end{sesion}

Esto nos puede facilitar establecer una jerarquía en la clasificación,     
por ejemplo \texttt{(espermatófitas)}; es decir, plantas con semillas.

\begin{code}
espermatofitas :: Entidades -> Bool
espermatofitas x = angiosperma x || gimnosperma x
\end{code}

\section{Lógica de predicados en Haskell}

\entrada{LPH}
