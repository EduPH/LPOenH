\section{Representación de modelos}

El contenido de esta sección se encuentra en el módulo \texttt{Modelo}.

\begin{code}
module Modelo where
import Dominio
import PFH
\end{code}

La lógica de primer orden permite dar una representación al
conocimiento. Nosotros trabajaremos con modelos a través de un dominio de
entidades; en concreto, aquellas del módulo \texttt{Dominio}. Cada entidad de
dicho módulo representa un sujeto. Cada sujeto tendrá distintas propiedades.

En secciones posteriores se definirá un modelo lógico. Aquí empleamos el término modelo
como una modelización o representación de la realidad. 
  
Damos un ejemplo de predicados lógicos para la clasificación botánica. La cual
no es completa, pero nos da una idea de la manera de una representación lógica.

Primero definimos los elementos que pretendemos clasificar, y que cumplirán los
predicados. Con este fin, definimos una función para cada elemento del            
dominio de entidades.

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

Una vez que ya tenemos todos los elementos a clasificar definidos, se procede a
la interpretación de los predicados. Es decir, una clasificación de aquellos
elementos que cumplen un cierto predicado.

\begin{Def}
  Un \textbf{predicado} es una oración narrativa que puede ser verdadera o falsa.
\end{Def}

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

Por ejemplo, podríamos comprobar si el \texttt{scenedesmus} es
\texttt{gimnosperma}

\begin{sesion}
ghci> gimnosperma scenedesmus
False
\end{sesion}

Esto nos puede facilitar establecer una jerarquía en la clasificación,     
por ejemplo \texttt{(espermatofitas)}; es decir, plantas con semillas.

\begin{code}
espermatofitas :: Entidades -> Bool
espermatofitas x = angiosperma x || gimnosperma x
\end{code}

\section{Lógica de primer orden en Haskell}

\entrada{LPH}
