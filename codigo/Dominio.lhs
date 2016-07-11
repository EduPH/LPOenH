\begin{code}
module Dominio where

data Entidades = A | B | C | D | E | F | G
               | H | I | J | K | L | M | N
               | O | P | Q | R | S | T | U
               | V | W | X | Y | Z | Inespecifico
     deriving (Eq, Bounded, Enum)
\end{code}

Se añade \texttt{deriving (Eq, Bounded, Enum)} para establecer relaciones de
igualdad entre las entidades \texttt{(Eq)}, una acotación \texttt{(Bounded)} y
enumeración de los elementos \texttt{(Enum)}.

Para mostrarlas por pantalla, definimos las entidades en la clase
\texttt{(Show)} de la siguiente forma
\begin{code}
instance Show Entidades where
    show A = "A"; show B = "B"; show C = "C";
    show D = "D"; show E = "E"; show F = "F";
    show G = "G"; show H = "H"; show I = "I";
    show J = "J"; show K = "K"; show L = "L";
    show M = "M"; show N = "N"; show O = "O";
    show P = "P"; show Q = "Q"; show R = "R";
    show S = "S"; show T = "T"; show U = "U";
    show V = "V"; show W = "W"; show X = "X";
    show Y = "Y"; show Z = "Z"; show Inespecifico = "*" 
\end{code}
Colocamos todas las entidades en una lista
\begin{code}
entidades :: [Entidades]
entidades = [minBound..maxBound]
\end{code}
De manera que si lo ejecutamos
\begin{sesion}
ghci> entidades
[A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,*]
\end{sesion}
