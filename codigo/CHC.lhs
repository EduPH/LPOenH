
Comencemos un módulo en Haskell, donde escribiremos nuestros ejemplos y construiremos distintas correspondencias entre lógica y programación. 
\begin{code}
module CHC where
import LPH 
\end{code}

\section{Proposiciones lógicas y tipos de programas}

Hemos dicho con anterioridad que las proposiciones lógicas 
corresponden a los tipos de datos de programas. Comentemos unos cuantos ejemplos
para tener una visión intuitiva. 

\begin{itemize*}
\item $a \rightarrow a$
\begin{code}
identidad :: a-> a
identidad x = x
\end{code}
\end{itemize*}
