
Comencemos un módulo en Haskell, donde escribiremos nuestros ejemplos y construiremos distintas correspondencias entre lógica y programación. 
\begin{code}
module CHC where
import LPH 
\end{code}

La correspondencia de Curry-Howard establece de manera informal la siguientes equivalencias:

\begin{itemize*}
\item Los tipos son teoremas, los programas son demostraciones. 
\item Existe un objeto del tipo $T$ si y sólo si $T$, interpretado como proposición lógica, es cierto. 
\end{itemize*}

Mostremos en una tabla, aunque posteriormente tratemos con ejemplos y más detenimiento, las correspondencias entre elementos concretos. 

  \begin{center}
   \begin{tabular}{| l | l |}
     \hline
     \textbf{Lógica}  &  \textbf{Haskell} \\ \hline
     $\rightarrow $   & \texttt{->} \\ \hline
     Modus ponens        & Aplicación de funciones \\ \hline
     $a\wedge b $     & \texttt{(a,b)} \\ \hline
     $\vee $ & \texttt{Either}\\  \hline
     $T$ & \texttt{()} \\ \hline
     $\neg $ & \texttt{not} \\ \hline
   \end{tabular}
 \end{center}

\comentario{Añadir false a la tabla}


\section{Proposiciones lógicas y tipos de programas}

