Buenos días Eduardo

Comentarios del fichero `Logica_de_predicados_en_Haskell.tex` 

+ He cambiado "Si \texttt{F} y \texttt{G} son fórmulas, entonces $(\texttt{F}
  \wedge \texttt{G})$, $(\texttt{F} \vee \texttt{G})$, $(\texttt{F} \rightarrow
  \texttt{G})$, $\neg F$ y $(F\leftrightarrow G)$ son fórmulas" por "Si $F$ y
  $G$ son fórmulas, entonces $F \wedge G)$, $F \vee G)$, $F \rightarrow G)$,
  $\neg F$ y $(F \leftrightarrow G)$ son fórmulas."
  
+ Conviene dejar una línea en blanco antes y después de las definiciones.  

En `LPH.lhs` 

+ He cambiado `Estructura` por `T` como constructor de términos compuestos.

+ En lugar de `[Char]` se escribe `String` 

+ Se simplifica 
    + `and (map (val u i f s) fs)` por `all (val u i f s) fs`
    + `or (map (val u i f s) fs)` por `any (val u i f s) fs`
    + `concat . map varEnTerm` por `concatMap varEnTerm`
    + `concat (map (varEnForm) forms)` por `concatMap varEnForm forms`
    + `concat (map (variablesLibres) forms)` por `concatMap variablesLibres forms`
      
Saludos, José A.      
