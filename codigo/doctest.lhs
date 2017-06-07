\begin{code}
-- | Ejemplos
-- >>> let c = Cs [C [Neg p,p],C [Neg p,Neg r]]
-- >>> atomosCs c
-- [p,r]
-- >>> interPosibles c
-- [[(p,0),(r,0)],[(p,0),(r,1)],[(p,1),(r,0)],[(p,1),(r,1)]]
-- >>> esConsistente c
-- True
-- >>> let c' = Cs [C [p],C [Neg p,q],C [Neg q]]
-- >>> c'
-- {{p},{¬p,q},{¬q}}
-- >>> esConsistente c'
-- False
\end{code}

Finalmente, se abre la carpeta en la que está el archivo en un terminal y se invoca el paquete mediante \fbox{\texttt{doctest RES.lhs}} y, en caso de que todos los ejemplos sean correctos, devolverá:

\texttt{
> doctest RES.lhs \\
Examples: 163  Tried: 163  Errors: 0  Failures: 0}

En el caso de que hubiera un error devuelve dónde lo ha encontrado, así como lo que él esperaba encontrar.
