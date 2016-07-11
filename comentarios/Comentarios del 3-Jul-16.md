Buenos días Eduado

Te comento algunas cuestiones de tu trabajo

En `LPH.lhs` 

+ He quitado la importación de `Data.List`, `Dominio`  y `Modelo`. De momento,
  no se usan.

+ Falta texto matemático que explique la formalización.

+ Se puede definir sustituye sin condicionales ni lambdas

~~~
      sustituye s x d v | x == v     = d 
                        | otherwise = s v
~~~

+ He cambiado `evalua` por `valor`  y `universo` por `u`.

+ He definido los tipos `Universo a`, `Interpretacion` y `Asignacion` con los
  que el tipo de `valor` es

~~~
      valor :: Eq a => 
               Universo a -> Interpretacion a -> Asignacion a -> Formula -> Bool
~~~

+ La definición de valor de la implicación se puede simplificar a

~~~
      valor u i s (Implica f1 f2) = 
        valor u i s f1 <= valor u i s f2)
~~~

+ Es mejor usar las primitivas. Por ejemplo, he cambiado `aplicafun` por `map`,
  `conjuncion` por `and` y `disyuncion` por `or`. 
  
+ Se pueden simplificar 
    + `concat [ show vs ]` por `show vs`. 
    + `and (map (valor u i s) fs)` por `all (valor u i s) fs`
    + `or (map (valor u i s) fs)` por `any (valor u i s) fs`


Saludos. José A.

P.D. Estos comentarios están en el Dropbox en la carpeta `comentarios`
