(TeX-add-style-hook
 "definiciones"
 (lambda ()
   (TeX-add-symbols
    '("entradaCodigo" 1)
    '("programa" 1)
    '("note" 1)
    '("entrada" 1)
    '("comentario" 1)
    "valor")
   (LaTeX-add-environments
    "enumerate"
    "itemize"))
 :latex)

