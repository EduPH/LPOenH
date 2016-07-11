Buenos días Eduardo

He eliminado los ficheros de control de versiones (.git y .gitignore) por
problemas de sincronización en Dropbox. 

Si deseas seguir usándolo sin sincronizarlo con Dropbox tienes que

+ abrir una shell en emacs con `Esc-x shell` 
+ En la shell, ejecutar

~~~
      cd ~/Dropbox/TFG_Eduardo
      dropbox exclude add .git
      dropbox exclude add .gitignore
~~~

+ Crear en el directorio `~/Dropbox/TFG_Eduardo` el fichero `.gitignore` y
  copiar el contenido del fichero que te adjunto.

+ Iniciar el control de versiones con `Esc-x magit-status`

Saludos, José A.
