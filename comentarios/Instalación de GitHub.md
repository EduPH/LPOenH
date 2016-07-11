Buenas tardes Eduardo

Los pasos para crear la clave en GitHub son

~~~
* Generar una nueva clave SSH
     ssh-keygen -t rsa -b 4096 -C <tuCorreo>
  con contraseña ???

* Añadir la clave a ssh-agent
     eval "$(ssh-agent -s)"
     ssh-add ~/.ssh/id_rsa

* Añadir la clave SSH a GitHub: entrar en la cuenta de GitHub y elegir
     Configuración -> Llaves públicas SSH -> Agregar otra llave pública
  y añadir el contenido de ~/.ssh/id_rsa.pub

* Comprobar la conexión SSH con GitHub
     ssh -T git@github.com

* Introducir el nombre y correo
     git config --global user.name "Eduardo"
     git config --global user.email "<tuCorreo>"

* Buscar el API: entrar en la cuenta de GitHub y elegir
     Personal acess tokens -> Generate new token

* Introducir el API anterior
     git config --global github.user EduPH
     git config --global github.token ....
~~~

Para más detalles lee en GitHub
[Generating an SSH key](https://help.github.com/articles/generating-an-ssh-key/)

Saludos, José A.
