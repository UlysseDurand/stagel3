# Stage de L3

Avec Pierre Clairambault et Etienne Miquey entre le LIS et l'I2M.

# Compilation du projet

Pour compiler le projet, il faut aller dans **codecoq** et executer `make`.

# Contenu

Pour un contenu bien plus détaillé des fichiers coq, une fois le fichier 
compilé, il faut se référer à **codecoq/html/toc.html**

Sinon voici la structure dans les grandes lignes du dépot git :

```
+./
+codecoq/       #Contient le code coq et sa doc une fois compilé
   +theories/   #Fichiers contenant les définition et preuves
   +tests/      #Fichiers test avec des exemples concrets
   +Makefile    #Fichier qui permet de compiler le projet
   +html/       #Si compilé, contient la doc du code coq
      +toc.html #Le sommaire de la doc
 
+presentation/  #Contient les diapos pour la soutenance de stage
   +doc.mdx     #Contenu des diapos à compiler
   +doc.pdf     #Les diapos

+rapport/       #Contient le rapport de stage
   +doc.mdx     #Contenu du rapport à compiler
   +doc.pdf     #Le rapport

+Games.v
+Games_ind.v
                #Fichiers initiant le projet, fais par Etienne Miquey

```

## Dossier codecoq

Ici se trouve le code coq du stage.
Il se divise en plusieurs fichiers :

- theories/utiles.v : Ce fichier contient des définitions et théorèmes utiles

- theories/jeu.v : Ce fichier contient toutes les définitions pour 
définir les jeux
  
- theories/residu.v : Ce fichier contient ce qu'il faut pour définir
un résidu
  
- theories/strategy.v : Ce fichier contient ce qu'il faut pour définir
les stratégies
  
- theories/interactions.v : Ce fichier contient ce qui concerne les 
interactions et le diagramme de polarité

- theories/sanitycheck.v : Ce fichier contient les preuves qui justifient
que les définitions utilisées correspondent bien aux définitions formelles.
  
- tests/test.v : Ce fichier permet de tester les définitions et théorèmes
précédents sur un jeu test concret.
  
## Dossier rapport


## Dossier presentation

Aucune consigne pour le moment
