# Stage de L3

Avec Pierre Clairambault et Etienne Miquey entre le LIS et l'I2M.


# Contenu

## Dossier codecoq

Ici se trouve le code coq du stage.
Il se divise en plusieurs fichiers :

- theories/utiles.v : Ce fichier contient des définitions et théorèmes utiles par exemple pour définir
  - les ensembles finis
  - les relations d'ordre
  - les fonctions bornées
  - les fonctions injectives 

- theories/jeu.v : Ce fichier contient toutes les définitions pour définir les jeux, c'est à dire
  - les structures d'événements
  - les configurations
  - les justifications
  - les jeux.
  
- theories/residu.v : Ce fichier contient ce qu'il faut pour définir un résidu, c'est à dire
  - la définition d'un jeu résiduel
  - la preuve qu'un jeu résiduel est un jeu
  
- theories/strategy.v : Ce fichier contient ce qu'il faut pour définir les stratégies, c'est à dire
  - les OPlay
  - les préfixes de parties
  - la relation de cohérence
  - les stratégies
  
- theories/diagpol.v : Ce fichier contient ce qui concerne les interpretations et le diagramme de polarité, c'est à dire
  - les OOO_Play
  - les préfixes sur les interprétations
  - les restrictions d'interprétation
  
- tests/test.v : Ce fichier permet de tester les définitions et théorèmes précédents sur un jeu test concret.
  
## Dossier rapport

Dans le dossier rapport, il y a tout le contenu du rapport qui a les contraintes suivantes :

Le rapport est la première base d'évaluation de votre travail. Il doit exposer le problème étudié et son contexte (avec une étude bibliographique), et bien sûr présenter votre travail, en étant clair et précis sur vos contributions personnelles.

Le rapport doit compter 12 à 20 pages, figures et bibliographie comprises, hors annexes. Je vous invite à utiliser un template et une taille de police standard (e.g., article, 10pt) et à utiliser votre bon sens pour juger de l'acceptabilité de la forme (12 pages de figures sans texte ne sont par exemple pas acceptables).
Votre rapport peut contenir des annexes en supplément, mais le jury n'est pas tenu de les lire et votre rapport doit être compréhensible sans.


Le rapport peut être rédigé indifféremment en français ou en anglais.
Le rapport doit avoir une page de garde, faisant apparaître le titre du stage, votre nom, celui de votre encadrant(e), le nom du laboratoire/établissement d'accueil.
Le rapport doit contenir une introduction qui présente le sujet du stage, le domaine dont il est issu et la motivation de l'étude de ce sujet, ainsi que le plan de votre rapport. Voici quelques questions qui peuvent vous guider :
- D'où vient le problème ?
- Pourquoi le problème est-il intéressant/pertinent/important ?
- Quel était l'état de l'art au début de votre stage ?

Organisez le corps du rapport avec un certain nombre de sections (introduction, préliminaires, résultats), en sélectionnant bien ce que vous présentez (en particulier si vous avez beaucoup de résultats, faites un tri). Expliquez votre démarche dès que possible et soyez honnête sur vos contributions personnelles en les distinguant bien des travaux préexistants. Voici quelques conseils supplémentaires suivant la nature du travail rencontré :
Parties théoriques : définissez bien les notions utilisées, ajustez la longueur de vos démonstrations (complètes ou ébauche avec la version complète en annexe), illustrez si besoin avec des exemples.
Parties expérimentales : spécifiez bien le protocole expérimental (les expériences doivent être reproductibles), utilisez tableaux, graphiques, statistiques pour décrire et discuter vos résultats, vos données peuvent être mises à disposition sur une annexe en ligne.
Parties programmation : précisez la part d'implémentations nouvelles et la part de réutilisation de codes déjà existants, expliquez vos choix, vos codes sources peuvent être mis à disposition sur une annexe en ligne.
Stage purement bibliographique : de tels stages sont acceptables en L3 si l'envergure du travail bibliographique est suffisante, dans ce cas précisez-le bien dans l'introduction, de tels stages servent souvent à s'approprier des sujets difficiles, les conseils précédents s'appliquent, gardez un oeil critique pour pouvoir proposer des simplifications, améliorations, perspectives.

Le rapport peut également contenir des liens vers des annexes en ligne (adresses web personnelles ou institutionnelles, arXiv, GitHub, ...) pour stocker des démonstrations longues, des codes sources, des données, des publications issues de votre travail (rien d'obligatoire là-dessus en 6 semaines), ...

Toutes ces contraintes sont classiques dans le processus d'évaluation des travaux scientifiques. Les meilleures conférences suivent des contraintes très similaires quant aux règles de soumission et d'écriture, avec une date limite d'envoi stricte, un nombre de pages borné et des recommandations précises d'organisation du travail. Je vous assure que vous pouvez produire un rapport d'excellente qualité en respectant toutes ces contraintes. Par ailleurs, le jury aura connaissance de tous les rapports et de tout retard. Il serait très mal vu de déroger aux règles ci-dessus. Pour information, contrevenir à n'importe laquelle de ces contraintes dans le cadre des meilleures conférences résulte automatiquement au rejet du travail.

Consignes obligatoires supplémentaires pour le rapport :

- Le rapport doit être accessible pour une personne non experte du domaine. Il peut contenir si besoin des discussions sur des pistes explorées mais ayant échouées. Cela le distingue d'un article de recherche qui souvent s'adresse à des personnes expertes et ne s'encombre pas des tentatives infructueuses.
- Le rapport doit contenir une conclusion, où vous pourrez résumer votre travail et vos résultats, suggérer des perspectives, comparer ce qui a été obtenu avec les objectifs initiaux, dire un mot des difficultés rencontrées et des parties chronophages.
- Le rapport doit contenir une bibliographie, chaque référence présente dans cette bibliographie doit être citée au moins une fois quelque part (pas de références fantômes) et doit avoir été consultée par vous (au moins en partie).
- Le rapport doit contenir une petite annexe (une demi-page maximum) décrivant le contexte institutionnel et social de votre stage (le laboratoire, sa taille, l'équipe, les personnes et groupes avec lesquels vous avez interagi). Vous pouvez aussi inclure quelques impressions sur les métiers de la recherche.
- Votre rapport doit avoir été relu et validé par votre encadrant(e) (voir la Charte des stages).
- Votre rapport doit être rendu dans les temps. Aucun délai ne sera accordé. 

## Dossier presentation

Aucune consigne pour le moment
