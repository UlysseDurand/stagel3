Require Import jeu.
Require Import strategy.
Require Import interactions.
Require Import jeuthese.

Definition isomorphes A B :=
  exists (f:A->B) (f':B->A),
    (forall x:A, f'(f(x)) = x) /\ (forall y:B, f(f'(y)) = y).

Theorem oplay2_coherent : forall (J G:Game),
  isomorphes
    (@O_play (Game_tenseur J G))
    (@O_play2 J G).
Admitted.

Theorem strategy2_coherent : forall (J G:Game),
  isomorphes
    (@strategy (Game_tenseur J G))
    (@strategy2O J G).
Admitted.
