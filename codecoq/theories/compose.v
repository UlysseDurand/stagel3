Require Import jeu.
Require Import interactions.


(**
* Définiton du parallèle de deux stratégies
 *)

Inductive parallele_strat `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2 J G) (tau : @strategy2 G H) : (@OOO_int J G H) -> Prop :=
  | bla : forall (u:(@OOO_int J G H)),
      sigma.(S) (restriction_lm_OOO u) -> tau.(S) (restriction_mr_OOO u) ->
        parallele_strat sigma tau u.


Definition parallele_strat `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2 J G) (tau : @strategy2 G H) :
  (@OOO_int J G H) -> Prop :=
  fun s => (
    sigma.(S) (@restriction_lm_OOO J G H s) /\
    tau.(S) (@restriction_mr_OOO J G H s)
).

Lemma parallele_strat_prefixe_stable `{J:Game} `{G:Game} `{H:Game} :
  forall (sigma:@strategy2 J G) (tau:@strategy2 G H) s1 s2,
    prefixOOO s1 s2 ->
    parallele_strat sigma tau s2 ->
      parallele_strat sigma tau s1.
Admitted.



(**
* Définition du témoins
 *)

Fixpoint temoins_O `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2 J G) (tau : @strategy2 G H)
  (s : @O_play2 J H) : (@OOO_int J G H) :=
  match s with
    | nilO2 => nilOOO
    | consO_l a m n s => OOO_int J G H
                                (*

GROS PROBLEME :
Avec une definition de stratégie sigma en O_play2 -> Prop,
je ne peux accéder au témoins, je ne peux savoir, sachant un O_play2
s, quel est l'unique a+ tel qu'on a sa+ dans sigma.
Or il me le faut pour construire l'unique témoins.

Il faudrait aussi faire l'ensemble d'une stratégie en inductif ???

                                 *)
    |
  end
with temoins_P `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2 J G) (tau : @strategy2 G H)
  (S : @P_play2 J H) : (@OOO_int J G H) :=



Lemma temoinsrespecte_nil `{J:Game} `{G:Game} `{H:Game} :
  forall (sigma:@strategy2 J G) (tau:@strategy2 G H),
    (temoins sigma tau nilO2) = nilOOO.
Admitted.

Lemma temoinsrespecte_pref_stable `{J:Game} `{G:Game} `{H:Game} :
  forall (sigma:@strategy2 J G) (tau:@strategy2 G H),
    (forall s1 s2,
        parallele_strat sigma tau (temoins sigma tau s2) ->
        prefixO2 s1 s2 ->
        parallele_strat sigma tau (temoins sigma tau s1)
    )
.
Admitted.



(**
* Définition de la composition de deux stratégies
 *)

Program Definition compose `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2 J G) (tau : @strategy2 G H) :
  (@strategy2 J H) :=
  @Build_strategy2
    J
    H
    ( fun (s:@O_play2 J H) =>
        parallele_strat sigma tau (temoins sigma tau s)
    )
    _ _ _.

Next Obligation.
  rewrite (@temoinsrespecte_nil J G H sigma tau).
  split ; [apply sigma.(S_nonempty)|apply tau.(S_nonempty)].
Qed.

Next Obligation.
  intros s1 s2 s2dedans s1prefs2.
  apply (temoinsrespecte_pref_stable sigma tau s1 s2); assumption.
Qed.

Next Obligation.
