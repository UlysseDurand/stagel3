Require Import jeu.
Require Import interactions.


(**
* Définiton du parallèle de deux stratégies
 *)

Inductive parallele_stratOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) (u:@OOO_int J G H) :=
  | respecte_stratsOO :
      sigma.(SO) (restriction_lm_OOO u) ->
      tau.(SO) (restriction_mr_OOO u) ->
        parallele_stratOO sigma tau u.

Inductive parallele_stratPO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2P J G) (tau : @strategy2O G H) (u:@POP_int J G H) :=
  | respecte_stratsPO :
      sigma.(SP) (restriction_lm_POP u) ->
      tau.(SO) (restriction_mr_POP u) ->
        parallele_stratPO sigma tau u.

Inductive parallele_stratOP `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2P G H) (u:@OPP_int J G H) :=
  | respecte_stratsOP :
      sigma.(SO) (restriction_lm_OPP u) ->
      tau.(SP) (restriction_mr_OPP u) ->
        parallele_stratOP sigma tau u.

(*
Lemma parallele_strat_prefixe_stable `{J:Game} `{G:Game} `{H:Game} :
  forall (sigma:@strategy2 J G) (tau:@strategy2 G H) s1 s2,
    prefixOOO s1 s2 ->
    parallele_strat sigma tau s2 ->
      parallele_strat sigma tau s1.
Admitted.
*)

(**
* Définition de la composition de deux stratégies
 *)

Inductive partiecomposeOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
  (@O_play2 J H) -> Prop :=
  | restr_temoinsOO :
      forall (u:@OOO_int J G H),
      parallele_stratOO sigma tau u ->
        partiecomposeOO sigma tau (restriction_lr_OOO u).

Inductive partiecomposePO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2P J G) (tau : @strategy2O G H) :
  (@P_play2 J H) -> Prop :=
  | restr_temoinsPO :
      forall (u:@POP_int J G H),
      parallele_stratPO sigma tau u ->
        partiecomposePO sigma tau (restriction_lr_POP u).

Inductive partiecomposeOP `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2P G H) :
  (@P_play2 J H) -> Prop :=
  | restr_temoinsOP :
      forall (u:@OPP_int J G H),
      parallele_stratOP sigma tau u ->
        partiecomposeOP sigma tau (restriction_lr_OPP u).


Lemma composeOO_nonempty `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) : partiecomposeOO sigma tau nilO2.
Proof.
  exact (
      (restr_temoinsOO sigma tau nilOOO)
      (respecte_stratsOO sigma tau
         nilOOO
         (sigma.(SO_nonempty))
         (tau.(SO_nonempty))
      )
    ).
Qed.

Lemma prefix_donc_parallele `{J:Game} `{G:Game} `{H:Game}:
    (
      forall (sigma : @strategy2O J G) (tau :  @strategy2O G H) (u v:@OOO_int J G H),
      (parallele_stratOO sigma tau) u -> prefixOOO v u -> (parallele_stratOO sigma tau) v
    ) /\
    (

      forall (sigma : @strategy2O J G) (tau :  @strategy2P G H) (u v:@OPP_int J G H),
      (parallele_stratOP sigma tau) u -> prefixOPP v u -> (parallele_stratOP sigma tau) v
    ) /\
    (

      forall (sigma : @strategy2P J G) (tau :  @strategy2O G H) (u v:@POP_int J G H),
      (parallele_stratPO sigma tau) u -> prefixPOP v u -> (parallele_stratPO sigma tau) v
    ).

Proof.

Lemma compose_prefix_closed `{J:Game} `{G:Game} `{H:Game} :
      forall (sigma : @strategy2O J G) (tau : @strategy2O G H) s1 (u:@OOO_int J G H),
      prefixO2 s1 (restriction_lr_OOO u) -> exists v, ((restriction_lr_OOO v) = s1) /\ (prefixOOO v u).
  Admitted.

Lemma prefix_closedOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
    forall s1 s2, (partiecomposeOO sigma tau) s2 -> prefixO2 s1 s2 ->
      (partiecomposeOO sigma tau) s1.
Proof.
  intros s1 s2 (u,u_parall) s1prefs2.
  pose proof (@compose_prefix_closed J G H sigma tau s1 u).
  assert (exists v : OOO_int, restriction_lr_OOO v = s1 /\ prefixOOO v u).
  apply H0; apply s1prefs2.
  destruct H1 as (v,(restrvs1,prefvu)).
  rewrite <- restrvs1.
  assert (parallele_stratOO sigma tau v).
  admit.
  exact (restr_temoinsOO sigma tau v H1).


Program Definition composeOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
  (@strategy2O J H) :=
  @Build_strategy2O
    J
    H
    (partiecomposeOO sigma tau)
    (composeOO_nonempty sigma tau)
    (prefix_closedOO sigma tau)
    _.


Next Obligation.
  intros s1 s2 (u,u_parall) s1prefs2.
  assert (exists (v : OOO_int), parallele_strat sigma tau v /\ s1 = restriction_lr_OOO v ).
  -


    admit.
  - destruct H0 as (v, (v_parall,v_restr_eq_s1)).
    rewrite v_restr_eq_s1.
    exact (restr_temoins sigma tau v v_parall).
Admitted.

Next Obligation.
