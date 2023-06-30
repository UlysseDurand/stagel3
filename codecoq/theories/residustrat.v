Require Import jeu.
Require Import residu.
Require Import strategy.
Require Import jeuthese.
Require Import interactions.


(**
Ici le but est de définir la stratégie résiduelle d'une stratégie.
 *)

Inductive ens_strat_res `{J:Game} `{G:Game}
  (sigma : @strategy2O J G) (c:J.(ES).(A)) : P_play2 -> Prop :=
  | strat_res : forall a m n s,
    sigma.(SO) (@consO_l J G a m n s) ->
      ens_strat_res sigma s.
