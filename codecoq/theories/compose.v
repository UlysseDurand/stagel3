Require Import jeu.
Require Import jeuthese.
Require Import interactions.
Require Import strategy.
Require Import residu.
Require Import Coq.Program.Equality.
Require Import residustrat.



(**
On va composer des stratégies, on peut soit composer
- Une stratégie O avec une stratégie O (on obtient une stratégie O)
- Une stratégie O avec une stratégie P (on obtient une stratégie P)
- Une stratégie P avec une stratégie O (on obtient une stratégie P)
 *)

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



(**
Prouvons que la propriété d'être dans sigma parallele tau
est stable par préfixeOOO.
 *)
Check OOO_induc.

Lemma prefixe_donc_paralleleOO `{J:Game} `{G:Game} `{H:Game} :
    forall (u:@OOO_int J G H) (v:@OOO_int J G H)
      (sigma:@strategy2O J G) (tau:@strategy2O G H),
    (parallele_stratOO sigma tau) u ->
    prefixOOO v u ->
      (parallele_stratOO sigma tau) v.
Proof.
  apply (OOO_induc
    (fun J0 G0 H0 u =>
      forall (v:@OOO_int J0 G0 H0)
        (sigma:@strategy2O J0 G0) (tau: @strategy2O G0 H0),
        (parallele_stratOO sigma tau) u ->
        prefixOOO v u ->
          (parallele_stratOO sigma tau) v
    )
    (fun J0 G0 H0 u =>
      forall (v:@OPP_int J0 G0 H0)
        (sigma:@strategy2O J0 G0) (tau: @strategy2P G0 H0),
        (parallele_stratOP sigma tau) u ->
        prefixOPP v u ->
          (parallele_stratOP sigma tau) v
    )
    (fun J0 G0 H0 u =>
      forall (v:@POP_int J0 G0 H0)
        (sigma:@strategy2P J0 G0) (tau: @strategy2O G0 H0),
        (parallele_stratPO sigma tau) u ->
        prefixPOP v u ->
          (parallele_stratPO sigma tau) v
    )
  ).

  - intros J0 G0 H0 v sigma tau nilparall vprefnil.
    induction v; [assumption| inversion vprefnil|inversion vprefnil].
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    destruct v.
    * dependent destruction consas_parall.
      exact (
        respecte_stratsOO sigma tau nilOOO
          (
            sigma.(SO_closed)
            nilO2
            (restriction_lm_OOO (consOOO_C a m n s))
            s0
            (nil_prefO2 (restriction_lm_OOO (consOOO_C a m n s)))
          )
          (
            tau.(SO_closed)
            nilO2
            (restriction_mr_OOO (consOOO_C a m n s))
            s1
            (nil_prefO2 (restriction_mr_OOO (consOOO_C a m n s)))
          )
      ).
    * dependent destruction vprefconsas.

      assert (m0=m) as H2. admit. assert (n0=n) as H3. admit. rewrite H2. rewrite H3. destruct H2. destruct H3.

      dependent destruction consas_parall.
      destruct (
        (HI o sigma (residu_stratP_r a m0 n0 tau))
        (respecte_stratsOP sigma (residu_stratP_r a m0 n0 tau) s s0 s1)
        H1
      ) as (s2,s3).
      exact ((respecte_stratsOO sigma tau (consOOO_C a m0 n0 o)) s2 s3).
    * inversion vprefconsas.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    destruct v.
    * dependent destruction consas_parall.
      exact (
        respecte_stratsOO sigma tau nilOOO
          (
            sigma.(SO_closed)
            nilO2
            (restriction_lm_OOO (consOOO_A a m n s))
            s0
            (nil_prefO2 (restriction_lm_OOO (consOOO_A a m n s)))
          )
          (
            tau.(SO_closed)
            nilO2
            (restriction_mr_OOO (consOOO_A a m n s))
            s1
            (nil_prefO2 (restriction_mr_OOO (consOOO_A a m n s)))
          )
      ).
    * inversion vprefconsas.
    * dependent destruction vprefconsas.

      assert (m0=m) as H2. admit. assert (p=n) as H3. admit. rewrite H2. rewrite H3. destruct H2. destruct H3.

      dependent destruction consas_parall.
      destruct(
        HI p0 (residu_stratP_l a m0 p sigma) tau
        (respecte_stratsPO (residu_stratP_l a m0 p sigma) tau s s0 s1)
        H1
      ) as (s2,s3).
      exact ((respecte_stratsOO sigma tau (consOOO_A a m0 p p0)) s2 s3).
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    destruct v.
    * dependent destruction vprefconsas.

      assert (m0=m) as H2. admit. assert (p=n) as H3. admit. rewrite H2. rewrite H3. destruct H2. destruct H3.

      dependent destruction consas_parall.
      destruct (
        HI o sigma (residu_stratO_r a m0 p tau)
        (respecte_stratsOO sigma (residu_stratO_r a m0 p tau) s s0 s1)
        H1
      ) as (s2,s3).
      exact ((respecte_stratsOP sigma tau (consOPP_C a m0 p o)) s2 s3).
    * inversion vprefconsas.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    destruct v.
    * inversion vprefconsas.
    * dependent destruction vprefconsas.

      assert (m0=m) as H2. admit. assert (n0=n) as H3. admit. rewrite H2. rewrite H3. destruct H2. destruct H3.
      dependent destruction consas_parall.
      destruct (
        (HI p (residu_stratP_r a m0 n0 sigma) (residu_stratO_l a m0 n0 tau))
        (respecte_stratsPO (residu_stratP_r a m0 n0 sigma) (residu_stratO_l a m0 n0 tau) s s0 s1)
        H1
      ) as (s2,s3).
      exact ((respecte_stratsOP sigma tau (consOPP_B a m0 n0 p)) s2 s3).
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    destruct v.
    * dependent destruction vprefconsas.

      assert (m0=m) as H2. admit. assert (p=n) as H3. admit. rewrite H2. rewrite H3. destruct H2. destruct H3.
      dependent destruction consas_parall.
      destruct (
        (HI o (residu_stratO_r a m0 p sigma) (residu_stratP_l a m0 p tau))
        (respecte_stratsOP (residu_stratO_r a m0 p sigma) (residu_stratP_l a m0 p tau) s s0 s1)
        H1
      ) as (s2,s3).
      exact ((respecte_stratsPO sigma tau (consPOP_B a m0 p o)) s2 s3).
    * inversion vprefconsas.
  - intros J0 G0 H0 a m n s HI v sigma tau.
    intros consas_parall vprefconsas.
    destruct v.
    * inversion vprefconsas.
    * dependent destruction vprefconsas.

      assert (m0=m) as H2. admit. assert (n0=n) as H3. admit. rewrite H2. rewrite H3. destruct H2. destruct H3.
      dependent destruction consas_parall.
      destruct (
        (HI o (residu_stratO_l a m0 n0 sigma) tau)
        (respecte_stratsOO (residu_stratO_l a m0 n0 sigma) tau s s0 s1)
        H1
      ) as (s2,s3).
      exact ((respecte_stratsPO sigma tau (consPOP_A a m0 n0 o)) s2 s3).
Admitted.

Lemma yeux_fermes `{J:Game} `{G:Game} `{H:Game} :
  forall (sigma : @strategy2O J G) (tau : @strategy2O G H),
    prefixO2_closed (partiecomposeOO sigma tau).
Proof.
  intros sigma tau s s' paralls' spres'.
  Check (prefixO2_induc
    (fun J0 H0 o o' prefoo' =>
      forall (G0:Game) (sigma0:@strategy2O J0 G0) (tau0:@strategy2O G0 H0),
      (partiecomposeOO sigma0 tau0 o') -> (partiecomposeOO sigma0 tau0 o)
    )
    (fun J0 H0 p p' prefpp' =>
      forall (G0:Game) (sigma0:@strategy2O J0 G0) (tau0:@strategy2O G0 G0),
      (partiecompose)
    )
        ).

Lemma compose_prefix_closed `{J:Game} `{G:Game} `{H:Game} :
      forall (sigma : @strategy2O J G) (tau : @strategy2O G H) s1 (u:@OOO_int J G H),
      prefixO2 s1 (restriction_lr_OOO u) -> exists v, ((restriction_lr_OOO v) = s1) /\ (prefixOOO v u).
Proof.
  intros sigma tau s1 u prefs1urestr.
  Check prefixO2_induc.
  apply (prefixO2_induc
    (fun J0 G0 H0 o o' prefoo'  =>
      forall (sigma:@strategy2O J0 G0) (tau:@strategy2O G0 H0),
        exists (v:@OOO_int, restriction_lr_OOO v = o /\ prefixOOO v o')
      forall (v:@OOO_int J0 G0 H0)
        (sigma:@strategy2O J0 G0) (tau: @strategy2O G0 H0),
        (parallele_stratOO sigma tau) u ->
        prefixOOO v u ->
          (parallele_stratOO sigma tau) v
    )
  ).
Admitted.

Lemma prefix_closedOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
    forall s1 s2, (partiecomposeOO sigma tau) s2 -> prefixO2 s1 s2 ->
      (partiecomposeOO sigma tau) s1.
Proof.
  intros s1 s2 (u,u_parall) s1prefs2.
  assert (exists v : OOO_int, restriction_lr_OOO v = s1 /\ prefixOOO v u).
  apply (@compose_prefix_closed J G H sigma tau s1 u); apply s1prefs2.
  destruct H0 as (v,(restrvs1,prefvu)).
  rewrite <- restrvs1.
  exact (restr_temoinsOO sigma tau v (prefixe_donc_paralleleOO u v sigma tau u_parall prefvu)).
Qed.

Program Definition composeOO `{J:Game} `{G:Game} `{H:Game}
  (sigma : @strategy2O J G) (tau : @strategy2O G H) :
  (@strategy2O J H) :=
  @Build_strategy2O
    J
    H
    (partiecomposeOO sigma tau)
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
