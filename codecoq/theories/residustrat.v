Require Import jeu.
Require Import residu.
Require Import strategy.
Require Import jeuthese.
Require Import interactions.

Require Import Coq.Program.Equality.

(**
Ici le but est de définir la stratégie résiduelle d'une stratégie.
 *)

Definition ens_residu_stratP_l `{J:Game} `{G:Game}
  (a:J.(ES).(A)) (m:minGame J a) (n:pos a) (sigma : @strategy2O J G) :
  (@P_play2 (residual J a) G) -> Prop :=
  fun s => sigma.(SO) (consO_l a m n s).

Definition ens_residu_stratP_r `{J:Game} `{G:Game}
  (a:G.(ES).(A)) (m:minGame G a) (n:neg a) (sigma : @strategy2O J G) :
  (@P_play2 J (residual G a)) -> Prop :=
  fun s => sigma.(SO) (consO_r a m n s).

Definition ens_residu_stratO_l `{J:Game} `{G:Game}
  (a:J.(ES).(A)) (m:minGame J a) (n:neg a) (sigma : @strategy2P J G) :
  (@O_play2 (residual J a) G) -> Prop :=
  fun s => sigma.(SP) (consP_l a m n s).

Definition ens_residu_stratO_r `{J:Game} `{G:Game}
  (a:G.(ES).(A)) (m:minGame G a) (n:pos a) (sigma : @strategy2P J G) :
  (@O_play2 J (residual G a)) -> Prop :=
  fun s => sigma.(SP) (consP_r a m n s).

Program Definition residu_stratP_l `{J:Game} `{G:Game}
  (a:J.(ES).(A)) (m:minGame J a) (n:pos a) (sigma : @strategy2O J G) :
  (@strategy2P (residual J a) G) :=
  @Build_strategy2P (residual J a) G (ens_residu_stratP_l a m n sigma) _ _.

Next Obligation.
  intros s s' s'dedans spres'.
  apply (sigma.(SO_closed) (consO_l a m n s) (consO_l a m n s'));
    [exact s'dedans|exact (cons_prefO2_l a m n s s' spres')].
Qed.

Next Obligation.
  assert (coherentO2 (consO_l a m n s) (consO_l a m n s')).
  apply sigma.(SO_det);[apply H|apply H0].
  dependent destruction H1.
  - cut False. intro. inversion H2. apply H1. reflexivity.
  - apply H1.
Qed.

Program Definition residu_stratP_r `{J:Game} `{G:Game}
  (a:G.(ES).(A)) (m:minGame G a) (n:neg a) (sigma : @strategy2O J G) :
  (@strategy2P J (residual G a)) :=
  @Build_strategy2P J (residual G a) (ens_residu_stratP_r a m n sigma) _ _.

Next Obligation.
  intros s s' s'dedans spres'.
  apply (sigma.(SO_closed) (consO_r a m n s) (consO_r a m n s'));
    [exact s'dedans|exact (cons_prefO2_r a m n s s' spres')].
Qed.

Next Obligation.
  assert (coherentO2 (consO_r a m n s) (consO_r a m n s')).
  apply sigma.(SO_det);[apply H|apply H0].
  dependent destruction H1.
  - cut False. intro. inversion H2. apply H1. reflexivity.
  - apply H1.
Qed.

Program Definition residu_stratO_l `{J:Game} `{G:Game}
  (a:J.(ES).(A)) (m:minGame J a) (n:neg a) (sigma : @strategy2P J G) :
  (@strategy2O (residual J a) G) :=
  @Build_strategy2O (residual J a) G (ens_residu_stratO_l a m n sigma) _ _.

Next Obligation.
  intros s s' s'dedans spres'.
  apply (sigma.(SP_closed) (consP_l a m n s) (consP_l a m n s'));
    [exact s'dedans|exact (cons_prefP2_l a m n s s' spres')].
Qed.

Next Obligation.
  assert (coherentP2 (consP_l a m n s) (consP_l a m n s')).
  apply sigma.(SP_det);[apply H|apply H0].
  dependent destruction H1.
  apply H1.
Qed.

Program Definition residu_stratO_r `{J:Game} `{G:Game}
  (a:G.(ES).(A)) (m:minGame G a) (n:pos a) (sigma : @strategy2P J G) :
  (@strategy2O J (residual G a)) :=
  @Build_strategy2O J (residual G a) (ens_residu_stratO_r a m n sigma) _ _.

Next Obligation.
  intros s s' s'dedans spres'.
  apply (sigma.(SP_closed) (consP_r a m n s) (consP_r a m n s'));
    [exact s'dedans|exact (cons_prefP2_r a m n s s' spres')].
Qed.

Next Obligation.
  assert (coherentP2 (consP_r a m n s) (consP_r a m n s')).
  apply sigma.(SP_det);[apply H|apply H0].
  dependent destruction H1.
  apply H1.
Qed.
