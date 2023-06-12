Require Import utiles.
Require Import jeu.

(**
* Définition des jeux résiduels
 *)


Definition minGame :
  forall (G:Game) (a:@A (@ES G)), Prop:=
  fun G a => forall a',  ord a' a -> a' = a.

Definition polGame :
  forall (G:Game) (a:@A (@ES G)), A -> player :=
  fun G a => (fun x => polarity x).

Definition resEvent :
  forall (G:Game) (a:@A (@ES G)), A->Prop :=
fun G a =>  (fun b => G.(ES).(B) b /\ not (b = a) /\ not (conflict b a)).

Definition resPolarity :
  forall (G:Game) (a:@A (@ES G)), G.(ES).(A)->player :=
  fun G a => polarity.

Program Definition resES :
  forall (G:Game) (a:@A (@ES G)), EventStructure:=
  fun G a =>
    @Build_EventStructure
      A
      (@resEvent G a)
      ord
      conflict
      _
      _
      _
      _
      _.

Next Obligation.
  split.
    intro. intro.
    apply ord_ordonned. destruct H. apply H.
  split.
    intro. intros.
    apply ord_ordonned. destruct H. apply H.
    destruct H0. apply H0.
    apply H1.
    apply H2.

    intro. intros.
    destruct H. destruct H0. destruct H1.
    pose proof G.(ES).(ord_ordonned).
    destruct H7. destruct H8. apply (H9 e f g).
    apply H. apply H0. apply H1. apply H2. apply H3.
Qed.

Next Obligation.
  intro.
  pose proof G.(ES).(confl_irrefl).
  apply (H1 e).
  destruct H. apply H. apply H0.
Qed.

Next Obligation.
  apply G.(ES).(confl_sym).
  destruct H. apply H.
  destruct H0. apply H0.
Qed.


Next Obligation.
  pose proof G.(ES).(finiteness).
  specialize (H0 a0).
  destruct H. destruct H0. apply H.
  exists x.
  destruct H0.
  split.
    apply (inject_restr_implic A x
                  (fun a':A => B a' /\ ord a' a0)
                  (fun a':A => resEvent G a a' /\ ord a' a0)
          ).
    intro.
    intro.
    destruct H3.
    split.
    destruct H3. apply H3.
    apply H4.
    apply H0.

    apply (
        borned_restr_implic A x
                  (fun a':A => B a' /\ ord a' a0)
                  (fun a':A => resEvent G a a' /\ ord a' a0)
          ).
   intro.
   intro.
   destruct H3.
   destruct H3.
   split.
    apply H3. apply H4.
   apply H2.
Qed.

Next Obligation.
  pose proof G.(ES).(vendetta).
  destruct H. destruct H0. destruct H1.
  apply (H4 e1 e2 e2').
    apply H. apply H0. apply H1.
    apply H2.
    apply H3.
Qed.

Definition residual :
  forall (G:Game) (a:@A (@ES G)), Game
  := fun G a=> @Build_Game (resES G a) (@resPolarity G a).
