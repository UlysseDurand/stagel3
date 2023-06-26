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
      _ _ _ _ _.

Next Obligation.
  destruct G.(ES).(ord_ordonned) as (Refl, (Sym, Trans)).
  repeat split.
  - intros e eEv; apply Refl; apply eEv.
  - intros e f eEv fEv Ord_e_f; apply Sym;
      [apply eEv | apply fEv | apply Ord_e_f].
  - intros e f g eEv fEv gEV Ord_e_f Ord_f_g; apply Trans with f;
    [apply eEv | apply fEv | apply gEV | apply Ord_e_f | apply Ord_f_g].
Qed.

Next Obligation.
  apply (G.(ES).(confl_irrefl) e); apply H.
Qed.

Next Obligation.
  apply G.(ES).(confl_sym); [apply H | apply H0].
Qed.

Next Obligation.
  destruct H as (a0dedans, (a0diffa, a0noconflita)).
  destruct (G.(ES).(finiteness) a0) as (f,(f_inj, f_bound)); [ assumption| ].
  exists f. split.
  - apply (inject_restr_implic A f
                  (fun a':A => B a' /\ ord a' a0)
                  (fun a':A => resEvent G a a' /\ ord a' a0)
          ).
    intros a1 (dedansa1, a1leqa0); split;[apply dedansa1 | apply a1leqa0].
    exact f_inj.
  -
    apply (
        borned_restr_implic A f
                  (fun a':A => B a' /\ ord a' a0)
                  (fun a':A => resEvent G a a' /\ ord a' a0)
          ).
    intros a1 (dedansa1, a1leqa0); split;[apply dedansa1|apply a1leqa0].
    exact f_bound.
Qed.

Next Obligation.
  apply G.(ES).(vendetta) with e2;
  [apply H | apply H0 | apply H1 | apply H2 | apply H3].
Qed.

Definition residual :
  forall (G:Game) (a:@A (@ES G)), Game
  := fun G a=> @Build_Game (resES G a) (@resPolarity G a).
