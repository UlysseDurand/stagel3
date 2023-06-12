Require Import utiles.
Require Import main.
Require Import jeu.
Require Import residu.

Inductive MBool := q | tt| ff.

Check @Build_EventStructure.

Definition estmin `{A: Type} (ord: A->A->Prop) (x:A) :=
  forall y, ord y x -> y = x.

Definition BoolOrd x y := x=y \/ (x=q /\ (y = tt \/ y = ff)).

Theorem ordonned_bool : ordonned_restr (fun x => True) BoolOrd.
  Admitted.

Definition BoolConflict x y := (x = tt /\ y = ff) \/ (x = ff /\ y = tt).

Theorem irreflexive_boolconflict : forall e, not (BoolConflict e e).
  Admitted.
Theorem symmetric_boolconflict : forall x y, BoolConflict x y <-> BoolConflict y x.
  Admitted.

Program Definition es_bool :=
  @Build_EventStructure MBool (fun x=>True) BoolOrd BoolConflict _ _ _ _ _.

Next Obligation.
  apply ordonned_bool.
Qed.
Next Obligation.
  apply irreflexive_boolconflict.
Qed.
Next Obligation.
  apply symmetric_boolconflict.
Qed.
Next Obligation.
  Definition f := fun (x: MBool) => match x with |q => 0 |tt => 1 | ff => 2 end.
  exists f.
  split.
    admit.
    exists 3. induction a0.
      auto.
      auto.
      auto.
Admitted.
Next Obligation.
Admitted.

Definition JeuBool :=
  @Build_Game es_bool (fun x => match x with |q => O |tt => P | ff => P end).
