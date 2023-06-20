Require Import utiles.
Require Import Program.

(**
* Définition d'une structure d'événements

Ici et dans toute la suite, B: A->Prop sera identifié à
un sous ensemble de A, sur lequel toutes nos définitions
portent. Ainsi au lieu de marquer forall e:B, on marque
forall e:A, B e -> .
 *)




Class EventStructure := {
    A: Set;
    B: A->Prop;

    ord : A -> A -> Prop;
    conflict : A -> A -> Prop;

    ord_ordonned: ordonned_restr B ord;

    confl_irrefl: forall e, B e->not (conflict e e);
    confl_sym : forall x y, B x->B y-> conflict x y <-> conflict y x;

    (* à causes finies *)
    finiteness: forall a, B a -> ens_fini_restr (fun a' => B a' /\ ord a' a);

    (* axiome de vendetta *)
    vendetta: forall e1 e2 e2', B e1->B e2-> B e2' ->
      conflict e1 e2 -> ord e2 e2' -> conflict e1 e2'


  }.

(**
Pour avoir B = A.
 *)
Definition all `{A: Type} : A->Prop := fun a => True.


(**
* Définition d'une configuration
 *)

Definition ferme_enbas `{A: Type} (B: A-> Prop) (ord: A -> A -> Prop) (P: A->Prop):=
  forall e e', B e -> B e' -> P e -> (ord e' e) -> P e'.
(**
Configuration finie.
 *)

Definition conf_finite (ES: EventStructure) (C: A->Prop) :=
  ens_fini_restr C.
(**
Configuration fermée vers le bas
 *)

Definition conf_closed (ES: EventStructure) (C: A->Prop) :=
  ferme_enbas ES.(B) ES.(ord) C.

(**
Configuration sans conflit
 *)
Definition conf_noconflict (ES: EventStructure) (C: A->Prop) :=
  forall e e', C e -> C e' -> not (conflict e e').

Definition est_conf (ES: EventStructure) (C: A->Prop) :=
  conf_finite ES C /\ conf_closed ES C /\ conf_noconflict ES C.

Class configuration `{ES:EventStructure}:=
  {
    C : A ->  Prop;
    conf_axiomes : est_conf ES C
  }.

(**
* Définition d'une justification
 *)

Definition union_subsets `{A: Type} (B : A->Prop) (B' : A->Prop) := fun x => B x \/ B' x.

Definition subset_singleton `{A: Type} (x: A) := fun a => a = x.

Definition justifies `{ES:EventStructure} (x:configuration) (e:A):=
  not (C e) /\ est_conf ES (union_subsets C (subset_singleton e)).

(**
* Définition d'un jeu
 *)

Inductive player:=
| P: player
| O: player.

Class Game := {
    ES : EventStructure;
    polarity : A -> player
  }.

Definition sumES (J G : Game) :=
  sum J.(ES).(A) G.(ES).(A).

Definition ssEnsSumES (J G : Game) :=
      (fun x => (match x with |inl a => J.(ES).(B) a |inr b => G.(ES).(B) b end)).


Definition ordSumES (J G : Game) :=
      (
        fun x y => (match (x,y) with
                   |(inl a, inl b) => J.(ES).(ord) a b
                   |(inr a, inr b) => G.(ES).(ord) a b
                   | _ => False
                 end
                )
      ).

Definition conflictSumES (J G : Game) :=
      (
        fun x y => (match (x,y) with
                   |(inl a, inl b) => J.(ES).(conflict) a b
                   |(inr a, inr b) => G.(ES).(conflict) a b
                   | _ => False
                 end
                )
      ).




Ltac destord J:= destruct J.(ES).(ord_ordonned) as  (?Refl,(?Antisym,?Trans)).

Ltac myinv :=
  match goal with
  | [ H:ordSumES _ _ (inl _) (inr _) |- _] => inversion H
  | [ H:ordSumES _ _ (inr _) (inl _) |- _] => inversion H
  end.

(**
* Jeu tenseur
 *)
Program Definition ES_tenseur :
  forall (J G :Game), EventStructure:=
  fun J G =>
    @Build_EventStructure
      (sumES J G)
      (ssEnsSumES J G)
      (ordSumES J G)
      (conflictSumES J G)
      _
      _
      _
      _
      _.

Next Obligation.
  repeat split.
  - intros e H.
    destruct e;[destord J|destord G];now apply Refl.
  - intros e f He Hf Ordef Ordfe.
    destruct e;destruct f;intros;try inversion Ordfe;
      f_equal;[destord J |destord G]; now apply Antisym.
  - intros x y z Hx Hy Hz Ordxy Ordyz;
      destord J;destord G.
    destruct x, y, z;try myinv.
    + apply Trans with a0;assumption.
    + apply Trans0 with a0;assumption.
Qed.
Next Obligation.
  induction e.
    intro.
    unfold conflictSumES in H0.
    pose proof J.(ES).(confl_irrefl).
    apply (H1 a).
    unfold ssEnsSumES in H. apply H. apply H0.

    intro.
    unfold conflictSumES in H0.
    pose proof G.(ES).(confl_irrefl).
    apply (H1 b).
    unfold ssEnsSumES in H. apply H. apply H0.
Qed.

Next Obligation.
  induction x.
    induction y.
      unfold conflictSumES.
      apply J.(ES).(confl_sym).
      unfold ssEnsSumES in H. apply H.
      unfold ssEnsSumES in H0. apply H0.

      unfold conflictSumES.
      split. trivial. trivial.

    induction y.
      unfold conflictSumES.
      split. trivial. trivial.

      unfold conflictSumES.
      apply G.(ES).(confl_sym).
      unfold ssEnsSumES in H. apply H.
      unfold ssEnsSumES in H0. apply H0.
Qed.

Definition extension1 (A B : Set) (f : A -> nat) : (sum A B)->nat.
  exact (fun x => match x with |inl(a) => f a |inr(b) => 0 end).
Defined.

Definition extension2 (A B : Set) (f : B -> nat) : (sum A B)->nat.
  exact (fun x => match x with |inl(a) => 0  |inr(b) => f b end).
Defined.

Next Obligation.
  pose proof J.(ES).(finiteness).
  pose proof G.(ES).(finiteness).

  induction a.
    unfold ssEnsSumES in H.
    destruct ((H0 a) H).
    destruct H2.
    exists (extension1 J.(ES).(A) G.(ES).(A) x).

    split.
      intro.
      induction a0.
        intro.
        induction a'.
          intros.
          f_equal.
          apply (H2 a0 a1).
          split.
          split.
          apply H4.
          apply H4.
          apply H4.
          apply H5.

          intros.
          inversion H4.
          inversion H7.
          inversion H9.

        intro.
        induction a'.
          intros.
          inversion H4.
          inversion H6.
          inversion H9.

        intros.
        inversion H4.
        inversion H7.
        inversion H9.

      destruct H3.
      exists x0.
      intro.
      induction a0.
      intros.
      simpl.
      apply (H3 a0).
      split.
        apply H4.
        apply H4.

      intros.
      inversion H4.
      inversion H6.

    unfold ssEnsSumES in H.
    destruct ((H1 b) H).
    destruct H2.
    exists (extension2 J.(ES).(A) G.(ES).(A) x).

    split.
      intro.
      induction a.
        intro.
        induction a'.
          intros.
          inversion H4.
          inversion H6.
          inversion H9.

          intros.
          inversion H4.
          inversion H6.
          inversion H9.

        intro.
        induction a'.
          intros.
          inversion H4.
          inversion H7.
          inversion H9.

          intros.
          f_equal.
          apply (H2 b0 b1).
          split.
          split.
          apply H4.
          apply H4.
          apply H4.
          apply H5.

      destruct H3.
      exists x0.
      intro.
      induction a.
        intros.
        simpl.
        inversion H4.
        inversion H6.

        intros.
        apply (H3 b0).
        split.
          apply H4.
          apply H4.
Qed.

Next Obligation.
