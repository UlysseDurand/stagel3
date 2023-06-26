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

(**
* Définition d'un jeu tenseur
 *)

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
  | [ H:conflictSumES _ _ (inl _) (inr _) |- _] => inversion H
  | [ H:conflictSumES _ _ (inr _) (inl _) |- _] => inversion H
  end.

Ltac mysplit :=
  match goal with
  | [ H: _ /\ _ |- _] => destruct H
  end.

Program Definition ES_tenseur :
  forall (J G :Game), EventStructure:=
  fun J G =>
    @Build_EventStructure
      (sumES J G)
      (ssEnsSumES J G)
      (ordSumES J G)
      (conflictSumES J G)
      _ _ _ _ _.

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
  destruct e.
  - apply (J.(ES).(confl_irrefl) a); assumption.
  - apply (G.(ES).(confl_irrefl) a); assumption.
Qed.

Next Obligation.
  destruct x,y.
  - apply J.(ES).(confl_sym);assumption.
  - split;trivial;trivial.
  - split;trivial;trivial.
  - apply G.(ES).(confl_sym);assumption.
Qed.

Definition extension (A B C: Set) (f1 : A -> C) (f2 : B -> C) : (sum A B)->C.
  exact (fun x => match x with |inl(a) => f1 a |inr(b) => f2 b end).
Defined.

Next Obligation.
  destruct a.
  -
    destruct ((J.(ES).(finiteness) a) H) as (f,(inj,bound)).
    exists (extension J.(ES).(A) G.(ES).(A) nat f (fun x=>0)).
    split.
    +
      intros a0 a'.
      destruct a0, a'.
      * intros;f_equal;apply (inj a0 a1);assumption.
      * intros;repeat mysplit;repeat myinv.
      * intros;repeat mysplit;repeat myinv.
      * intros;repeat mysplit;repeat myinv.
    +
      destruct bound as (n,n_bound_f).
      exists n. intros a0 petita0. destruct a0.
      * simpl; apply n_bound_f; apply petita0.
      * mysplit; myinv.
  -
    destruct ((G.(ES).(finiteness) a) H) as (f,(inj,bound)).
    exists (extension J.(ES).(A) G.(ES).(A) nat (fun x=>0) f).
    split.
    +
      intros a0 a'.
      destruct a0, a'.
      * intros;repeat mysplit;repeat myinv.
      * intros;repeat mysplit;repeat myinv.
      * intros;repeat mysplit;repeat myinv.
      * intros;f_equal;apply (inj a0 a1);assumption.
    +
      destruct bound as (n,n_bound_f).
      exists n. intros a0 petita0. destruct a0.
      * mysplit; myinv.
      * simpl; apply n_bound_f; apply petita0.
Qed.

Next Obligation.
  destruct e1, e2, e2'.
  - apply (J.(ES).(vendetta) a a0 a1) ;assumption.
  - myinv.
  - myinv.
  - myinv.
  - myinv.
  - myinv.
  - myinv.
  - apply (G.(ES).(vendetta) a a0 a1);assumption.
Qed.

Definition Game_tenseur (J G :Game) : Game :=
  Build_Game
    (ES_tenseur J G)
    (extension J.(ES).(A) G.(ES).(A) player J.(polarity) G.(polarity)).

(**
* Définition d'un jeu dual
*)

Definition Game_dual (J : Game) : Game :=
  Build_Game J.(ES) (fun x => match J.(polarity) x with |O=>P|P=>O end).

(**
* Définition d'un jeu thèse
*)
Definition Game_these (J G : Game) : Game :=
  Game_tenseur (Game_dual J) G.
