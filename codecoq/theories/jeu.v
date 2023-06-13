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
