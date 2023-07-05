Require Import jeu.
Require Import residu.

Notation "m · u":=(cons u m) (at level 49).

(**
* Définition des parties
 *)

Definition neg `{G:Game} (a:@A (@ES G)):= polarity a = O.

Definition pos `{G:Game} (a:@A (@ES G)):= polarity a = P.

Inductive O_play `{G:Game}:=
| nilO : O_play

| consO : forall (a:@A (@ES G)),
    minGame G a ->
    neg a ->
    @P_play (residual G a) ->
    O_play


with P_play `{G:Game}:=
| consP : forall (a:@A (@ES G)),
    minGame G a ->
    pos a ->
    @O_play (residual G a) ->
    P_play.


(**
* Définition des stratégies
 *)

Inductive prefixO `{G:Game} : O_play -> O_play -> Prop:=
| nil_prefO : forall s,
    prefixO nilO s

| cons_prefO: forall a m n s s',
  @prefixP (residual G a) s s' ->
    prefixO (@consO _ a m n s) (@consO _ a m n s')


with  prefixP `{G:Game} : P_play -> P_play -> Prop:=
| cons_prefP: forall a m p s s',
  @prefixO (residual G a) s s' ->
    prefixP (@consP _ a m p s) (@consP _ a m p s').



Definition prefixO_closed `{G:Game} (Pos : O_play ->Prop) :=
  forall s s', Pos s' -> prefixO s s' -> Pos s.



Inductive coherentO `{G:Game} : O_play -> O_play -> Prop:=
| nil_coherentO_l : forall s,
    coherentO nilO s

| nil_coherentO_r : forall s,
    coherentO s nilO

| cons_coherentO_neq : forall a a' m m' n n' s s',
  not( a = a') ->
    coherentO (@consO _ a m n s) (@consO _ a' m' n' s')

| cons_coherentO_eq : forall a m n s s',
  @coherentP (residual G a) s s' ->
    coherentO (@consO _ a m n s) (@consO _ a m n s')


with  coherentP `{G:Game} : P_play -> P_play -> Prop:=
| cons_coherentP_eq : forall a m n s s',
  @coherentO (residual G a) s s' ->
    coherentP (@consP _ a m n s) (@consP _ a m n s').



Class strategy `{G:Game} :=
  {
    S: O_play -> Prop;
    S_nonempty : S nilO;
    S_closed : prefixO_closed S;
    S_det : forall s s', S s  -> S s' -> coherentO s s';
  }.
