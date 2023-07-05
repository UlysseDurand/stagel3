Require Import utiles.
Require Import jeu.
Require Import strategy.
Require Import residu.


(**
Dans la suite tous les 2 désignent la version d'un objet adaptée
pour un jeu A thèse B
 *)

(**
* Définition d'une partie sur un jeu A thèse B
 *)

Inductive O_play2 `{J:Game} `{G:Game}:=
| nilO2 :
    @O_play2 J G

| consO_l : forall a,
  minGame J a ->
  @pos J a ->
  @P_play2 (residual J a) G ->
    @O_play2 J G

| consO_r : forall b,
  minGame G b ->
  @neg G b ->
  @P_play2 J (residual G b) ->
    @O_play2 J G


with P_play2 `{J:Game} `{G:Game}:=
| consP_l : forall a,
  minGame J a ->
  @neg J a ->
  @O_play2 (residual J a) G ->
    @P_play2 J G

| consP_r : forall b,
  minGame G b ->
  @pos G b ->
  @O_play2 J (residual G b) ->
    @P_play2 J G.

Scheme O_play2_induc := Induction for O_play2 Sort Prop
with P_play2_induc := Induction for P_play2 Sort Prop.



(**
* Définition d'une stratégie sur un jeu A thèse B
 *)

Inductive prefixO2 `{J:Game} `{G:Game} :
  (@O_play2 J G)-> (@O_play2 J G)-> Prop:=
| nil_prefO2 : forall s,
    prefixO2 nilO2 s

| cons_prefO2_l: forall (a:J.(ES).(A)) m n (s s': (@P_play2 (residual J a) G)),
  @prefixP2 (residual J a) G s s'->
    @prefixO2 J G (@consO_l J G a m n s) (@consO_l J G a m n s')

| cons_prefO2_r: forall (a:G.(ES).(A)) m n (s s': (@P_play2 J (residual G a))),
  @prefixP2 J (residual G a) s s' ->
    @prefixO2 J G (@consO_r J G a m n s) (@consO_r J G a m n s')


with  prefixP2 `{J:Game} `{G:Game} :
  @P_play2 J G -> @P_play2 J G-> Prop:=
| cons_prefP2_l: forall (a:J.(ES).(A)) m p (s s': (@O_play2 (residual J a) G)),
  @prefixO2 (residual J a) G s s' ->
    @prefixP2 J G (@consP_l J G a m p s) (@consP_l J G a m p s')

| cons_prefP2_r: forall (a:G.(ES).(A)) m p (s s': (@O_play2 J (residual G a))),
  @prefixO2 J (residual G a) s s' ->
    @prefixP2 J G (@consP_r J G a m p s) (@consP_r J G a m p s').

Scheme prefixO2_induc := Induction for prefixO2 Sort Prop
with prefixP2_induc := Induction for prefixP2 Sort Prop.



Definition prefixO2_closed `{J:Game} `{G:Game} (Pos : (@O_play2 J G) -> Prop) :=
  forall (s s' : (@O_play2 J G)), Pos s' -> (@prefixO2 J G) s s' -> Pos s.

Definition prefixP2_closed `{J:Game} `{G:Game} (Pos : (@P_play2 J G) -> Prop) :=
  forall (s s' : (@P_play2 J G)), Pos s' -> (@prefixP2 J G) s s' -> Pos s.



Inductive coherentO2 `{J : Game} `{G : Game} : (@O_play2 J G) -> (@O_play2 J G) -> Prop :=
  | nil_cohO2_l : forall s,
      @coherentO2 J G nilO2 s

  | nil_cohO2_r : forall s,
      @coherentO2 J G s nilO2

  | cons_cohO2_neq_ll : forall a a' s s' m m' n n',
    not (a=a') ->
      @coherentO2 J G (@consO_l _ _ a m n s) (@consO_l _ _ a' m' n' s')

  | cons_cohO2_neq_rr : forall a a' s s' m m' n n',
    not (a=a') ->
      @coherentO2 J G (@consO_r _ _ a m n s) (@consO_r _ _ a' m' n' s')

  | cons_cohO2_neq_lr : forall a a' (s : @P_play2 (residual J a) G) (s': @P_play2 J (residual G a')) m m' n n',
      @coherentO2 J G (@consO_l _ _ a m n s) (@consO_r _ _ a' m' n' s')

  | cons_cohO2_neq_rl : forall a a' s s' m m' n n',
      @coherentO2 J G (@consO_r _ _ a m n s) (@consO_l _ _ a' m' n' s')

  | cons_cohO2_eq_l : forall (a:J.(ES).(A)) (s s':(@P_play2 (residual J a) G)) m n,
    @coherentP2 (residual J a) G s s' ->
      @coherentO2 J G (@consO_l J G a m n s) (@consO_l J G a m n s')

  | cons_cohO2_eq_r : forall (a:G.(ES).(A)) (s s':(@P_play2 J (residual G a))) m n,
    @coherentP2 J (residual G a) s s' ->
      @coherentO2 J G (@consO_r J G a m n s) (@consO_r J G a m n s')

  with coherentP2 `{J : Game} `{G : Game} : (@P_play2 J G)-> (@P_play2 J G) -> Prop :=
  | cons_cohP2_eq_l : forall (a:J.(ES).(A)) (s s':(@O_play2 (residual J a) G)) m n,
    @coherentO2 (residual J a) G s s' ->
      @coherentP2 J G (@consP_l J G a m n s) (@consP_l J G a m n s')

  | cons_cohP2_eq_r : forall (a:G.(ES).(A)) (s s':(@O_play2 J (residual G a))) m n,
    @coherentO2 J (residual G a) s s' ->
      @coherentP2 J G (@consP_r J G a m n s) (@consP_r J G a m n s')
.

Scheme coherentO2_induc := Induction for coherentO2 Sort Prop
with coherentP2_induc := Induction for coherentP2 Sort Prop.



Class strategy2O `{J: Game} `{G: Game} :=
  {
    SO: (@O_play2 J G) -> Prop;
    SO_closed : (@prefixO2_closed J G) SO;
    SO_det : forall s s', SO s  -> SO s' -> (@coherentO2 J G) s s';
  }.

Class strategy2P `{J: Game} `{G: Game} :=
  {
    SP: (@P_play2 J G) -> Prop;
    SP_closed : (@prefixP2_closed J G) SP;
    SP_det : forall s s', SP s -> SP s' -> (@coherentP2 J G) s s';
  }.
