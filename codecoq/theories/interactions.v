Require Import jeu.
Require Import residu.
Require Import strategy.


(**
* Définition d'une interaction
 *)

Inductive OOO_int `{A:Game} `{B:Game} `{C:Game} :=
|nilOOO :
  OOO_int

|consOOO_C : forall c,
  minGame C c ->
  neg c ->
  @OPP_int A B (residual C c) ->
    @OOO_int A B C

|consOOO_A : forall a,
  minGame A a ->
  pos a ->
  @POP_int (residual A a) B C ->
    @OOO_int A B C


with OPP_int `{A:Game} `{B:Game} `{C:Game} :=
|consOPP_C : forall c,
  minGame C c ->
  pos c ->
  @OOO_int A B (residual C c) ->
    @OPP_int A B C

|consOPP_B : forall b,
  minGame B b ->
  neg b ->
  @POP_int A (residual B b) C ->
    @OPP_int A B C


with POP_int `{A:Game} `{B:Game} `{C:Game} :=
|consPOP_B : forall b,
  minGame B b ->
  pos b ->
  @OPP_int A (residual B b) C ->
    @POP_int A B C

|consPOP_A : forall a,
  minGame A a ->
  neg a ->
  @OOO_int (residual A a) B C ->
    @POP_int A B C
.



Inductive prefixOOO `{J:Game} `{G:Game} `{H:Game} :
  (@OOO_int J G H) -> (@OOO_int J G H) -> Prop :=
  | nil_prefOOO : forall (s:@OOO_int J G H),
      prefixOOO nilOOO s

  | prefOOO_C : forall a m m' n n' s s',
    prefixOPP s s' ->
      prefixOOO (consOOO_C a m n s) (consOOO_C a m' n' s')

  | prefOOO_A : forall a m m' n n' s s',
    prefixPOP s s' ->
      prefixOOO (consOOO_A a m n s) (consOOO_A a m' n' s')

with prefixOPP `{J:Game} `{G:Game} `{H:Game} :
  (@OPP_int J G H) -> (@OPP_int J G H) -> Prop :=
  | prefOPP_C : forall a m m' n n' s s',
    prefixOOO s s' ->
      prefixOPP (consOPP_C a m n s) (consOPP_C a m' n' s')
  | prefOPP_B : forall a m m' n n' s s',
    prefixPOP s s' ->
      prefixOPP (consOPP_B a m n s) (consOPP_B a m' n' s')

with prefixPOP `{J:Game} `{G:Game} `{H:Game} :
  (@POP_int J G H) -> (@POP_int J G H) -> Prop :=
  | prefPOP_B : forall a m m' n n' s s',
    prefixOPP s s' ->
      prefixPOP (consPOP_B a m n s) (consPOP_B a m' n' s')

  | prefPOP_A : forall a m m' n n' s s',
    prefixOOO s s' ->
      prefixPOP (consPOP_A a m n s) (consPOP_A a m' n' s')
.



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

Check consO_l.


(**
* Définition d'une stratégie sur un jeu A thèse B
 *)

Inductive prefixO2 `{J:Game} `{G:Game} :
  (@O_play2 J G)-> (@O_play2 J G)-> Prop:=
| nil_prefO2 : forall s,
    prefixO2 nilO2 s

| cons_prefO2_l: forall (a:J.(ES).(A)) m m' n n' (s s': (@P_play2 (residual J a) G)),
  @prefixP2 (residual J a) G s s'->
    @prefixO2 J G (@consO_l J G a m n s) (@consO_l J G a m' n' s')

| cons_prefO2_r: forall (a:G.(ES).(A)) m m' n n' (s s': (@P_play2 J (residual G a))),
  @prefixP2 J (residual G a) s s' ->
    @prefixO2 J G (@consO_r J G a m n s) (@consO_r J G a m' n' s')


with  prefixP2 `{J:Game} `{G:Game} :
  @P_play2 J G -> @P_play2 J G-> Prop:=
| cons_prefP2_l: forall (a:J.(ES).(A)) m m' p p' (s s': (@O_play2 (residual J a) G)),
  @prefixO2 (residual J a) G s s' ->
    @prefixP2 J G (@consP_l J G a m p s) (@consP_l J G a m' p' s')

| cons_prefP2_r: forall (a:G.(ES).(A)) m m' p p' (s s': (@O_play2 J (residual G a))),
  @prefixO2 J (residual G a) s s' ->
    @prefixP2 J G (@consP_r J G a m p s) (@consP_r J G a m' p' s').



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

  | cons_cohO2_eq_l : forall (a:J.(ES).(A)) (s s':(@P_play2 (residual J a) G)) m m' n n',
    @coherentP2 (residual J a) G s s' ->
      @coherentO2 J G (@consO_l J G a m n s) (@consO_l J G a m' n' s')

  | cons_cohO2_eq_r : forall (a:G.(ES).(A)) (s s':(@P_play2 J (residual G a))) m m' n n',
    @coherentP2 J (residual G a) s s' ->
      @coherentO2 J G (@consO_r J G a m n s) (@consO_r J G a m' n' s')

  with coherentP2 `{J : Game} `{G : Game} : (@P_play2 J G)-> (@P_play2 J G) -> Prop :=
  | cons_cohP2_eq_l : forall (a:J.(ES).(A)) (s s':(@O_play2 (residual J a) G)) m m' n n',
    @coherentO2 (residual J a) G s s' ->
      @coherentP2 J G (@consP_l J G a m n s) (@consP_l J G a m' n' s')

  | cons_cohP2_eq_r : forall (a:G.(ES).(A)) (s s':(@O_play2 J (residual G a))) m m' n n',
    @coherentO2 J (residual G a) s s' ->
      @coherentP2 J G (@consP_r J G a m n s) (@consP_r J G a m' n' s')
.



Class strategy2O `{J: Game} `{G: Game} :=
  {
    SO: (@O_play2 J G) -> Prop;
    SO_nonempty : SO nilO2;
    SO_closed : (@prefixO2_closed J G) SO;
    SO_det : forall s s', SO s  -> SO s' -> (@coherentO2 J G) s s';
  }.

Class strategy2P `{J: Game} `{G: Game} :=
  {
    SP: (@P_play2 J G) -> Prop;
    SP_closed : (@prefixP2_closed J G) SP;
    SP_det : forall s s', SP s -> SP s' -> (@coherentP2 J G) s s';
  }.


(**
* Définition des restrictions d'interaction
 *)



Fixpoint restriction_lm_OOO `{J :Game} `{G :Game} `{H : Game}
(u:(@OOO_int J G H)) : (@O_play2 J G) := match u with
  | nilOOO => nilO2
  | consOOO_C a m n u' => restriction_lm_OPP u'
  | consOOO_A a m n u' => consO_l a m n (restriction_lm_POP u')
  end
with
restriction_lm_OPP `{J :Game} `{G :Game} `{H : Game}
(u:(@OPP_int J G H)) : (@O_play2 J G) := match u with
  | consOPP_C a m n u' => restriction_lm_OOO u'
  | consOPP_B a m n u' => consO_r a m n (restriction_lm_POP u')
  end
with
restriction_lm_POP `{J :Game} `{G :Game} `{H : Game}
(u:(@POP_int J G H)) : (@P_play2 J G) :=
  match u with
  | consPOP_B a m n u' => consP_r a m n (restriction_lm_OPP u')
  | consPOP_A a m n u' => consP_l a m n (restriction_lm_OOO u')
  end
.



Fixpoint restriction_mr_OOO `{J :Game} `{G :Game} `{H : Game}
(u:(@OOO_int J G H)) : (@O_play2 G H) := match u with
  | nilOOO => nilO2
  | consOOO_C a m n u' => consO_r a m n (restriction_mr_OPP u')
  | consOOO_A a m n u' => restriction_mr_POP u'
  end
with
restriction_mr_OPP `{J :Game} `{G :Game} `{H : Game}
(u:(@OPP_int J G H)) : (@P_play2 G H) := match u with
  | consOPP_C a m n u' => consP_r a m n (restriction_mr_OOO u')
  | consOPP_B a m n u' => consP_l a m n (restriction_mr_POP u')
  end
with
restriction_mr_POP `{J :Game} `{G :Game} `{H : Game}
(u:(@POP_int J G H)) : (@O_play2 G H) :=
  match u with
  | consPOP_B a m n u' => consO_l a m n (restriction_mr_OPP u')
  | consPOP_A a m n u' => restriction_mr_OOO u'
  end
.


Fixpoint restriction_lr_OOO `{J :Game} `{G :Game} `{H : Game}
(u:(@OOO_int J G H)) : (@O_play2 J H) := match u with
  | nilOOO => nilO2
  | consOOO_C a m n u' => consO_r a m n (restriction_lr_OPP u')
  | consOOO_A a m n u' => consO_l a m n (restriction_lr_POP u')
  end
with
restriction_lr_OPP `{J :Game} `{G :Game} `{H : Game}
(u:(@OPP_int J G H)) : (@P_play2 J H) := match u with
  | consOPP_C a m n u' => consP_r a m n (restriction_lr_OOO u')
  | consOPP_B a m n u' => restriction_lr_POP u'
  end
with
restriction_lr_POP `{J :Game} `{G :Game} `{H : Game}
(u : (@POP_int J G H)) : (@P_play2 J H) :=
  match u with
  | consPOP_B a m n u' => restriction_lr_OPP u'
  | consPOP_A a m n u' => consP_l a m n (restriction_lr_OOO u')
  end
.
