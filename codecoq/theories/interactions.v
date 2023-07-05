Require Import jeu.
Require Import residu.
Require Import strategy.
Require Import jeuthese.


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

Scheme OOO_induc := Induction for OOO_int Sort Prop
with OPP_induc := Induction for OPP_int Sort Prop
with POP_induc := Induction for POP_int Sort Prop.



Inductive prefixOOO `{J:Game} `{G:Game} `{H:Game} :
  (@OOO_int J G H) -> (@OOO_int J G H) -> Prop :=
  | nil_prefOOO : forall (s:@OOO_int J G H),
      prefixOOO nilOOO s

  | prefOOO_C : forall a m n s s',
    prefixOPP s s' ->
      prefixOOO (consOOO_C a m n s) (consOOO_C a m n s')

  | prefOOO_A : forall a m n s s',
    prefixPOP s s' ->
      prefixOOO (consOOO_A a m n s) (consOOO_A a m n s')

with prefixOPP `{J:Game} `{G:Game} `{H:Game} :
  (@OPP_int J G H) -> (@OPP_int J G H) -> Prop :=
  | prefOPP_C : forall a m n s s',
    prefixOOO s s' ->
      prefixOPP (consOPP_C a m n s) (consOPP_C a m n s')
  | prefOPP_B : forall a m n s s',
    prefixPOP s s' ->
      prefixOPP (consOPP_B a m n s) (consOPP_B a m n s')

with prefixPOP `{J:Game} `{G:Game} `{H:Game} :
  (@POP_int J G H) -> (@POP_int J G H) -> Prop :=
  | prefPOP_B : forall a m n s s',
    prefixOPP s s' ->
      prefixPOP (consPOP_B a m n s) (consPOP_B a m n s')

  | prefPOP_A : forall a m n s s',
    prefixOOO s s' ->
      prefixPOP (consPOP_A a m n s) (consPOP_A a m n s')
.

Scheme prefixOOO_induc := Induction for prefixOOO Sort Prop
with prefixOPP_induc := Induction for prefixOPP Sort Prop
with prefixPOP_induc := Induction for prefixPOP Sort Prop.



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
