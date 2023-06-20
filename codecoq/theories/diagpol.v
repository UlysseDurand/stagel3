Require Import jeu.
Require Import residu.
Require Import strategy.

Inductive OOO_int `{A:Game} `{B:Game} `{C:Game} :=
|nilOOO : OOO_int
|consOOO_C : forall c, minGame C c -> neg c ->
                  @OPP_int A B (residual C c) -> @OOO_int A B C
|consOOO_A : forall a, minGame A a -> pos a ->
                  @POP_int (residual A a) B C -> @OOO_int A B C
with OPP_int `{A:Game} `{B:Game} `{C:Game} :=
|consOPP_C : forall c, minGame C c -> pos c ->
                  @OOO_int A B (residual C c) -> @OPP_int A B C
|consOPP_B : forall b, minGame B b -> neg b ->
                  @POP_int A (residual B b) C -> @OPP_int A B C
with POP_int `{A:Game} `{B:Game} `{C:Game} :=
|consPOP_B : forall b, minGame B b -> pos b ->
                  @OPP_int A (residual B b) C -> @POP_int A B C
|consPOP_A : forall a, minGame A a -> neg a ->
                  @OOO_int (residual A a) B C -> @POP_int A B C
.


Inductive O_play2 `{A:Game} `{B:Game}:=
| nilO2 : @O_play2 A B
| consO_l : forall a, minGame A a -> pos a -> @P_play2 (residual A a) B -> @O_play2 A B
| consO_r : forall b, minGame B b -> neg b -> @P_play2 A (residual B b) -> @O_play2 A B
with P_play2 `{A:Game} `{B:Game}:=
| consP_l : forall a, minGame A a -> neg a -> @O_play2 (residual A a) B -> @P_play2 A B
| consP_r : forall b, minGame B b -> pos b -> @O_play2 A (residual B b) -> @P_play2 A B.

Inductive prefixO2 `{A:Game} `{B:Game} :
  (@O_play2 A B)-> (@O_play2 A B)-> Prop:=
| nil_prefO2 : forall s, prefixO2 nilO2 s
| cons_prefO2_l:
  forall a m m' n n' (s s':@P_play2 (residual A a) B),
    @prefixP2 (residual A a) B s s'
    -> @prefixO2 A B (@consO_l A B a m n s) (@consO_l A B a m' n' s')
| cons_prefO2_r:
  forall a m m' n n' s s', prefixP2 s s' -> prefixO2 (@consO_r _ _ a m n s) (@consO_r _ _ a m' n' s')
with  prefixP2 `{A:Game} `{B:Game} : @P_play2 A B -> @P_play2 A B-> Prop:=
| cons_prefP2_l:
  forall a m m' p p' s s', prefixO2 s s' -> prefixP2 (@consP_l _ _ a m p s) (@consP_l _ _ a m' p' s')
| cons_prefP2_r:
  forall a m m' p p' s s', prefixO2 s s' -> prefixP2 (@consP_r _ _ a m p s) (@consP_r _ _ a m' p' s').

Definition prefixO2_closed `{G:Game} (Pos : O_play ->Prop) :=
  forall s s', Pos s' -> prefixO s s' -> Pos s.

Inductive Coherent2 `{G: Game} : O_play2 -> O_play2 -> Prop :=
  epsilon1


(* Todo list *)

(*
- coherent2 (mm chose)
-> strategy2

- restriction


*)
