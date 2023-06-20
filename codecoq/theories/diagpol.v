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
