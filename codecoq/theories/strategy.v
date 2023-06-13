Require Import jeu.
Require Import residu.


(* Définition des parties *)

Definition neg `{G:Game} (a:@A (@ES G)):= polarity a = O.

Definition pos `{G:Game} (a:@A (@ES G)):= polarity a = P.

Inductive O_play `{G:Game}:=
| nilO : O_play
| consO : forall (a:@A (@ES G)), minGame G a -> neg a -> @P_play (residual G a) -> O_play
with P_play `{G:Game}:=
| consP : forall (a:@A (@ES G)), minGame G a -> pos a -> @O_play (residual G a) -> P_play.
