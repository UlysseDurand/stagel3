Require Import jeu.
Require Import residu.

Notation "m · u":=(cons u m) (at level 49).

(* Fixpoint concat `{A:Type} (u v:list A):= *)
(*   match v with *)
(*   |nil => u *)
(*   |cons a v => (concat u v) · a *)
(*   end. *)


(* Définition des parties *)

Definition neg `{G:Game} (a:@A (@ES G)):= polarity a = O.

Definition pos `{G:Game} (a:@A (@ES G)):= polarity a = P.

Inductive O_play `{G:Game}:=
| nilO : O_play
| consO : forall (a:@A (@ES G)), minGame G a -> neg a -> @P_play (residual G a) -> O_play
with P_play `{G:Game}:=
| consP : forall (a:@A (@ES G)), minGame G a -> pos a -> @O_play (residual G a) -> P_play.

Check consO.

(* EXERCISE : extraire la liste
    play : list E;
 puis vérifier :
    valid : is_valid play;
    nonrepeting : is_nonrepeting play;
    alt: @alternating _ polarity play;
    negative : is_negative play;
 *)

Fixpoint list_Oplay `{G:Game} (s:O_play) : list (G.(ES).(A)) :=
  match s with
  | nilO => nil
  | consO a mina nega s' => (list_Pplay s') · a
  end
with list_Pplay `{G:Game} (s:P_play) : list (G.(ES).(A)) :=
  match s with
  |consP a mina nega s' => list_Oplay s' · a
  end.




Inductive prefixO `{G:Game} : O_play -> O_play -> Prop:=
| nil_prefO : forall s, prefixO nilO s
| cons_prefO:
  forall a m m' n n' s s', prefixP s s' -> prefixO (@consO _ a m n s) (@consO _ a m' n' s')
with  prefixP `{G:Game} : P_play -> P_play -> Prop:=
| cons_prefP:
  forall a m m' p p' s s', prefixO s s' -> prefixP (@consP _ a m p s) (@consP _ a m' p' s').


Definition prefixO_closed `{G:Game} (Pos : O_play ->Prop) :=
  forall s s', Pos s' -> prefixO s s' -> Pos s.


Inductive coherentO `{G:Game} : O_play -> O_play -> Prop:=
| nil_coherentO_l : forall s, coherentO nilO s
| nil_coherentO_r : forall s, coherentO s nilO
| cons_coherentO_neq:
  forall a a' m m' n n' s s', not( a = a') -> coherentO (@consO _ a m n s) (@consO _ a' m' n' s')
| cons_coherentO_eq:
  forall a m m' n n' s s', coherentP s s' -> coherentO (@consO _ a m n s) (@consO _ a m' n' s')
with  coherentP `{G:Game} : P_play -> P_play -> Prop:=
| cons_coherentP_eq:
  forall a m m' n n' s s', coherentO s s' -> coherentP (@consP _ a m n s) (@consP _ a m' n' s').

Class strategy `{G:Game} :=
  {
    S: O_play -> Prop;
    S_nonempty : S nilO;
    S_closed : prefixO_closed S;
    S_det : forall s s', S s  -> S s' -> coherentO s s';
  }.
