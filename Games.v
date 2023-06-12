Set Implicit Arguments.
Set Contextual Implicit.

Require Import Program.
Require Import Lia.

Inductive player:=
| P: player
| O: player.

Definition player_bool :player -> bool:=
  fun p => match p with P => true | O => false end.

Coercion player_bool : player >-> bool.


(** Sequenced-like view on lists, 
new elements are added on the right. *)

Notation "m · u":=(cons u m) (at level 49).

Fixpoint concat `{A:Type} (u v:list A):=
  match v with
  |nil => u
  |cons a v => (concat u v) · a
  end.

Notation "u @ v":=(concat u v) (at level 50).

Lemma cons_cat_cons `{A:Type}:
  forall (a:A) l, exists l' b, (nil · a)@ l = l' · b.
Proof.
  intros a l. destruct l.
  - exists nil;exists a;reflexivity.
  - exists (nil·a @ l);exists a0;reflexivity.
Qed.

Lemma cat_comm `{A:Type}:
  forall (u v w:list A), u @ (v @ w) = (u @ v) @ w.
Proof.
  intros u v w;revert u w; induction w;simpl.
  - reflexivity.
  - now rewrite IHw.
Qed.


Lemma cat_nil_l `{A:Type}:
  forall (u :list A), nil @ u = u.
Proof.
  induction u.
  - reflexivity.
  - simpl. now rewrite IHu.
Qed.

Lemma cat_nil_r `{A:Type}:
  forall (u :list A), u @ nil = u.
Proof.
  reflexivity.
Qed.


Lemma cat_nil_nil `{A:Type}:
  forall (u v:list A),u @ v =nil ->  u = nil /\ v = nil.
Proof.
  intros u v;revert u;induction v;simpl;intros;split;trivial.
  inversion H. inversion H.
Qed.

Lemma cat_inv_r `{A:Type}:
  forall (a:A) (u v w:list A), u@v =w · a -> v = nil \/ exists v', u@v' = w /\ v = v' · a.
Proof.
  intros a u v ;revert u a; induction v;intros;simpl in *.
  - now left.
  - inversion H. right. exists v;now split.
Qed.

Lemma cat_inv_l `{A:Type}:
  forall (a b:A) (u v:list A), (nil · a) @ u =(nil · b) @ v -> a=b /\ u = v.
Proof.
  intros a b u v;revert a b u; induction v;intros;simpl in *.
  - destruct u;simpl in *;inversion H;subst. now split.
    destruct (cat_nil_nil  H2). inversion H0.
  - destruct (cat_inv_r    _ H);subst;simpl in *.
    inversion H;subst. symmetry in H2. destruct (cat_nil_nil H2). inversion H0.
    destruct H0 as (w,(Hw,Hu));subst.
    destruct (IHv _ _ _ Hw);subst;now split.
Qed.

Lemma len_cat `{A:Type}:
  forall (u v:list A), length (u @ v) = length u + length v.
Proof.
  intros u v;induction v;intros.
  - simpl. lia.
  - simpl. rewrite IHv. lia.
Qed.    


Inductive prefix `{M:Type}  : list M -> list M -> Prop:=
|prefix_id : forall l, prefix l l
|prefix_cons : forall a l l', prefix l l' -> prefix l (l'·a).

Notation " l ⊆ l' ":=(prefix l l') (at level 51).

Definition prefix_closed `{M:Type} (Pos : list M ->Prop) :=
  forall l l', Pos l' -> l ⊆ l' -> Pos l.


Fixpoint rev_aux `{A:Type} (u acc:list A):=
  match u with
  |nil => acc
  |cons a v => (rev_aux v (acc · a))
  end.

Definition rev `{A:Type} (u:list A):= rev_aux u nil.

Lemma rev_aux_cat  `{A:Type}:
  forall (l acc:list A), rev_aux l acc = acc @ rev l.
Proof.  
  intro l;induction l;intros.
  - reflexivity.
  - cbn. do 2 rewrite IHl.
    now rewrite cat_comm.
Qed.

Lemma rev_cons  `{A:Type} (l:list A) a:
  rev (l·a) = (nil · a) @ (rev l).
Proof.
  cbn. now rewrite rev_aux_cat.
Qed.


Lemma rev_cat  `{A:Type}:
  forall (l1 l2:list A), rev (l1@l2) = (rev l2) @ rev l1.
Proof.
  intros l1 l2;revert l1;induction l2;intros.
  - unfold rev. simpl. now rewrite cat_nil_l.
  - simpl. now rewrite rev_cons,IHl2,cat_comm,<-rev_cons.
Qed.

Lemma rev_idempotent `{A:Type}:
  forall (l:list A), rev (rev l)=l.
Proof.
  induction l.
  - reflexivity.
  - now rewrite rev_cons,rev_cat,IHl.
Qed.

Lemma list_ind_rev `{A:Type}:
  forall (P : list A -> Prop),
       P nil ->
       (forall (a : A) (l : list A ), P l -> P ((nil · a)@l)) -> forall l : list A , P l.
Proof.
  intros P Hnil IH l.
  rewrite <- rev_idempotent .
  induction (rev l).
  - assumption.
  - rewrite rev_cons. now apply IH.
Qed. 



Inductive alternating `{M:Type} `{Λ: M -> player}: list M -> Prop :=
| alt_nil : alternating (@nil M)
| alt_singleton : forall a, alternating (nil · a)
| alt_cons : forall a b l, alternating (l · a) -> Λ a <> Λ b -> alternating (l · a · b).

(** * Simple Game  *)

Class SimpleGame := {
    M : Set;
    Λ : M -> player;
    Pos : list M ->Prop;

    nonempty : Pos nil;
    closed_Pos : prefix_closed Pos;
    alt_Pos :  forall l, Pos l -> @alternating _ Λ l;
    starts_O :  forall l a, Pos ((nil · a) @l) -> Λ a=O;
}.


(** ** Example : Bool *)

Inductive Mbool:=
  q : Mbool |tt : Mbool | ff:Mbool.

Definition Λbool (m:Mbool) :=
  match m with
    q  => O 
  | tt => P
  | ff => P
  end.

Definition Pbool l :=
  match l with
  |nil |nil · q | nil · q · tt | nil · q · ff => True
  | _ => False
  end.
  


Program Definition simpleBool :=
  @Build_SimpleGame Mbool Λbool Pbool _ _ _ _. 
Next Obligation.
  intros l l' H' Leq.                   
  destruct l';inversion Leq;subst;trivial.
  destruct l';inversion Leq;subst;trivial.
  - now inversion H1.
  - destruct l';simpl in H';destruct m;destruct m0;try (now exfalso).
    + inversion H1;subst;trivial. now inversion H3.
    + inversion H1;subst;trivial. now inversion H3.
Qed.
Next Obligation.
  destruct l;[apply alt_nil|].
  destruct l;[apply alt_singleton|].
  destruct l;destruct m0;destruct m;try (now exfalso).
  - apply alt_cons;[apply alt_singleton|intro;now exfalso].
  - apply alt_cons;[apply alt_singleton|intro;now exfalso].
Qed.
Next Obligation.
  destruct l;simpl in H.
  - destruct a;trivial;now exfalso.
  - destruct l;destruct m;destruct a;simpl in H;trivial;try now exfalso.
    destruct l;destruct m0;simpl in H;now exfalso.
    destruct l;destruct m0;simpl in H;now exfalso.
    destruct l;destruct m0;simpl in H;now exfalso.
    destruct l;destruct m0;simpl in H;now exfalso.
Qed.


(** * Event structures *)


Definition injection  `{A:Type} (f:A -> nat) :=
  forall a a', f a = f a' -> a = a'.

Definition bounded_under  `{A:Type} `{ord: A->A->Prop} (a:A) (f:A -> nat) :=
  exists n, forall a', ord a' a ->  f a' <= n.

(* This might be too naive, at least it avoids defining a general notion 
of finiteness that cannot be applied on subset types {a' | a' ≤ a} because
of the non-uniqueness of proofs for a' ≤ a. *)

Definition finite_under `{A:Type} `{ord: A->A->Prop} (a:A) :=
  exists (f:A->nat), injection f /\ forall a, @bounded_under _ ord a f.


(** We rely on Coq equality for E, which may cause troubles afterwards... *)

Class EventStructure := {
    E: Set;
    
    ord : E -> E -> Prop;
    conflict : E -> E -> Prop;

    ord_refl : forall e, ord e e;
    ord_antisym : forall e f, ord e f -> ord f e -> e = f;
    ord_trans : forall e f g, ord e f -> ord f g -> ord e g;
    

    conf_irrefl: forall e, not (conflict e e);

    finiteness: forall e, @finite_under _ ord e;
    vendetta: forall e1 e2 e2', conflict e1 e2 -> ord e2 e2' -> conflict e1 e2'

  }.


Infix "≤E":= ord (at level 50).
Infix "#":= conflict (at level 50).


Definition dw_closed `{E:Type} `{ord:E -> E -> Prop} (P:E->Prop):=
  forall e e', P e -> ord e'  e -> P e'.


(* Again, this might be an extremely naive way to define finite inclusions...*)

Definition finite_inc `{E:Type} (C:E->Prop) :=
  exists (f:E->nat), injection f /\ exists n, forall e, C e -> f e <= n.

Definition is_configuration `{ES:EventStructure}:=
  fun (C:E ->  Prop) => finite_inc C /\ @dw_closed _ ord C /\ forall e e', C e -> C e' -> not (conflict e e').

Class configuration `{ES:EventStructure}:=
  {
    C : E ->  Prop;
    conf_finite : finite_inc C;
    conf_closed : @dw_closed _ ord C;
    conf_noconflict : forall e e', C e -> C e' -> not (conflict e e')
  }.


Definition justifies `{ES:EventStructure} (x:configuration) (e:E):=
  not (C e) /\ is_configuration (fun f => f = e \/ C f).


Class Game  :=
  {
    ES:EventStructure;
    polarity : E -> player
}.


Definition ordBool (b b':Mbool):=
  match (b,b') with
  |(q,tt) |(q,ff) | (q,q) | (tt,tt) | (ff,ff) => True
  | _ => False
  end.

Definition conflictBool (b b':Mbool):=
  match (b,b') with (tt,ff) => True | _ => False end.


Ltac boolbycase :=
  repeat (match  goal with
  | [ a : Mbool |- _ ] => destruct a
  end).


(* Naive function to prove finiteness constraints on bool. *)

Definition MBool_to_nat:=
  fun (b:Mbool) =>
       match b with q => 0 | tt => 1 | ff => 2 end.

Obligation Tactic:=intros;try (now boolbycase).
Program Definition ESBool :=
  @Build_EventStructure Mbool ordBool conflictBool _ _ _ _ _ _  .
Next Obligation.
  exists MBool_to_nat. split.
  - intros a b H. now boolbycase.
  - intros a;exists 3;intros. boolbycase;cbv in H;cbv;now lia.
Qed.


Definition GameBool := @Build_Game ESBool Λbool .


(** This looks like the last thing you would like to manipulate... maybe
we should force a configuration to be presented as a list of its elements. *)

Fixpoint set_of_list `{E:Type} (l:list E):=
  match l with
  | nil => fun e => False
  | l · f => fun e => e = f \/ set_of_list l e
  end.

Fixpoint tail_n `{E:Type} (l:list E) n:list E:=
  match n with
  | 0 => l
  | S m => match l with
          | nil => nil
          | l' · f => (tail_n  l' m) · f
          end
  end.

Definition head_n `{E:Type} (l:list E) n:=tail_n (rev l) n.

Definition is_valid  `{G:Game} (play:list E):Prop
  :=forall n, n<= length play -> @is_configuration (@ES G) (set_of_list (head_n play n)).
Parameter is_nonrepeting :forall E, list E -> Prop.
Parameter is_negative : forall E, list E -> Prop.

Definition is_Match `{G:Game} (play:list E):=
  is_valid play /\ is_nonrepeting play /\ (@alternating _ polarity play)  /\  is_negative play.
                               
Class Match `{G:Game} := {
    play : list E;
    valid : is_valid play;
    nonrepeting : is_nonrepeting play;
    alt: @alternating _ polarity play;
    negative : is_negative play;
  }.


Program Definition game_simple `{ES:EventStructure} (G:Game):SimpleGame :=
  @Build_SimpleGame E polarity is_Match _ _ _ _ .
Next Obligation.
  repeat split;admit.
Admitted.
Next Obligation.  
Admitted.
Next Obligation.  
Admitted.
Next Obligation.  
Admitted.


Definition receptive  `{G:Game} (S:list E -> Prop):=
  forall a s,  S s -> polarity a = O -> is_Match (s·a) -> S (s·a).

Class strategy `{G:Game} :=
  {
    S: list E -> Prop;
    S_nonempty : S nil;
    S_closed : prefix_closed S;
    S_det : forall l a b, polarity a = P -> polarity b = P -> S (l·a) -> S (l·b) -> a = b;
    S_receptive : receptive S;
  }.



(** * Constructions on games *)


(** ** Tensor A₁ ⊗ A₂ *)

(* Parameter tensorES : forall (E1 E2:EventStructure), EventStructure . *)
Program Definition tensorES (E1 E2:EventStructure): EventStructure :=
  @Build_EventStructure (@E E1 * @E E2) _ _ _ _ _ _ _ _ .
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.


Program Definition tensor  `{A:Game} `{B:Game}:=
    @Build_Game (@tensorES (@ES A) (@ES B)) _.
Next Obligation.
Admitted.

Notation "A ⊗ B":=(@tensor A B) (at level 51).

(** Example : bool ⊗ bool ? *)

(** ** Dual A^⊥ *)

Definition dualES (E:EventStructure): EventStructure.
Admitted.

Program Definition dual (A:Game):=
  @Build_Game (@dualES (@ES A)) _.
Next Obligation.
Admitted.
Notation "A ^⊥":=(dual A) (at level 51).


(** ** Entailment A ⊢ B *)

Definition composition  (A B:Game):=
  (A ^⊥) ⊗ B.


Notation "A ⊢ B":=(composition A B) (at level 51).

(** ** Restriction s ↾ A *)

(* Definition restriction (A B:Game) (s:list A ⊗ B):list A. *)
(*   (A ^⊥) ⊗ B. *)


  
(** * Constructions on strategies *)

(** ** Catégories *)

(** ** Copycat *)


(** copycat : bool ⊗ bool ⊢ bool ⊗ bool *)




Definition interaction `{A:Game} `{B:Game} `{C:Game}
           (u: list (@E (@ES (A ⊗ B ⊗ C)))): Prop.
Admitted.
  (* 
u ∈ (A ⊗ B ⊗ C)* telle que
* u ↾ A,B ∈ P(A⊢B)
* u ↾ B,C ∈ P(B⊢C)
* u ↾ A,C ∈ P(A⊢C)
*)


Notation " I[ A , B , C ]":=(interaction A B C) (at level 51). 

Definition tensor_strategy `{A:Game} `{B:Game} `{C:Game} 
           (σ:@strategy (A ⊢ B)) (τ:@strategy  (B ⊢ C)) :strategy.
Admitted.
(* {u | I[A,B,C] u /\ u ↾ A,B ∈ σ /\ u ↾ A,B ∈ τ } *)



Definition composition_prestrat `{A:Game} `{B:Game} `{C:Game} 
           (σ:@strategy (A ⊢ B)) (τ:@strategy  (B ⊢ C)) :
  list (@E (@ES (A⊢C))) -> Prop.
Admitted.
(* {u ↾ A,C | u ∈ tensor_strategy σ τ} *)


Definition even n:=exists k, n = 2*k.
Definition even_l `{A:Type} (u:list A):=even (length u).

(*
Lemma polarities_interactions:
  forall A B C u, I[A,B,C] u ->  even_l (u ↾ A,C) 
             ->  even_l (u ↾ A,B) /\  even_l (u ↾ B,C) 
*)


(* Attention b dans A,B et b dans A,B,C différent !! *)

(* Lemma sublemma: *)
(*   forall A B C u m b, *)
(*     I[A,B,C] (u·m·b) -> @polarity (A ⊢ B) b = O. *)

(* 
Supposons 
@polarity (A ⊢ B) b = P
donc um est dans l'état OOO
donc um ↾ A,B et um ↾ B,C sont dans l'état O
. si polarity B b = O, polarity  (B⊢C) b = P
donc  umb ↾ B,C non-alternant
. si polarity B b = P, polarity  (A⊢B) b = O
donc  umb ↾ A,B non-alternant
 *)


Lemma bla: 
  forall A B C s  (σ:@strategy (A ⊢ B)) (τ:@strategy  (B ⊢ C)) n,
    (composition_prestrat σ τ ) s -> length s = 2*n ->
     exists u,  @S _ (tensor_strategy σ τ)  u (* /\  s = restriction u  (A,C)*)
        /\ forall u', @S _ (tensor_strategy σ τ) u' (*  /\ s = restriction u'  (A,C)*) -> u = u'
.
Proof.
  intros.
  eexists. (* par définition ?*) 
  split.
  - admit.
  - intros.
(*
w = plus grand préfixe commun

w m₁ ⊆ u

w m₂ ⊆ v

* w est dans l'état OOO 
-> polarity (A ⊢ C) m₁ = O
(par diagramme de polarité, seul coup possible)
et alors wm₁⊆v -> contradiction


* w est dans l'état POP 
-> polarity (A ⊢ B) m₁ = P
(digramme de polarité, deux coups possibles)
donc (w ↾A,B) m₁+ et (w ↾A,B) m₂+ sont dans σ
par déterminisme, m₁ = m₂

* OPP : symmétrique 
-> polarity (B ⊢ C) m₁ = P
(digramme de polarité, deux coups possibles)
donc (w ↾B,C) m₁+ et (w ↾B,C) m₂+ sont dans σ
par déterminisme, m₁ = m₂

*)
Admitted.

(* Proposition composition_prestrat_det:
   determinist ... *)

(* 
Supposons 
composition_prestrat σ τ (sm)
composition_prestrat σ τ (sn)
pol m = pol n = +

prenons les témoins u,v tq ....

prenons w le plus grand préfixe commun de um et vn

même cas que pour la preuve du lemme

 *)

      
Lemma  precomposition_receptive `{A:Game} `{B:Game} `{C:Game} 
       (σ:@strategy (A ⊢ B)) (τ:@strategy  (B ⊢ C)) :
  receptive (composition_prestrat σ τ).
Proof.
  intros e s comp Hs (Val,(Rep,(Alt,Neg))).
(* 
s tq:
s c- ∈ P(A ⊢ c)

Prenons u ∈ σ || τ tq u ↾ A,C = s
(témoin)

s est dans l'état O, donc u est dans OOO par diagramme polarité
donc u ↾ B,C état O

donc (u ↾ B,C)c- ∈ P(B⊢C)
(valide : Mq |(u ↾ B,C)|∪{c} 
is_configuration B |(u ↾ B,C)c↾B| 
(u ↾ B,C)c↾C  = sc↾C 
or sc∈P(A⊢C)
Donc is_configuration C |sc↾C| 
Donc is_configuration C |(u ↾ B,C)c↾C|

is_alternating :
u ↾ B,C état O

is_negative:
u↾B,C = ε
(u↾B,C)c- négative 

Donc (u↾B,C)c- ∈ P(B⊢C)

Or τ réceptive, don (u↾B,C)c = (uc↾B,C) ∈ τ

uc ↾ A,B = u ↾ A,B ∈ σ
uc ↾ B,C ∈ τ
uc ↾ A,C ∈ P(A ⊢C)

Donc uc ∈ σ ⊗ τ
et uc ↾ A,C = sc
donc sc ∈ τ∘σ

 *)
Admitted.
  
Definition composition_strat `{A:Game} `{B:Game} `{C:Game} 
           (σ:@strategy (A ⊢ B)) (τ:@strategy  (B ⊢ C)) :
  @strategy (A ⊢ C).
Admitted.
  
Notation "τ ∘ σ":= (composition_strat σ τ).

Parameter copycat : forall A:Game, @strategy (A ⊢ A).


Proposition cc_id_l `{A:Game} `{B:Game}  (σ:@strategy (A ⊢ B)):
  (@copycat B)∘ σ = σ.
Proof.
  (*
Par double inclusion (axiome ?)

⊆
soit s ∈ cc ∘ σ
si s état O,
soit u∈ σ || ccB son témoin 

u ↾ A,B ∈ σ
u ↾ B₁,B₂ ∈ ccB  
(état O)

"par def" de ccB,
u↾A,B₁ = u↾A,B₂ = s
(car u↾B₁ =  u↾B₂ (exo ??))


*)
Admitted.


Proposition cc_id_r `{A:Game} `{B:Game}  (σ:@strategy (A ⊢ B)):
  σ ∘ (@copycat A)=σ.
Admitted.




(** * Associativity  *)

Definition interaction4 `{A:Game} `{B:Game} `{C:Game} `{D:Game}
           (u: list (@E (@ES (A ⊗ B ⊗ C ⊗ D)))): Prop.
Admitted.
  (* 
u ∈ (A ⊗ B ⊗ C ⊗ D)* telle que
* u ↾ A,B ∈ P(A⊢B)
* u ↾ B,C ∈ P(B⊢C)
* u ↾ C,D ∈ P(C⊢D)
* u ↾ A,D ∈ P(A⊢D)
*)



(*
Inductive polarity4 `{A:Game} `{B:Game} `{C:Game} `{D:Game}


          →→→→→→→→→→
          ↑               ↓
     P O O P ←←←←←     ↓
     |     ↑         ↑    ↓
     a-    a+        b-  b+
     ↓     |         ↑    ↓
 ←→ O O O O        O P O P
     ↑     ↓         ↓    ↑
     d+    d-       c+   c-  
     ↑     ↓         ↓    ↑
     O O P P  ←←←       ↑
           ↓             ↑
           →→→→→→→→ ↑
*)




Proposition interaction43 `{A:Game} `{B:Game} `{C:Game} `{D:Game}:
  forall w, (interaction4 w) -> interaction w.
  (* suspicieux que ça type-check... w devrait être w ↾ A,B,C à droite *)
  Admitted.






Lemma zipping `{A:Game} `{B:Game} `{C:Game} `{D:Game}:
  forall u v, I[A,B,D] u -> I[B,C,D] v -> exists w, @interaction4 A B C D w
(*
w ↾A,B,D = u
w ↾B,C,D = v
*).
  




Proposition comp_assoc `{A:Game} `{B:Game} `{C:Game} `{D:Game}
  (σ:@strategy (A ⊢ B)) (τ:@strategy  (B ⊢ C))  (δ:@strategy (C ⊢ D)):
    δ ∘ (τ ∘ σ) = (δ ∘ τ) ∘ σ.
Proof.
  (* 
⊇ soit s ∈ (δ ∘ τ) ∘ σ.
il existe u ∈ σ ||  (δ ∘ τ)  (I(A,B,D))
tq u ↾A,B ∈ σ
   u ↾A,D = s
   u ↾B,D = δ∘τ

il existe v ∈ τ || δ   (I(B,C,D))
tq v ↾B,C ∈ τ
   v ↾C,D ∈ δ
   v ↾B,D = u ↾B,D


Par zipping
il existe w ∈ I[A,B,C,D]
tq ...

Mq w ↾ A,B,C ∈ σ || τ
w ↾ A,B ∈ σ 
= (w ↾ A,B,D) ↾ A,B = u ↾ A,B ∈ σ

w ↾ B,C ∈ σ 
= (w ↾ B,C,D) ↾ B,C = v ↾ B,C ∈ τ

donc w ↾ A,C ∈ τ∘σ

w ↾ C,D ∈ σ 
= (w ↾ B,C,D) ↾ C,D = v ↾ C,D ∈ δ

donc w↾A,C,D ∈ (τ∘σ)||δ

donc w↾A,D ∈ δ∘(τ∘σ)

Or w↾A,D = (w↾A,B,D)↾A,D=u↾A,D=s
donc s ∈ δ∘(τ∘σ)



 *)


  
Admitted.

