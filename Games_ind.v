Set Implicit Arguments.
Set Contextual Implicit.

Require Import Program.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
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

(* Fixpoint concat `{A:Type} (u v:list A):= *)
(*   match v with *)
(*   |nil => u *)
(*   |cons a v => (concat u v) · a *)
(*   end. *)

 Notation "u @ v":=(v++ u) (at level 50).

Lemma cons_cat_cons `{A:Type}:
  forall (a:A) l, exists l' b, [:: a]@ l = l' · b.
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
  - by rewrite addn0. 
  -by simpl;rewrite IHv addnS. 
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
  - by rewrite cat_nil_l.
  - simpl. by rewrite rev_cons IHl2 cat_comm -rev_cons.
Qed.

Lemma rev_idempotent `{A:Type}:
  forall (l:list A), rev (rev l)=l.
Proof.
  induction l.
  - reflexivity.
  - now rewrite rev_cons rev_cat IHl.
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



Inductive alternating `{M:Type} `{Λ: M -> player}:
  list M -> Prop :=
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
    starts_O :  forall l a, Pos ((nil · a) @l) -> Λ a = O;
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
    A: Set;
    
    ord : A -> A -> Prop;
    conflict : A -> A -> Prop;

    ord_refl : forall e, ord e e;
    ord_antisym : forall e f, ord e f -> ord f e -> e = f;
    ord_trans : forall e f g, ord e f -> ord f g -> ord e g;
    

    conf_irrefl: forall e, not (conflict e e);

    finiteness: forall e, @finite_under _ ord e;
    vendetta: forall e1 e2 e2', conflict e1 e2 -> ord e2 e2' -> conflict e1 e2'
                                                                  
  }.


Infix "≤A":= ord (at level 50).
Infix "#":= conflict (at level 50).


Definition dw_closed `{E:Type} `{ord:E -> E -> Prop} (P:E->Prop):=
  forall e e', P e -> ord e' e -> P e'.


(* Again, this might be an extremely naive way to define finite inclusions...*)

Definition finite_inc `{E:Type} (C:E->Prop) :=
  exists (f:E->nat), injection f /\ exists n, forall e, C e -> f e <= n.

Definition is_configuration `{ES:EventStructure}:=
  fun (C:A ->  Prop) => finite_inc C /\ @dw_closed _ ord C /\ forall e e', C e -> C e' -> not (conflict e e').

Class configuration `{ES:EventStructure}:=
  {
    C : A ->  Prop;
    conf_finite : finite_inc C;
    conf_closed : @dw_closed _ ord C;
    conf_noconflict : forall e e', C e -> C e' -> not (conflict e e')
  }.


Definition justifies `{ES:EventStructure} (x:configuration) (e:A):=
  not (C e) /\ is_configuration (fun f => f = e \/ C f).


Class Game  :=
  {
    ES:EventStructure;
    polarity : A -> player
  }.



Definition minGame :
  forall (G:Game) (a:@A (@ES G)), Prop:=
  fun G a => forall a',  ord a' a -> a' = a.

Definition polGame :
  forall (G:Game) (a:@A (@ES G)), player :=
  fun G a => polarity a.

Definition resEvent :
  forall (G:Game) (a:@A (@ES G)), Set :=
fun G a =>  { b : @A (@ES G) | not (b = a) /\ not (conflict b a)}.

Definition resOrd :
  forall (G:Game) (a:@A (@ES G)), resEvent G a-> resEvent G a-> Prop.
Proof.
  intros G a (b,_) (c,_).
  exact (ord b c).
Defined.

Definition resConflict :
  forall (G:Game) (a:@A (@ES G)), resEvent G a-> resEvent G a-> Prop.
Proof.
  intros G a (b,_) (c,_).
  exact (conflict b c).
Defined.

Definition resPolarity :
  forall (G:Game) (a:@A (@ES G)), resEvent G a -> player.
Proof.
  intros G a (b,_).
  exact (polarity b).
Defined.


Program Definition resES :
  forall (G:Game) (a:@A (@ES G)), EventStructure:=
  fun G a => 
    @Build_EventStructure (resEvent G a) (@resOrd G a) (@resConflict G a ) _ _ _ _ _ _.
Next Obligation.
  destruct e. simpl.
  apply ord_refl.
Qed.
Next Obligation.
  destruct e,f.
  simpl in *.
  apply (@ord_antisym _ _ _ H0 ) in H ;subst.
  
(* UIP *)
Admitted.
Next Obligation.
  destruct e,f,g.
  simpl in *.
  now apply ord_trans with x0.
Qed.  
Next Obligation.
  destruct e;simpl.
  apply conf_irrefl.
Qed.
Next Obligation.
Admitted.
Next Obligation.
  destruct e1,e2,e2';simpl in *.
  now apply vendetta with x0.
Qed.


Definition residual :
  forall (G:Game) (a:@A (@ES G)), Game
  := fun G a=> @Build_Game (resES G a) (@resPolarity G a).


Definition proj_res :
  forall (G:Game) (a:@A (@ES G)), (@A (@ES (residual G a))) -> (@A (@ES G)).
Proof.
  intros G a (e,_).
  exact e.
Defined.

(* Coercion proj_res (G:Game) (a:@A (@ES G)): *)
(*   (@A (@ES (residual G a))) >-> (@A (@ES G)). *)

Definition neg `{G:Game} (a:@A (@ES G)):= polarity a = O.

Definition pos `{G:Game} (a:@A (@ES G)):= polarity a = P.

Inductive O_play `{G:Game}:=
| nilO : O_play
| consO : forall (a:@A (@ES G)), minGame G a -> neg a -> @P_play (residual G a) -> O_play
with P_play `{G:Game}:=
(* | nil_P : P_play *)
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


Fixpoint list_play `{G:Game} (s:O_play): list A :=
  match s with
  | nilO => nil
  | @consO _ a mina nega s' => (List.map (@proj_res G a) (list_Pplay s')) · a
  end
with list_Pplay `{G:Game} (s:P_play): list A :=
  match s with
   | @consP _ a mina nega s' => (List.map (@proj_res G a) (list_play s')) · a
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


(* définition par fixpoint vers Bool + reflection *)

(* Sanity check avec list préfixe *)


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

(* 
Sanity check:
1) reflexif
2) lien avec determinisme + liste extraite 

*)


(* Definition receptive  `{G:Game} (S:list E -> Prop):= *)
(*   forall a s,  S s -> polarity a = O -> is_Match (s·a) -> S (s·a). *)

(* codée en dur vu qu'on ne considère que des O-plays, donc de longueur paire *)


Class strategy `{G:Game} :=
  {
    S: O_play -> Prop;
    S_nonempty : S nilO;
    S_closed : prefixO_closed S;
    S_det : forall s s', S s  -> S s' -> coherentO s s';
  }.


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


(* exercice + sanity check*)


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


(* Todo list *)

(*
- coherent2 (mm chose)
-> strategy2

- restriction 


*)

Definition restriction_lm `{A:Game} `{B:Game} `{C:Game} :
  forall (i:@OOO_int A B C), @O_play2 A B.
Admitted.

Definition restriction_mr `{A:Game} `{B:Game} `{C:Game} :
  forall (i:@OOO_int A B C), @O_play2 B C.
Admitted.

Definition restriction_lr `{A:Game} `{B:Game} `{C:Game} :
  forall (i:@OOO_int A B C), @O_play2 A C.
Admitted.




(* 
τ : strat2 A B

σ : strat2 B C

*)


(* définition par fixpoint vers Bool + reflection *)

(* Sanity check avec list préfixe *)

