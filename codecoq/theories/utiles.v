Definition refl_restr `{A: Type} (B: A->Prop) (ord: A->A->Prop) :=
  forall e, B e -> ord e e.

Definition antisym_restr `{A :Type} (B: A->Prop) (ord: A->A->Prop) :=
  forall e f, B e->B f-> ord e f -> ord f e -> e = f.

Definition transitif_restr `{A: Type} (B: A->Prop) (ord: A->A->Prop) :=
  forall e f g, B e-> B f-> B g-> ord e f -> ord f g -> ord e g.

Definition ordonned_restr `{A: Type} (B: A->Prop) (ord: A->A->Prop) :=
  refl_restr B ord /\ antisym_restr B ord /\ transitif_restr B ord.

Definition injection_restr  `{A: Type} (B: A->Prop) (f : A -> nat) :=
  forall a a', B a /\ B a'-> f a = f a' -> a = a'.

Definition fun_bounded_restr `{A: Type} (B: A->Prop) (f: A->nat) :=
  exists n, forall a, B a -> f a <= n.

(**
un ensemble $B$ est fini si et seulement si il existe f
injective : B -> nat qui est bornée.
 *)
Definition ens_fini_restr `{A: Type} (B: A->Prop) :=
  exists (f: A->nat), injection_restr B f /\ fun_bounded_restr B f.

(**
f injective => toute restriction de f est injective
*)
Lemma inject_restr_implic :
  forall A f (B:A->Prop) (B':A->Prop),
    (forall a:A, B' a -> B a) -> (injection_restr B f -> injection_restr B' f) .
Proof.
  intros A f B B' B'incB injf a a' (adansB',a'dansB') faeqfa'.
  apply injf. split; apply B'incB ;[apply adansB'|apply a'dansB'].
  apply faeqfa'.
Qed.

(**
f bornée => toute restriction de f est bornée
 *)
Lemma borned_restr_implic :
  forall A f (B:A->Prop) (B':A->Prop),
    (forall a:A, B' a -> B a) -> (fun_bounded_restr B f -> fun_bounded_restr B' f).
Proof.
  intros A f B B' B'incB fB_bound.
  destruct fB_bound as (n, nbornef).
  exists n. intros a adansB'; apply nbornef;apply (B'incB a); apply adansB'.
Qed.
