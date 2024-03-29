Require Export List.
Require Export Setoid.

Set Implicit Arguments.

Section Single.

Variable (a : Set).
Variable (aeq : relation a).
Variable (aeqEquiv : Equivalence aeq).

Definition opaque (s t:Set) seq teq (f:s -> t) := 
  forall x y, seq x y -> teq (f x) (f y).

CoInductive braun : Set :=
| bons : a -> braun -> braun -> braun.

(* Bisimilarity is the equivalence relation we will want on braun streams *)

CoInductive coeq : braun -> braun -> Prop :=
| coeqc : forall x y 
             od od' 
             ev ev', 
      aeq x y -> 
      coeq od od' -> 
      coeq ev ev' 
      -> coeq (bons x od ev) 
              (bons y od' ev').

Lemma coeqRefl : forall x, coeq x x.
Proof.
  cofix.
  intros x.
  destruct x.
  apply coeqc.
  apply aeqEquiv.
  apply coeqRefl.
  apply coeqRefl.
Qed.

Print coeqRefl.

Lemma coeqSymm : forall x y, coeq x y -> coeq y x.
Proof.
  cofix.
  intros x y coeq_x_y.
  destruct coeq_x_y.
  apply coeqc.
  apply aeqEquiv. apply H.
  apply coeqSymm. assumption.
  apply coeqSymm. assumption.
Qed.

Lemma coeqTrans : forall x y z , coeq x y -> coeq y z -> coeq x z.
Proof.
  cofix.
  intros x y z coeq_x_y coeq_y_z.
  inversion coeq_x_y as [xh  yh xod  yod xev  yev].
  inversion coeq_y_z as [yh' zh yod' zod yev' zev yzh yzod yzev yy].
  subst.
  inversion yy. subst. clear yy.
  constructor.
  setoid_transitivity yh; assumption.
  apply coeqTrans with yod; assumption.
  apply coeqTrans with yev; assumption.
Qed.

Global Instance coeqEquiv : @Equivalence braun coeq := 
{
 Equivalence_Reflexive := coeqRefl;
 Equivalence_Symmetric := coeqSymm;
 Equivalence_Transitive := coeqTrans 
}.
(*
Add Parametric Relation : braun coeq
reflexivity proved by coeqRefl
symmetry proved by coeqSymm
transitivity proved by coeqTrans
as coeqEquiv.
*)
(* An equivalent definition of braun streams: *)

(* Extensional function quality is an equivalence relation: *)

Section Double.

Variable (b:Set).
Variable (beq : relation b).
Variable (beqEquiv : Equivalence beq).

Locate " _ --> _ ".


Definition exteq (f:b -> a) (g:b -> a) := 
  forall x y, 
    beq x y -> 
    opaque beq aeq f -> 
    opaque beq aeq g -> 
    aeq (f x) (g y).

Hint Unfold exteq.

Lemma exteqRefl : forall f, exteq f f.
Proof.
  auto.
Qed.
Require Import Coq.Classes.SetoidClass.
Lemma exteqSymm : forall f g, exteq f g -> exteq g f.
Proof.
  unfold exteq; intros f g fg x y xy geq feq.
  symmetry. apply fg; auto.
  symmetry. assumption.
Qed.

Lemma exteqTrans : forall f g h, 
  opaque beq aeq g ->
  exteq f g -> 
  exteq g h -> 
  exteq f h.
Proof.
  unfold exteq. intros f g h OG fg gh x y xy feq heq.
  transitivity (g x).
  apply fg; auto.
  reflexivity.
  apply gh; auto.
Qed.
(*
Add Parametric Relation : (b->a) exteq
reflexivity proved by exteqRefl
symmetry proved by exteqSymm
transitivity proved by exteqTrans
as exteq_equiv.
*)
End Double.

Hint Unfold exteq.

Ltac des :=
  intros; simpl in *;
  match goal with
    | [H:Equivalence ?S |- _] => inversion_clear H; auto; des
    | [a:bool |- _] => destruct a; auto; des
    | [ |- coeq (bons _ _ _) (bons _ _ _)] => constructor; auto; des
    | [_:_=_ |- _] => subst; auto
    | [xy : coeq ?x ?y |- _] => inversion_clear xy; auto
    | _ => auto
  end.

(* A little trick from http://adam.chlipala.net/cpdt/
This function is useful for proofs.
 *)

Definition frob (x : braun) : braun :=
match x with
| bons h od ev => bons h od ev
end.

Lemma frobeq : forall (x:braun), x = frob x.
Proof.
  destruct x. simpl. reflexivity.
Defined.

(* like braunFraun, fraunBraun takes entensionally equivalent functions to bisimilar streams *)

Print Equivalence.

Lemma opaqueEq : 
  forall (s t:Set) teq (f:s->t), 
    Reflexive teq -> 
    opaque eq teq f.
Proof.
  clear; unfold Reflexive, opaque; intros.
  subst; auto.
Qed.

(* ord converts locations in braun streams to natural numbers *)

Fixpoint ord (x : list bool) : nat :=
match x with
  | nil => 0
  | (true :: r) => 1 + 2 * (ord r)
  | (false :: r) => 2 + 2 * (ord r)
end.

(* The usual record selectors: *)

Definition bead (x : braun) :=
match x with 
| bons h _ _ => h
end.

Definition bodds (x : braun) :=
match x with 
| bons _ od _ => od
end.

Definition bevens (x : braun) :=
match x with 
| bons _ _ ev => ev
end.

Add Parametric Morphism : bead with
  signature 
  coeq ==> aeq as beadMorph.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Add Parametric Morphism : bodds with
  signature 
  coeq ==> coeq as oddsMorph.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Add Parametric Morphism : bevens with
  signature 
  coeq ==> coeq as evensMorph.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.


(* And fmap as in Haskell's Functor class *)


CoFixpoint fmap f (x:braun) : braun :=
match x with
| bons h od ev => bons (f h) (fmap f od) (fmap f ev)
end.

Lemma fmapMorph : 
  forall f g,
    opaque aeq aeq f ->
    opaque aeq aeq g ->
    exteq aeq f g ->
    forall x y,
      coeq x y ->
      coeq (fmap f x)
           (fmap g y).
Proof.
  cofix.
  intros.
  destruct x; destruct y; simpl.
  rewrite (frobeq (fmap f _)).
  rewrite (frobeq (fmap g _)). 
  simpl.
  inversion H0; subst.
  constructor.
  apply H; assumption.
  apply fmapMorph; assumption.
  apply fmapMorph; assumption.
Qed.


Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.

Require Import Coq.omega.Omega.


(*

The proof will need induction on the depth of the elements in the streams. The function bat (binary at) translates between coequality and extensional equality.

*)

Fixpoint bat (x:braun) (b:list bool) {struct b} : a :=
  match x with
    | bons h o e =>
      match b with
        | nil => h
        | true  :: r => bat o r
        | false :: r => bat e r
      end
  end.

Lemma batCoeq : forall x y,
  (forall b, aeq (bat x b) (bat y b)) -> coeq x y.
Proof.
  cofix; intros.
  destruct x; destruct y; constructor.
  apply (H nil).
  apply batCoeq. intros. apply (H (true::b)).
  apply batCoeq. intros. apply (H (false::b)).
Qed.

Add Parametric Morphism : bat with
  signature coeq ==> (@eq (list bool)) ==> (aeq) as batMorph.
Proof.
  intros ? ? ? b; 
    generalize dependent x;
      generalize dependent y;
        induction b; intros ? ? xy;
          destruct x; destruct y; 
            inversion xy; subst.

  simpl. assumption.

  destruct a0; apply IHb; assumption.
Qed.


Lemma fmapbat : forall f b x,
  bat (fmap f x) b = f (bat x b).
Proof.
  clear; induction b; destruct x; auto.
  destruct a0; simpl; auto.
Qed.

Require Import Arith.

Fixpoint evenp (n:nat) : nat+nat :=
  match n with
    | 0 => inl 0
    | 1 => inr 0
    | S (S m) => 
      match evenp m with
        | inl a => inl (S a)
        | inr a => inr (S a)
      end
  end.

Lemma evenis : let P n :=
  match evenp n with
    | inl x => x+x = n
    | inr x => 1+x+x = n
  end
  in forall n, P n.
Proof.
  clear.
  intros.
  apply lt_wf_ind.
  intros.
  unfold P in *.
  clear P.
  destruct n0.
  simpl; auto.
  simpl.
  destruct n0.
  auto.
  remember (evenp n0) as en.
  destruct en.
  assert (n1+n1 = n0).
  assert (match evenp n0 with
            | inl z => z + z = n0
            | inr z => 1 + z + z = n0
          end).
  apply H.
  auto.
  rewrite <- Heqen in H0.
  auto.
  auto with arith.
  omega.
  assert (match evenp n0 with
            | inl z => z + z = n0
            | inr z => 1 + z + z = n0
          end).
  apply H.
  auto.
  rewrite <- Heqen in H0.
  omega.
Qed.

Lemma evenleft : forall n x, 
  evenp n = inl x -> x+x = n.
Proof.
  clear.
  intros.
  assert (match evenp n with
            | inl x => x+x = n
            | inr x => 1+x+x = n
          end).
  apply evenis.
  rewrite H in H0. auto.
Qed.

Lemma evenright : forall n x, 
    evenp n = inr x -> 1+x+x = n.
Proof.
  clear.
  intros.
  assert (match evenp n with
            | inl x => x+x = n
            | inr x => 1+x+x = n
          end).
  apply evenis.
  rewrite H in H0. auto.
Qed.

Function unord (x:nat) {measure id x} : list bool :=
  match x with
    | 0 => nil
    | S y => 
      match evenp y with
        | inl a => true :: unord a
        | inr a => false :: unord a
      end
  end.
clear; intros.
unfold id.
induction y.
simpl in teq0.
inversion teq0.
auto.
simpl in teq0.
clear IHy.
destruct y.
inversion teq0.
remember (evenp y) as ey.
destruct ey.
Check evenleft.
inversion teq0.
subst.
clear teq0.
Check evenleft.
assert (n+n=y).
apply evenleft. auto.
omega.
inversion teq0.
intros.
unfold id.
subst.
assert (1 + a0 + a0 = y).
apply evenright.
auto.
omega.
Defined.

Lemma eventwo : forall x, evenp (x+x) = inl x.
Proof.
  clear.
  induction x.
  auto.
  remember (S x + S x) as y.
  assert (y = S (S (x+x))).
  omega.
  subst.
  rewrite H.
  unfold evenp.
  simpl.
  fold (evenp (x + x)).
  rewrite IHx.
  reflexivity.
Qed.

Lemma eventhree : forall x, evenp (S (x+x)) = inr x.
Proof.
  clear.
  induction x.
  auto.
  remember (S (S x + S x)) as y.
  assert (y = S (S (S (x+x)))).
  omega.
  subst.
  rewrite H.
  unfold evenp.
  simpl.
  fold (evenp (S (x + x))).
  rewrite IHx.
  reflexivity.
Qed.

Lemma unt : forall x, unord (ord x) = x.
Proof.
  clear.
  induction x.
  auto.
  destruct a.
  simpl.
  assert (forall y, y + y = y + (y + 0)).
  intros.
  omega.
  rewrite <- H.
  simpl.
  rewrite unord_equation.
  rewrite eventwo.
  f_equal. auto.
  simpl.
  assert (forall y, y + y = y + (y + 0)).
  intros.
  omega.
  rewrite <- H.
  rewrite unord_equation.
  rewrite eventhree.
  f_equal. auto.
Qed.

Lemma tun : let P x := ord (unord x) = x in 
  forall x, P x.
Proof.
  clear.
  intros.
  apply lt_wf_ind.
  intros.
  unfold P in *.
  clear P.
  destruct n.
  auto.
  rewrite unord_equation.
  remember (evenp n) as en.
  destruct en.
  simpl.
  rewrite H.
  f_equal.
  transitivity (n0 + n0).
  omega.
  apply evenleft. auto.
  Check evenleft.
  assert (n0 + n0 = n).
  apply evenleft.
  auto.
  omega.
  simpl.
  f_equal.
  rewrite H.
  transitivity (S (n0 + n0)).
  auto with arith.
  transitivity (1 + n0 + n0).
  auto with arith.
  apply evenright.
  auto.
  assert (1 + n0 + n0 = n).
  apply evenright. auto.
  omega.
Qed.


Ltac num :=
  des; autorewrite with bord in *; try omega; auto.

(* twiceT n is 2*n *)
(*

From the FAQ:

137  Is there an axiom-free proof of Streicher's axiom K for the equality on nat?
Yes, because equality is decidable on nat. Here is the proof.
*)
Require Import Eqdep_dec.
Require Import Peano_dec.

Theorem K_nat :
   forall (x:nat) (P:x = x -> Prop), P (@refl_equal nat x) -> forall p:x = x, P p.
Proof.
  intros; apply K_dec_set with (p := p).
  apply eq_nat_dec.
  assumption.
Qed.

(*
Similarly, we have
*)

Theorem eq_rect_eq_nat :
  forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
  intros; apply K_nat with (p := h); reflexivity.
Qed.

(*

138  How to prove that two proofs of n<=m on nat are equal?
This is provable without requiring any axiom because axiom K directly holds on nat. Here is a proof using question 137.

*)

Require Import Arith.

Scheme le_ind' := Induction for le Sort Prop.

Theorem le_uniqueness_proof : forall (n m : nat) (p q : n <= m), p = q.
Proof.
  induction p using le_ind'; intro q.
  replace (le_n n) with
   (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (@refl_equal nat n)).
  2:reflexivity.
  generalize (@refl_equal nat n).
     pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (le_Sn_n m); rewrite <- e; assumption.
  replace (le_S n m p) with
   (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (@refl_equal nat (S m))).
  2:reflexivity.
   generalize (@refl_equal nat (S m)).
     pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
      contradiction (le_Sn_n m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
       rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
       rewrite (IHp l0); reflexivity.
Qed.

End Single.