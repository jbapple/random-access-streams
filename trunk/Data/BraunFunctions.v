Require Import BraunStreams.
Require Import List.
Require Import Setoid.

Set Implicit Arguments.

Section Single.

Variable (a : Set).
Variable (aeq : relation a).
Variable (aeqEquiv : Equivalence aeq).

Definition braun := braun a.
Definition coeq := coeq aeq.

(* An equivalent definition of braun streams: *)

Definition fraun := list bool -> a.

(* Extensional function quality is an equivalence relation: *)

Hint Unfold exteq.

(* braunFraun converts Braun streams to their functional dopplegangers, Frauns *)

Fixpoint braunFraun (x : braun) (n : list bool) {struct n} : a :=
match x with
| bons h od ev =>
  match n with
    | nil => h
    | true ::r => braunFraun od r
    | false::r => braunFraun ev r
  end
end.

(* braunFraun turns bisimilar Braun streams into extensionally equal frauns *)


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


Add Parametric Morphism : braunFraun with
  signature coeq ==> (@exteq _ aeq _ eq) as braunFraunMorph.
Proof.
  assert (forall n x y, coeq x y -> aeq (braunFraun x n) (braunFraun y n)).
  induction n; des.
  unfold exteq. intros. subst. auto.
Qed.

(* fraunBraun undoes the conversion, turning frauns into Braun streams *)

CoFixpoint fraunBraun (x : fraun) : braun :=
bons (x nil) (fraunBraun (fun y => x (cons true y)))
             (fraunBraun (fun y => x (cons false y))).

(* A little trick from http://adam.chlipala.net/cpdt/
This function is useful for proofs.
 *)
  
Add Parametric Morphism : fraunBraun with
  signature (@exteq _ aeq _ eq) ==> coeq 
  as fraunBraunMorph.
Proof.
  unfold exteq, opaque.
  cofix.
  intros x y xy.
  rewrite (frobeq (fraunBraun x)).
  rewrite (frobeq (fraunBraun y)).
  simpl.
  constructor.
  apply xy; try (apply opaqueEq; apply aeqEquiv); reflexivity.
  apply fraunBraunMorph_Morphism. intros; subst.
  apply xy; try (intros; subst; reflexivity); try auto.
  apply fraunBraunMorph_Morphism. intros; subst.
  apply xy; try (intros; subst; reflexivity); try auto.
Qed.

(* braunFraun and fraunBraun are inverses: *)

Lemma fraunBack : forall x y, exteq aeq eq x y -> exteq aeq eq (braunFraun (fraunBraun x)) y.
Proof.
  unfold exteq, opaque.
  assert (forall n x y, exteq aeq eq x y -> aeq (braunFraun (fraunBraun x) n) (y n)).
  unfold exteq, opaque.
  induction n; des. apply H; auto; intros; des.  
  apply IHn with (y := fun z => y (true::z)); des.
  apply H; auto; intros; des.
  apply IHn with (y := fun z => y (false::z)). des.
  apply H; auto; intros; des.
  des.
Qed.

Lemma braunBack : forall x y, coeq x y -> coeq (fraunBraun (braunFraun x)) y.
Proof.
  Lemma braunBack' : 
    forall x y, coeq x y -> coeq (fraunBraun (fun v => braunFraun x v)) y.
  Proof.
    cofix.
    intros.
    rewrite (frobeq (fraunBraun (fun v => braunFraun x v))).
    simpl.
    destruct y. simpl.
    destruct x. simpl. 
    inversion H. subst.
    constructor.

    assumption.
    apply braunBack'. assumption.
    apply braunBack'. assumption.
  Qed.
  Show.
  intros.
  rewrite fraunBraunMorph_Morphism.
  apply braunBack' with (x := x).
  assumption.
  unfold exteq, opaque. des.
Qed.

(* The usual record selectors: *)

Definition fead (x:fraun) := x nil.

Definition fodds (x : fraun) (n : list bool) := x (true :: n).

Definition fevens (x : fraun) (n : list bool) := x (false :: n).

(* And fmap as in Haskell's Functor class *)

Definition ffmap f (x : fraun) (n : list bool) : a :=
f (x n).

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.

Require Import Coq.omega.Omega.


(*

The proof will need induction on the depth of the elements in the streams. The function bat (binary at) translates between coequality and extensional equality.

*)

Require Import Arith.

(* succT n is one more than n *)

Fixpoint succT (n:list bool) : list bool :=
match n with
| nil => true :: nil
| true ::r => false::r
| false::r => true::(succT r)
end.

Lemma succTisS : forall n, ord (succT n) = S (ord n).
Proof.
  induction n; des. omega.
Defined.

Hint Rewrite succTisS : bord.

Ltac num :=
  des; autorewrite with bord in *; try omega; auto.

(* twiceT n is 2*n *)

Fixpoint twiceT (n:list bool) : list bool :=
match n with
| nil => nil
| true::r => false::(twiceT r)
| false::r => false::(succT (twiceT r))
end.

Lemma twice : forall n, ord (twiceT n) = 2*(ord n).
Proof.
  induction n; num.
Qed. 

Hint Rewrite twice : bord.

Definition predT (n:list bool) : list bool :=
  match n with 
    | nil => nil
    | true::r => twiceT r
    | false::r => true::r
  end.

Lemma succPred : 
  forall x, x <> nil -> succT (predT x) = x.
Proof.
  intros; destruct x.
  destruct H. auto.
  destruct b; simpl.
  rewrite <- (@unt (succT (twiceT x))).
  num. simpl.
  rewrite <- unt.
  simpl. auto. auto.
Qed.

Hint Rewrite succPred : bord.

Lemma allEq :
  forall x y,
    (forall b, aeq (braunFraun x b) (braunFraun y b)) ->
    coeq x y.
Proof.
  cofix.
  intros.
  destruct x; destruct y.
  constructor.
  pose (H nil) as heq.
  simpl in heq.
  apply heq.
  apply allEq.
  intros r; pose (H (true::r)) as leq.
  simpl in leq. apply leq.
  apply allEq.
  intros r; pose (H (false::r)) as leq.
  simpl in leq. apply leq.
Qed.

Lemma coext : forall f g,
  coeq (fraunBraun f) (fraunBraun g) <-> exteq aeq eq f g.
Proof.
  unfold exteq, opaque.
  split.
  intros fg x y xy ff gg; subst.
  generalize dependent f. generalize dependent g.
  induction y; intros;
    rewrite frobeq in fg;
      simpl in fg;
        replace (fraunBraun f) with (frob (fraunBraun f)) in fg;
          simpl in fg;
            inversion fg; subst; auto.
  destruct a0.
  eapply IHy with (f := fun y => f (true:: y)) (g := fun y => g (true:: y)); des.
  eapply IHy with (f := fun y => f (false:: y)) (g := fun y => g (false:: y)); des.
  
  generalize dependent f; generalize dependent g.
  cofix.
  intros; subst.
  rewrite (frobeq (fraunBraun g)).
  rewrite (frobeq (fraunBraun f)).
  simpl.
  constructor.
  apply H; des.
  eapply coext with (f := fun y => f (true:: y)) (g := fun y => g (true:: y)).
  intros; subst. apply H; des.
  eapply coext with (f := fun y => f (false:: y)) (g := fun y => g (false:: y)).
  intros; subst. apply H; des.
Qed.

Lemma fmapCommute : forall f x, coeq (fmap f (fraunBraun x)) (fraunBraun (ffmap f x)).
Proof.
  cofix.
  intros.
  rewrite (frobeq (fmap _ _)).
  rewrite (frobeq (fraunBraun (ffmap _ _))).
  simpl.
  constructor.
  unfold ffmap.
  reflexivity.
  apply fmapCommute.
  apply fmapCommute.
Qed.

End Single.