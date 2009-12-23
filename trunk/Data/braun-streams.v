Require Import List.
Require Import Setoid.

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
  proof.
    given x : braun.
    per cases on x.
    suppose it is (bons h o e).
    suffices to have 
      c:(aeq h h)
      ,l:(coeq o o)
      ,r:(coeq e e) 
      to show thesis 
      by (coeqc c l r).
      
    focus on (aeq h h).
      thus thesis by aeqEquiv.
    end focus.

    focus on (coeq o o).
      thus thesis by coeqRefl.
    end focus.

    focus on (coeq e e).
      thus thesis by coeqRefl.
    end focus.
  end cases.
  end proof.
Qed.

Lemma coeqSymm : forall x y, coeq x y -> coeq y x.
Proof.
  cofix.
    proof.
      given x:braun, y:braun, coeq_x_y:(coeq x y).
      per cases on coeq_x_y.
      suppose it is (coeqc xh yh xo yo xe ye heq oeq eeq).
      suffices to have 
        c:(aeq yh xh)
        ,l:(coeq yo xo)
        ,r:(coeq ye xe) 
      to show thesis by (coeqc c l r).

      focus on (aeq yh xh).
        thus thesis by heq, aeqEquiv.
      end focus.

      focus on (coeq yo xo).
        thus thesis by oeq, coeqSymm.
      end focus.
  
      focus on (coeq ye xe).
        thus thesis by eeq, coeqSymm.
      end focus.
    end cases.
  end proof.
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

Add Parametric Relation : braun coeq
reflexivity proved by coeqRefl
symmetry proved by coeqSymm
transitivity proved by coeqTrans
as coeqEquiv.

(* An equivalent definition of braun streams: *)

Definition fraun := list bool -> a.

(* Extensional function quality is an equivalence relation: *)

Section Double.

Variable (b:Set).
Variable (beq : relation b).
Variable (beqEquiv : Equivalence beq).

Locate " _ --> _ ".
Print respectful.

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
  unfold exteq; intros f g h OG fg gh x y xy feq heq.
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

(* braunFraun turns bisimilar Braun streams into extensionally equal frauns *)

Add Parametric Morphism : braunFraun with
  signature coeq ==> (@exteq (list bool) (@eq (list bool))) as braunFraunMorph.
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
  
Add Parametric Morphism : fraunBraun with
  signature (@exteq (list bool) (@eq (list bool))) ==> coeq 
  as fraunBraunMorph.
Proof.
  unfold exteq, opaque.
  cofix.
  intros x y xy.
  rewrite (frobeq (_ x)).
  rewrite (frobeq (_ y)).
  simpl.
  constructor.
  apply xy; try (apply opaqueEq; apply aeqEquiv); reflexivity.
  apply fraunBraunMorph_Morphism. intros; subst.
  apply xy; try (intros; subst; reflexivity); try auto.
  apply fraunBraunMorph_Morphism. intros; subst.
  apply xy; try (intros; subst; reflexivity); try auto.
Qed.

(* braunFraun and fraunBraun are inverses: *)

Lemma fraunBack : forall x y, exteq eq x y -> exteq eq (braunFraun (fraunBraun x)) y.
Proof.
  unfold exteq, opaque.
  assert (forall n x y, exteq eq x y -> aeq (braunFraun (fraunBraun x) n) (y n)).
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

Definition fead (x:fraun) := x nil.

Definition bodds (x : braun) :=
match x with 
| bons _ od _ => od
end.

Definition fodds (x : fraun) (n : list bool) := x (true :: n).

Definition bevens (x : braun) :=
match x with 
| bons _ _ ev => ev
end.

Definition fevens (x : fraun) (n : list bool) := x (false :: n).

(* And fmap as in Haskell's Functor class *)


CoFixpoint fmap f (x:braun) : braun :=
match x with
| bons h od ev => bons (f h) (fmap f od) (fmap f ev)
end.

Definition ffmap f (x : fraun) (n : list bool) : a :=
f (x n).

Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Recdef.

Require Import Coq.omega.Omega.


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

(*

From the FAQ:

137  Is there an axiom-free proof of Streicher's axiom K for the equality on nat?
Yes, because equality is decidable on nat. Here is the proof.
*)
Require Import Eqdep_dec.
Require Import Peano_dec.

Theorem K_nat :
   forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
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
   (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).
  2:reflexivity.
  generalize (refl_equal n).
     pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
      rewrite <- eq_rect_eq_nat; trivial.
      contradiction (le_Sn_n m); rewrite <- e; assumption.
  replace (le_S n m p) with
   (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
  2:reflexivity.
   generalize (refl_equal (S m)).
     pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
      contradiction (le_Sn_n m); rewrite Heq; assumption.
      injection HeqS; intro Heq; generalize l HeqS.
       rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
       rewrite (IHp l0); reflexivity.
Qed.

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
  coeq (fraunBraun f) (fraunBraun g) <-> exteq eq f g.
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
  rewrite (frobeq (_ g)).
  rewrite (frobeq (_ f)).
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