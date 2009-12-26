Set Implicit Arguments.

Require Import Setoid.
Require Import List.
Require Import Coq.Init.Wf.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.

Section type.

Variable a:Set.
Variable (aeq : relation a).
Variable (aeqEquiv : Equivalence aeq).

Require Import BraunStreams.

Definition braun := braun a.
Definition coeq := coeq aeq.
Definition exteq := @exteq a aeq a aeq.

Variable oddFromEven : (a->a) -> a -> braun -> braun.
Variable oddFromUnfold :
  forall f x b,
    coeq (oddFromEven f x b) 
    (bons x (oddFromEven f (f (bead b)) (bevens b)) (fmap f (bodds b))).
Variable oddFromMorph :
  forall f g x y v w,
    exteq f g ->
    aeq x y ->
    coeq v w ->
    coeq (oddFromEven f x v) 
         (oddFromEven g y w).
(*

It is difficult to define 'od' in such a way that Coq can see that it is productive. By making it a variable to this section, that problem can be solved in a separate module.

*)

Variable od : (a -> a) -> a -> braun.
Variable ev : (a -> a) -> a -> braun.

Variable odMorph :
  forall f g x y,
    exteq f g ->
    aeq x y ->
    coeq (od f x) (od g y).
Variable evMorph :
  forall f g x y,
    exteq f g ->
    aeq x y ->
    coeq (ev f x) (ev g y).
    
Variable odUnfold : forall f (x:a), 
  coeq (od f x) (oddFromEven f (f x) (ev f x)).
Variable evUnfold : forall f x,
  coeq (ev f x) (fmap f (od f x)).

Definition iterate f (x:a) : braun :=
  bons x (od f x) (ev f x).

Add Parametric Morphism : iterate with
  signature exteq ==> aeq ==> coeq as iterateMorph.
Proof.
  cofix.
  unfold exteq in *; 
    unfold iterate in *; 
      intros.
  constructor.
  assumption.
  apply odMorph.
  assumption.
  assumption.
  apply evMorph.
  assumption.
  assumption.
Qed.

(*

The Haskell definition of all of the above is:

data braun a = bons a (braun a) (braun a)
instance Functor braun where
    fmap f (bons h od ev) = bons (f h) (fmap f od) (fmap f ev)
oddFromEven f x (bons h od ev) = 
   bons x (oddFromEven f (f h) ev) (fmap f od)
iterate f x = bons x od ev
    where
      od = oddFromEven f (f x) ev
      ev = fmap f od

The claim is that 

iterate f x = iterateSlow f x

where

iterateSlow f x = 
    bons x (iterateSlow g y)
           (iterateSlow g (f y))
    where
      y = f x
      g = f . f

Because f (f x) will be used in both branches of the stream, it should be shared. iterateSlow does not share it, and so will do unnecessary work. For instance, forcing the second element (counting from 0) will calculate the zeroth element of iterateSlow g (f y), f y = f (f x). Forcing the third element of iterateSlow f x will calculate the first element of iterateSlow g y, which is the zeroth element of iterateSlow (g . g) (g y): g y = (f . f) (f x) = f (f (f x)).

iterate does not do any of that extra work. Its algorithmic efficiency is not proved in this module. Its equivalence to iterateSlow *is* shown.

*)

Hint Rewrite odUnfold using batMorph_Morphism : core.

Hint Unfold ord.

Fixpoint applyn (n:nat) (f:a->a) (x:a) : a :=
  match n with
    | 0 => x
    | S m => f (applyn m f x)
  end.

Lemma applynOpaque :
  forall n f, 
    opaque aeq aeq f -> 
    opaque aeq aeq (applyn n f).
Proof.
  unfold opaque; induction n; simpl; intros.
  assumption.
  apply H; apply IHn.
  assumption. assumption.
Qed.

Lemma applynMorph :
  forall n m f g,
    opaque aeq aeq f ->
    opaque aeq aeq g ->
    exteq f g ->
    n = m ->
    exteq (applyn n f) (applyn m g).
Proof.
  induction n; intros; subst.
  simpl. apply exteqRefl.
  simpl.
  unfold exteq in H |- *.
  unfold BraunStreams.exteq in H |- *.
  intros; apply H.
  unfold exteq in IHn.
  unfold BraunStreams.exteq in IHn.
  apply IHn.
  assumption.
  assumption.
  assumption. reflexivity.
  assumption.
  apply applynOpaque.
  assumption.
  apply applynOpaque.
  assumption.
  assumption.
  assumption.
Qed. 

Hint Unfold applyn.

Definition bacc x y := ord x < ord y.

Hint Unfold bacc.

Lemma bwf : well_founded bacc.
Proof.
  apply well_founded_ltof.
Qed.

Fixpoint pow x y :=
  match y with
    | 0 => 1
    | (S n) => x * (pow x n)
  end.

Lemma applyAdd :
  forall f n m x,
    applyn n f (applyn m f x) =
    applyn (n+m) f x.
Proof.
  intros f n; 
    generalize dependent f;
      induction n; intros.
  auto.
  simpl. f_equal. apply IHn.
Qed.

Hint Rewrite applyAdd : arith.

Hint Resolve applyAdd.

Lemma applyMul :
  forall f n m x,
    applyn n (applyn m f) x =
    applyn (n*m) f x.
Proof.
  intros f n; 
    generalize dependent f;
      induction n; intros.
  auto.
  simpl.
  rewrite <- applyAdd.
  f_equal.
  apply IHn.
Qed.

Hint Rewrite applyMul : arith.
Hint Resolve applyMul.

Hint Rewrite fmapbat : core.
Hint Resolve fmapbat.

(*

even = iterate (f^(2^k)) (f^(2^(k+1) - 2) x)
f^(2^k)^j f^(2^(k+1)-2) x = e @ j

oddFromEven f (f^(2^k-1) x) e @ b =  f^(2^k)^b f^(2^k-1) x
oddFromEven f (f^(2^k-1) x) even = iterate f^(2^k) (f^(2^k-1) x)

*)



Lemma mainLemma :
  forall b e x f k,
(*    exteq f f -> *)
    opaque aeq aeq f ->
    (forall j, ord j < ord b ->
      aeq (bat e j)
      (applyn (ord j)
      (applyn (pow 2 k) f) 
      (applyn ((pow 2 (k+1)) - 2) f x))) ->
    aeq (bat (oddFromEven f 
      (applyn ((pow 2 k) - 1) f x) e) b) (
    applyn (ord b)
    (applyn (pow 2 k) f) 
    (applyn ((pow 2 k) - 1) f x)).
Proof.

  (* We prove this by induction on b. *)

  induction b; destruct e as [hd odd even]; intros; unfold opaque in *.

  (* The nil case is trivial. *)

  rewrite batMorph.
  Focus 2.
  apply oddFromUnfold.
  Focus 2. reflexivity.
  reflexivity.

  pose (oddFromEven f (applyn (pow 2 k - 1) f x) (bons hd odd even)) as oo.
  assert (coeq oo (oddFromEven f (applyn (pow 2 k - 1) f x) (bons hd odd even))) as ooo.
  reflexivity.
  rewrite oddFromUnfold in ooo.
  fold oo.
  rewrite batMorph.
  Focus 2. apply ooo.
  Focus 2. reflexivity.

(*  unfold oo in ooo.*)
  destruct a0; simpl.

  (* For the odd branch *)


  assert (exteq f f) as E.
  unfold exteq; unfold BraunStreams.exteq.
  intros; apply X; auto.

  transitivity
    (bat (oddFromEven f (applyn (pow 2 (S k) - 1) f x) even) b); auto.
  transitivity 
    (bat (oddFromEven f (applyn (S (pow 2 (S k) - 2)) f x) even) b); auto.
  repeat (repeat (apply batmor); unfold applyn).
  fold (applyn (pow 2 (S k) - 2) f x).
  Check batMorph.
  apply batMorph with (aeq := aeq).
  apply oddFromMorph; auto.
  assert (forall k, S k = k + 1) as sk.
  intros; omega.
  rewrite <- sk in H.  
  apply X.
  apply H with (j := nil).
  simpl; omega. reflexivity. auto.
  apply batMorph with (aeq := aeq).
  apply oddFromMorph.
  unfold exteq; unfold BraunStreams.exteq.
  intros; apply X; auto.
  apply applynMorph; auto.
  Lemma helppow : forall k, S (pow 2 (S k) - 2) = pow 2 (S k) - 1.
  Proof.
    clear.
    induction k.
    unfold pow. omega.
    unfold pow; fold (pow 2 (S k)).
    simpl. simpl in IHk.
    omega.
  Qed.
  Show.
  rewrite helppow; auto.
  reflexivity.
  apply applynOpaque; auto.
  apply applynOpaque; auto.
  reflexivity.
  auto.

  rewrite IHb.

  autorewrite with arith.
  apply applynMorph; auto.

  unfold pow; fold (pow 2 k).
  simpl.
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_plus_distr_l).
  omega; auto.  reflexivity. 
  apply applynOpaque; auto.
  apply applynOpaque; auto.
  auto. 

  intros.
  transitivity (bat (bons hd odd even) (false::j)); auto.
  unfold bat at 2. fold (bat even j). reflexivity.
  rewrite H.
  autorewrite with arith.
  apply applynMorph; try reflexivity; auto.
  
  unfold ord; fold (ord j). simpl.
  assert (forall k, S k = k + 1) as sk.
  intros; omega.
  rewrite <- sk.
  
  unfold pow; fold (pow 2 k).
  simpl. 
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  simpl. omega; auto; try reflexivity; try (apply applynOpaque). 
  apply applynOpaque; auto; try reflexivity.
  apply applynOpaque; auto; try reflexivity.
  
  unfold ord; fold (ord j); fold (ord b).
  omega.

  
  assert (exteq f f) as E.
  unfold exteq; unfold BraunStreams.exteq.
  intros; apply X; auto.

  rewrite fmapbat.

  transitivity (applyn 1 f (bat (bons hd odd even) (true::b))); auto.
  unfold applyn. apply X; auto.
  unfold bat at 2; fold (bat odd b).
  reflexivity.

  transitivity (applyn 1 f ((applyn (ord (true::b)) (applyn (pow 2 k) f) (applyn (pow 2 (S k) - 2) f x)))).
  apply applynMorph; try reflexivity; try assumption; auto.
  assert (forall k, S k = k + 1) as sk.
  intros; omega.
  rewrite <- sk in H.

  apply H. unfold ord; fold (ord b); omega.

  autorewrite with arith.
  apply applynMorph; try reflexivity; try (apply applynMorph); auto.
(*
  rewrite H.
  clear.
  autorewrite with arith.
  f_equal.
  *)
  unfold ord; fold (ord b).
  simpl. 
  
  assert (S (pow 2 k - 1) = pow 2 k). 
  clear.
  induction k. simpl. reflexivity.
  simpl.
  rewrite <- IHk.
  omega.
  remember (pow 2 k - 1) as km.
  destruct km; simpl; omega. 
  apply applynOpaque; try reflexivity; try assumption; auto.
  apply applynOpaque; try reflexivity; try assumption; auto.
Qed.

Lemma iter :
  let P b := forall f x, exteq f f -> aeq (bat (iterate f x) b) (applyn (ord b) f x)
    in forall b, P b.
Proof.
  intro P.
  (* We proceed by induction on the number of othe position in the stream: (ord b) *)

  eapply (well_founded_ind bwf).
  intros b IH.
  unfold P in *.
  intros.
  (* If b is the head element, the proof is trivial. Otherwise, name the head of b "a" and the tail of b "b" *)
  destruct b as [|z b]; auto.
  simpl. reflexivity.

  (*
     Most of the work is done in this helper lemma:

  *)

  assert 
    (aeq (bat (oddFromEven f (f x) (ev f x)) b)
      (f (applyn (ord b + (ord b + 0)) f x))) as help.

  (* 2^1-1 = 1 *)

  replace (f x) with (applyn (pow 2 1 - 1) f x); auto.
  (* We can now apply the long, main lemma we proved above. *)
  rewrite mainLemma.
  (* Some simple arithmetic proves the required equality for the application of mainLemma *)
  transitivity (applyn 1 f (applyn (ord b + (ord b + 0)) f x)); auto.
  repeat (repeat (rewrite applyMul); repeat (rewrite applyAdd)).
  apply applynMorph. simpl; omega. assumption.  reflexivity.
  reflexivity. assumption.

  (* For the condition on mainLemma, first change the sequence we bat to iterate f x, rather than ev f x *)
  intros.
  transitivity
    (bat (iterate f x) (false::j)); auto.
  unfold iterate. simpl. reflexivity.
  (* Then apply the induction hypothesis *)
  rewrite IH.
  (* The equality now follows with some arithmetic *)
  repeat (rewrite applyMul); repeat (rewrite applyAdd).
  apply applynMorph.
  unfold ord; fold (ord j). simpl; omega. assumption. reflexivity.

  (* The condition of the induction hypothesis follows by arithemtic and a simple case analysis on b and j *)

  unfold bacc; unfold ord; fold (ord b); fold (ord j). 
  destruct a; omega. assumption.

  (*
     End proof of helper lemma.
  *)

  (* Now a is either true or false, corresponding to either the odd or the even branch, respectively. *)

  destruct a; simpl.
  (* In the odd branch, once we unfold odd, we can apply the helper lemma. *)

  rewrite odUnfold; apply help.

  (* We will transform the even branch into an instance of the odd branch. ev unfolds to fmap od. *) 
  rewrite evUnfold.
  (* The commutator of bat and fmap f is f *)
  rewrite fmapbat. apply H.

  (* Now this is just the odd case from above *)
  rewrite odUnfold. apply help.
Qed.

CoFixpoint iterateSlow f (x:a) : braun :=
  let g := fun z => f (f z) in
    let y := f x in
      bons x (iterateSlow g y)
             (iterateSlow g (f y)).

Lemma iterSlow :
  let P b := forall f x, exteq f f -> aeq (bat (iterateSlow f x) b) (applyn (ord b) f x)
    in forall b, P b.
Proof.
  intro P.
  induction b.
  unfold P; intros; auto.
  simpl. reflexivity.
  destruct a; unfold P in *; intros.
  transitivity (bat (iterateSlow (fun z => f (f z)) (f x)) b).
  simpl. reflexivity.
  rewrite IHb.
  simpl ord.
  transitivity (applyn (ord b) (applyn 2 f) (f x)).
  simpl. reflexivity.
  rewrite applyMul.
  repeat (rewrite <- mult_n_Sm).
  rewrite <- mult_n_O.
  simpl.
  transitivity (applyn (ord b + ord b) f (applyn 1 f x)).
  reflexivity.
  rewrite applyAdd.
  transitivity (applyn 1 f (applyn (ord b + ord b) f x)).
  rewrite applyAdd. apply applynMorph. auto with arith.
  
  simpl. assumption. reflexivity. simpl.
  apply H. apply applynMorph. auto. assumption. reflexivity.
  unfold exteq in *.
  intros.
  apply H. apply H. assumption.

  simpl.
  rewrite IHb.
  transitivity (applyn (ord b) (applyn 2 f) (f (f x))).
  simpl. reflexivity.
  rewrite applyMul.
  repeat (rewrite <- mult_n_Sm).
  rewrite <- mult_n_O.
  simpl.
  transitivity (applyn (ord b + ord b) f (applyn 2 f x)).
  reflexivity.
  rewrite applyAdd. 
  transitivity (applyn 2 f (applyn (ord b + ord b) f x)).
  rewrite applyAdd. apply applynMorph. auto with arith.
  assumption. reflexivity.
  simpl. repeat (apply H). apply applynMorph. auto.
  assumption.
  reflexivity.
  unfold exteq in *; intros.
  apply H; apply H; assumption.
Qed.

Lemma iterSame :
  forall f x, exteq f f -> coeq (iterateSlow f x) (iterate f x).
Proof.
  intros.
  apply batcoeq.
  intros.
  transitivity (applyn (ord b) f x).
  Check iterSlow.
  pose iterSlow as p.
  simpl in p.
  apply p. assumption.
  pose iter as p.
  simpl in p.
  symmetry.
  apply p.
  assumption.
Qed.

End type.
