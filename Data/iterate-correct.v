Set Implicit Arguments.

Require Import Setoid.
Require Import List.
Require Import Coq.Init.Wf.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.

Section type.

Variable A:Set.
Variable (Aeq : relation A).
Variable (Aeq_equiv : Equivalence Aeq).

CoInductive Braun : Set :=
| Conb : A -> Braun -> Braun -> Braun.

(*

It is often impossible to prove inductive equality for coinductive objects like Braun streams, even when every element is the same. Instead, coequality (bisumulation?) is often used.

*)

CoInductive coeq : Braun -> Braun -> Prop :=
| co : forall x y od od' ev ev',
        (Aeq x y) -> coeq od od' -> coeq ev ev'
        -> coeq (Conb x od ev) (Conb y od' ev').

(*

Here begins the definition of the algorithm.

*)

(*
Definition map := {F : A -> A | forall x y, Aeq x y -> Aeq (F x) (F y)}.
Program Definition ap (F:map) (x:A) : A :=
  F x.
Print ap.
*)

Definition fmorph f := forall x y, Aeq x y -> Aeq (f x) (f y).

Hint Unfold fmorph.

CoFixpoint fmap F (x:Braun) : Braun :=
  match x with
    | Conb h od ev => Conb (F h) (fmap F od) (fmap F ev) 
  end.


Definition frob (x : Braun) : Braun :=
match x with
| Conb h od ev => Conb h od ev
end.

Lemma frobeq : forall (x:Braun), x = frob x.
Proof.
  destruct x. simpl. reflexivity.
Defined.

Definition aext f g :=
  forall x y,
    Aeq x y ->
    Aeq (f x) (g y).

Lemma fmapMorph :
  forall f g x y,
    aext f g->
    coeq x y ->
    coeq (fmap f x) (fmap g y).
Proof.
  cofix.
  destruct x; destruct y;
    simpl;
      unfold aext; intros.
  rewrite (frobeq (fmap f _)).
  rewrite (frobeq (fmap g _)). 
  simpl.
  inversion H0; subst.
  constructor.
  apply H; apply H5.
  apply fmapMorph. exact H. exact H8.
  apply fmapMorph. exact H. exact H9.
Qed.

(*
  Conb 
  (match x with | Conb h _ _ => F h end)
  (match x with | Conb _ o _ => fmap F o end)
  (match x with | Conb _ _ e => fmap F e end).
*)
(*
CoFixpoint oddFromEven F (x:A) (b:Braun) : Braun :=
  match b with
    | Conb h od ev => Conb x (oddFromEven F (F h) ev) (fmap F od)
  end.
*)


Definition odds (x:Braun) :=
  match x with
    | Conb _ od _ => od
  end.

Definition evens (x:Braun) :=
  match x with
    | Conb _ _ ev => ev
  end.

Definition bead (x:Braun) :=
  match x with
    | Conb h _ _ => h
  end.

Add Parametric Morphism : bead with
  signature 
  coeq ==> Aeq as beadMor.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Add Parametric Morphism : odds with
  signature 
  coeq ==> coeq as oddsMor.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Add Parametric Morphism : evens with
  signature 
  coeq ==> coeq as evensMor.
Proof.
  intros.
  destruct x; destruct y.
  simpl.
  inversion H. assumption.
Qed.

Variable oddFromEven : (A->A) -> A -> Braun -> Braun.
Variable oddFromUnfold :
  forall F x b,
    coeq (oddFromEven F x b) 
    (Conb x (oddFromEven F (F (bead b)) (evens b)) (fmap F (odds b))).
Variable oddFromMorph :
  forall f g x y v w,
    aext f g ->
    Aeq x y ->
    coeq v w ->
    coeq (oddFromEven f x v) 
         (oddFromEven g y w).

(*
  Conb x 
  (match b with 
     | Conb h _ ev => oddFromEven F (F h) ev
   end)
  (match b with 
     | Conb _ od _ => fmap F od
   end).
*)
(*

It is difficult to define 'od' in such a way that Coq can see that it is productive. By making it a variable to this section, that problem can be solved in a separate module.

*)
(*
Fact od : (A -> A) -> A -> Braun
with ev : (A -> A) -> A -> Braun.
*)
Variable od : (A -> A) -> A -> Braun.
Variable ev : (A -> A) -> A -> Braun.

Variable odMorph :
  forall f g x y,
    aext f g ->
    Aeq x y ->
    coeq (od f x) (od g y).
Variable evMorph :
  forall f g x y,
    aext f g ->
    Aeq x y ->
    coeq (ev f x) (ev g y).
    
Variable odUnfold : forall F (x:A), 
  coeq (od F x) (oddFromEven F (F x) (ev F x)).
Variable evUnfold : forall F x,
  coeq (ev F x) (fmap F (od F x)).

Definition iterate F (x:A) : Braun :=
  Conb x (od F x) (ev F x).

Add Parametric Morphism : iterate with
  signature aext ==> Aeq ==> coeq as iterateMorph.
Proof.
  cofix.
  unfold aext in *; 
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

data Braun a = Conb a (Braun a) (Braun a)
instance Functor Braun where
    fmap f (Conb h od ev) = Conb (f h) (fmap f od) (fmap f ev)
oddFromEven f x (Conb h od ev) = 
   Conb x (oddFromEven f (f h) ev) (fmap f od)
iterate f x = Conb x od ev
    where
      od = oddFromEven f (f x) ev
      ev = fmap f od

The claim is that 

iterate f x = iterateSlow f x

where

iterateSlow f x = 
    Conb x (iterateSlow g y)
           (iterateSlow g (f y))
    where
      y = f x
      g = f . f

Because f (f x) will be used in both branches of the stream, it should be shared. iterateSlow does not share it, and so will do unnecessary work. For instance, forcing the second element (counting from 0) will calculate the zeroth element of iterateSlow g (f y), f y = f (f x). Forcing the third element of iterateSlow f x will calculate the first element of iterateSlow g y, which is the zeroth element of iterateSlow (g . g) (g y): g y = (f . f) (f x) = f (f (f x)).

iterate does not do any of that extra work. Its algorithmic efficiency is not proved in this module. Its equivalence to iterateSlow *is* shown.

*)

(*

The proof will need induction on the depth of the elements in the streams. The function bat (binary at) translates between coequality and extensional equality.

*)

Fixpoint bat (x:Braun) (b:list bool) {struct b} : A :=
  match x with
    | Conb h o e =>
      match b with
        | nil => h
        | true  :: r => bat o r
        | false :: r => bat e r
      end
  end.

Lemma batcoeq : forall x y,
  (forall b, Aeq (bat x b) (bat y b)) -> coeq x y.
Proof.
  cofix; intros.
  destruct x; destruct y; constructor.
  apply (H nil).
  apply batcoeq. intros. apply (H (true::b)).
  apply batcoeq. intros. apply (H (false::b)).
Qed.

Add Parametric Morphism : bat with
  signature coeq ==> (@eq (list bool)) ==> (Aeq) as batmor.
Proof.
  intros ? ? ? b; 
    generalize dependent x;
      generalize dependent y;
        induction b; intros ? ? xy;
          destruct x; destruct y; 
            inversion xy; subst.

  simpl. assumption.

  destruct a; apply IHb; assumption.
Qed.

Check batmor.

Hint Rewrite odUnfold using batmor_Morphism : core.

(*

The proof will also need induction on the position of elements in the streams. The function ord translates from lists of booleans, used as stream indexes by bat, into natural numbers.

*)

Fixpoint ord (x:list bool) : nat :=
  match x with
    | nil => 0
    | true::r  => 1 + 2*(ord r)
    | false::r => 2 + 2*(ord r)
  end.

Hint Unfold ord.

Fixpoint applyn (n:nat) (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | S m => f (applyn m f x)
  end.

Add Parametric Morphism : applyn with
  signature (@eq nat) ==> aext ==> aext as applynMorph.
Proof.
  unfold aext in *;
    induction y;
      intros.
  simpl. assumption.
  simpl.
  apply H.
  apply IHy.
  assumption. assumption.
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

Lemma fmapbat : forall f b x,
  bat (fmap f x) b = f (bat x b).
Proof.
  clear; induction b; destruct x; auto.
  destruct a; simpl; auto.
Qed.

Hint Rewrite fmapbat : core.
Hint Resolve fmapbat.

(*

even = iterate (f^(2^k)) (f^(2^(k+1) - 2) x)
f^(2^k)^j f^(2^(k+1)-2) x = e @ j

oddFromEven f (f^(2^k-1) x) e @ b =  f^(2^k)^b f^(2^k-1) x
oddFromEven f (f^(2^k-1) x) even = iterate f^(2^k) (f^(2^k-1) x)

*)


Lemma coeq_refl : forall x, coeq x x.
Proof.
  cofix.
  destruct x. 
  constructor.
  setoid_reflexivity.
  apply coeq_refl.
  apply coeq_refl.
Qed.

Lemma coeq_symm : forall x y, coeq x y -> coeq y x.
Proof.
  cofix.
  intros x y coeq_x_y.
  destruct coeq_x_y.
  constructor. 
  setoid_symmetry. assumption.
  apply coeq_symm. assumption.
  apply coeq_symm. assumption.
Qed.

Lemma coeq_trans : forall x y z , coeq x y -> coeq y z -> coeq x z.
Proof.
  cofix.
  intros x y z coeq_x_y coeq_y_z.
  inversion coeq_x_y as [xh  yh xod  yod xev  yev].
  inversion coeq_y_z as [yh' zh yod' zod yev' zev yzh yzod yzev yy].
  subst.
  inversion yy. subst. clear yy.
  constructor.
  setoid_transitivity yh; assumption.
  apply coeq_trans with yod; assumption.
  apply coeq_trans with yev; assumption.
Qed.

Add Parametric Relation : Braun coeq
reflexivity proved by coeq_refl
symmetry proved by coeq_symm
transitivity proved by coeq_trans
as coeq_equiv.
(*
Lemma eqco :
  forall x,
    coeq x x.
Proof.
  cofix.
  intros; destruct x; constructor.
  reflexivity.
  apply eqco.
  apply eqco.
Qed.
*)
Lemma mainLemma :
  forall b e x f k,
    aext f f ->
    (forall j, ord j < ord b ->
      Aeq (bat e j)
      (applyn (ord j)
      (applyn (pow 2 k) f) 
      (applyn ((pow 2 (k+1)) - 2) f x))) ->
    Aeq (bat (oddFromEven f 
      (applyn ((pow 2 k) - 1) f x) e) b) (
    applyn (ord b)
    (applyn (pow 2 k) f) 
    (applyn ((pow 2 k) - 1) f x)).
Proof.
  (* We prove this by induction on b. *)

  induction b; destruct e as [hd odd even]; intros. 

  (* The nil case is trivial. *)

  erewrite oddFromUnfold.
  reflexivity.

  pose (oddFromEven f (applyn (pow 2 k - 1) f x) (Conb hd odd even)) as oo.
  assert (coeq oo (oddFromEven f (applyn (pow 2 k - 1) f x) (Conb hd odd even))) as ooo.
  reflexivity.
  rewrite oddFromUnfold in ooo.
  fold oo.
  rewrite ooo.
(*  unfold oo in ooo.*)
  destruct a; simpl.

  (* For the odd branch *)

  transitivity
    (bat (oddFromEven f (applyn (pow 2 (S k) - 1) f x) even) b); auto.
  transitivity 
    (bat (oddFromEven f (applyn (S (pow 2 (S k) - 2)) f x) even) b); auto.
  repeat (repeat (apply batmor); unfold applyn).
  fold (applyn (pow 2 (S k) - 2) f x).
  apply oddFromMorph.
  assumption. apply H.
  assert (forall k, S k = k + 1) as sk.
  intros; omega.
  rewrite <- sk in H0.  
  apply H0 with (j := nil).
  simpl; omega. reflexivity. reflexivity.
  apply batmor.
  apply oddFromMorph.
  assumption.
  apply applynMorph. 
  Lemma helppow : forall k, S (pow 2 (S k) - 2) = pow 2 (S k) - 1.
  Proof.
    clear.
    induction k.
    unfold pow. omega.
    unfold pow; fold (pow 2 (S k)).
    simpl. simpl in IHk.
    omega.
  Qed.
  apply helppow.
  assumption. reflexivity. reflexivity. reflexivity.

  rewrite IHb.

  autorewrite with arith.
  apply applynMorph.
  unfold pow; fold (pow 2 k).
  simpl.
  repeat (rewrite mult_plus_distr_r).
  repeat (rewrite mult_plus_distr_l).
  omega. assumption.   reflexivity. assumption.

  intros.
  transitivity (bat (Conb hd odd even) (false::j)); auto.
  unfold bat at 2. fold (bat even j). reflexivity.
  rewrite H0.
  autorewrite with arith.
  apply applynMorph.
  unfold ord; fold (ord j). simpl.
  assert (forall k, S k = k + 1) as sk.
  intros; omega.
  rewrite <- sk.
  
  unfold pow; fold (pow 2 k).
  simpl. 
  repeat (rewrite mult_plus_distr_l).
  repeat (rewrite mult_plus_distr_r).
  simpl. omega. assumption. reflexivity.
  
  unfold ord; fold (ord j); fold (ord b).
  omega.

  rewrite fmapbat.

  transitivity (applyn 1 f (bat (Conb hd odd even) (true::b))); auto.
  unfold applyn. apply H. auto.
  unfold bat at 2; fold (bat odd b).
  reflexivity.

  transitivity (applyn 1 f ((applyn (ord (true::b)) (applyn (pow 2 k) f) (applyn (pow 2 (S k) - 2) f x)))).
  apply applynMorph. reflexivity. assumption.
  assert (forall k, S k = k + 1) as sk.
  intros; omega.
  rewrite <- sk in H0.

  apply H0. unfold ord; fold (ord b); omega.

  autorewrite with arith.
  apply applynMorph.
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
  destruct km; simpl; omega. assumption. reflexivity.
Qed.

Lemma iter :
  let P b := forall f x, aext f f -> Aeq (bat (iterate f x) b) (applyn (ord b) f x)
    in forall b, P b.
Proof.
  intro P.
  (* We proceed by induction on the number of othe position in the stream: (ord b) *)

  eapply (well_founded_ind bwf).
  intros b IH.
  unfold P in *.
  intros.
  (* If b is the head element, the proof is trivial. Otherwise, name the head of b "a" and the tail of b "b" *)
  destruct b as [|a b]; auto.
  simpl. reflexivity.

  (*
     Most of the work is done in this helper lemma:

  *)

  assert 
    (Aeq (bat (oddFromEven f (f x) (ev f x)) b)
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

CoFixpoint iterateSlow F (x:A) : Braun :=
  let g := fun z => F (F z) in
    let y := F x in
      Conb x (iterateSlow g y)
             (iterateSlow g (F y)).
(*
Lemma applyCommut :
  forall f g,
    (forall y, f (g y) = g (f y)) ->
    forall x n, f (applyn n g x) = applyn n g (f x).
Proof.
  intros.
  generalize dependent x.
  generalize dependent H.
  generalize dependent f.
  generalize dependent g.
  induction n.
  simpl. auto.
  simpl.
  intros.
  transitivity (f (applyn n g (g x))).
  f_equal.
  apply IHn. auto.
  transitivity (applyn n g (f (g x))).
  apply IHn. apply H.
  transitivity (applyn n g (g (f x))).
  rewrite H. auto.
  rewrite IHn; auto.
Qed.
*)

Lemma iterSlow :
  let P b := forall f x, aext f f -> Aeq (bat (iterateSlow f x) b) (applyn (ord b) f x)
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
  unfold aext in *.
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
  unfold aext in *; intros.
  apply H; apply H; assumption.
Qed.

Lemma iterSame :
  forall f x, aext f f -> coeq (iterateSlow f x) (iterate f x).
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
