Set Implicit Arguments.

Require Import Setoid.
Require Import List.
Require Import Coq.Init.Wf.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Coq.Program.Equality.

Section type.

Variable A:Set.

CoInductive Braun : Set :=
| Conb : A -> Braun -> Braun -> Braun.

CoInductive coeq : Braun -> Braun -> Prop :=
| co : forall x y od od' ev ev',
        (x = y) -> coeq od od' -> coeq ev ev'
        -> coeq (Conb x od ev) (Conb y od' ev').

CoFixpoint fmap F (x:Braun) : Braun :=
match x with
  | Conb h od ev => Conb (F h) (fmap F od) (fmap F ev) 
end.

CoFixpoint oddFromEven F (x:A) (b:Braun) : Braun :=
match b with
  | Conb h od ev => Conb x (oddFromEven F (F h) ev) (fmap F od)
end.

Variable od : (A->A) -> A -> Braun.

Definition ev F (x:A) :=
  fmap F (od F x).

Variable odeq : forall F (x:A), 
  coeq (od F x) (oddFromEven F (F x) (ev F x)).

Definition iterate F (x:A) : Braun :=
  Conb x (od F x) (ev F x).

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
  (forall b, bat x b = bat y b) -> coeq x y.
Proof.
  cofix; intros.
  destruct x; destruct y; constructor.
  apply (H nil).
  apply batcoeq. intros. apply (H (true::b)).
  apply batcoeq. intros. apply (H (false::b)).
Qed.


Add Parametric Morphism : bat with
  signature coeq ==> (@eq (list bool)) ==> (@eq A) as batmor.
Proof.
  intros ? ? ? b; 
    generalize dependent x;
      generalize dependent y;
        induction b; intros ? ? xy;
          destruct x; destruct y; 
            inversion xy; subst.

  reflexivity.

  destruct a; apply IHb; assumption.
Qed.

Check batmor_Morphism.

Fixpoint ord (x:list bool) : nat :=
  match x with
    | nil => 0
    | true::r  => 1 + 2*(ord r)
    | false::r => 2 + 2*(ord r)
  end.

Fixpoint applyn (n:nat) (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | S m => f (applyn m f x)
  end.
(*
Fixpoint applyn' (n:nat) (f:A->A) (x:A) : A :=
  match n with
    | 0 => x
    | S m => applyn' m f (f x)
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

Definition bacc x y := ord x < ord y.
Lemma bwf : well_founded bacc.
Proof.
  apply well_founded_ltof.
Qed.

Fixpoint pow x y :=
  match y with
    | 0 => 1
    | (S n) => x * (pow x n)
  end.

Lemma subHelp :
  forall x y, S x >= S y -> x >= y.
Proof.
  intros; omega.
Qed.


Function sub (x:nat) (y:nat)  {struct x} : (x >= y) -> nat :=
  match x return (x >= y) -> nat with
    | S n => 
      match y return (S n >= y) -> nat with
        | 0 => fun _ => x
        | S m => fun (p:S n >= S m) => @sub n m (subHelp p)
      end
    | 0 => fun _ => 0
  end.

Lemma subeq : forall p q p' q' r s, 
  p = p' -> q = q' -> @sub p q r = @sub p' q' s.
Proof.
  dependent induction p.
  intros. subst.
  assert (q' = 0). inversion r. auto. subst. auto.
  dependent induction q.
  intros. subst.
  reflexivity.
  intros. subst.
  unfold sub.
  fold (sub (subHelp r)).
  fold (sub (subHelp s)).
  apply IHp; reflexivity.
Defined.

Print sub.

(*
Definition sub (x:nat) (y:nat) (p: x >= y) : nat.
refine (fix ss x y p :=
  match (x,y) as xy with
    | (S n,0) => S n
    | (S n,S m) => @ss n m (subHelp _)
    | (0,_) => 0
  end).



Program Fixpoint sub x y (p: x >= y) :=
  match (x,y) with
    | (S n,0) => S n
    | (S n,S m) => @sub n m _
    | (0,0) => 0
    | (0,S m) => _
  end.
Next Obligation.
  omega.
Qed.
*)

(*
Lemma eviter :
  forall f b it x,
    (forall n, bacc n b -> bat it n = applyn (ord n) f x) ->
      forall n, ord n <= ord b -> 
        bat (evens it) n = applyn (2*(ord n)+2) f x.
Proof.
  intros.
  destruct it. simpl.
  destruct 
*)



Definition half (x:list bool) :=
  match x with
    | nil => nil
    | _ :: y => y
  end.

Lemma dec1pow :
  forall k, pow 2 k >= 1.
Proof.
  induction k; simpl; omega.
Defined.

Lemma dec2pow :
  forall k, pow 2 (S k) >= 2.
Proof.
  induction k; simpl.
  auto.
  simpl in IHk. omega.
Defined.

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

Lemma applyMul :
  forall f n m x,
    applyn n (applyn m f) x =
    applyn (n*m) f x.
Proof.
  intros f n; 
    generalize dependent f;
      induction n; intros.
  auto.
  simpl. rewrite IHn. apply applyAdd.
Qed.

Lemma subPlus : forall ab a b c c' p q, 
  ab = a+b -> c = c' -> 
  @sub ab c p = a + @sub b c' q.
Proof.
  assert (forall a b c p q, 
    @sub (a+b) c p = a + @sub b c q).
  Focus 2.
  intros; subst. apply H.
  clear.
  dependent induction a.
  simpl. intros. apply subeq; reflexivity.
  dependent induction b.
  rewrite plus_0_r.
  intros.
  assert (c = 0).
  inversion q. reflexivity.
  subst. unfold sub. omega.
  dependent induction c.
  intros. 
  reflexivity.
  intros. 
  simpl in p.
  unfold sub.
  simpl.
  fold (sub (subHelp p)).
  fold (sub (subHelp q)).
  rewrite plus_Snm_nSm in IHb. apply IHb.
Qed.

Lemma subOne : forall a b p q,
      S (@sub a (S b) p) = @sub a b q.
Proof.
  clear.
  
  dependent induction a.
  intros.
  inversion p.
  dependent induction b.
  intros.
  unfold sub.
  fold (@sub a 0 (subHelp p)).
  f_equal.
  destruct a; reflexivity.
  intros.
  unfold sub.
  fold (sub (subHelp p)).
  fold (sub (subHelp q)).
  f_equal.
  apply IHa.
Qed.



Lemma mainLemma :
  forall b e x f k,
    (forall j, ord j < ord b ->
      bat e j = 
      applyn (ord j)
      (applyn (pow 2 k) f) 
      (applyn (sub (*(pow 2 (k+1)) 2*) (dec2pow k)) f x)) ->
    bat (oddFromEven f 
      (applyn (sub (*(pow 2 k) 1*) (dec1pow k)) f x) e) b =
    applyn (ord b)
    (applyn (pow 2 k) f) 
    (applyn (sub (*(pow 2 k) 1*) (dec1pow k)) f x).
Proof.
  induction b; destruct e; intros.

  reflexivity.

  destruct a; simpl.
  assert (a0 = applyn (sub (dec2pow k)) f x).
  apply (@H nil). unfold ord. omega.
  assert (f a0 = applyn (sub (dec1pow (S k))) f x).
  subst. 
  assert (S (sub (dec2pow k)) = sub (dec1pow (S k))).
  Focus 2.
  rewrite <- H0.
  reflexivity.
  Focus 2.
  rewrite H1.
  rewrite IHb.
  Focus 2.
  intros.
  clear IHb.
  transitivity (bat (Conb a0 e1 e2) (false :: j)).
  Focus 2.
  rewrite H.
  Focus 2.
  unfold ord. fold (ord j). fold (ord b). omega.
  Focus 5.
  transitivity (f (bat e1 b)).
  Focus 2.
  transitivity (f (bat (Conb a0 e1 e2) (true::b))).
  Focus 2.
  rewrite H.
  Unfocus.
  Focus 8.
  unfold ord. omega.
  Focus 3.
  reflexivity.
  Focus 4.
  clear H IHb.
  generalize dependent e1.
  induction b; destruct e1.
  reflexivity.
  destruct a.
  simpl. apply IHb.
  simpl. apply IHb.
  Focus 4.
  reflexivity.
  Focus 2.
  rewrite applyMul.
  rewrite applyAdd.
  rewrite applyMul.
  rewrite applyAdd.
  rewrite applyAdd.
  f_equal.
  Unfocus.
  Focus 3.
  rewrite applyMul.
  rewrite applyAdd.
  rewrite applyMul.
  rewrite applyAdd.
  f_equal.
  Unfocus.
  Focus 4.
  rewrite applyAdd.
  rewrite applyMul.
  rewrite applyAdd.
  rewrite applyMul.
  rewrite applyAdd.
  rewrite applyAdd.
  transitivity 
    (applyn (S (ord (true :: b) * pow 2 k + sub (dec2pow k))) f x).
  reflexivity.
  f_equal.
  Unfocus.


  apply subOne.
  

  clear.
  remember (ord b) as c. clear b Heqc.
  replace ((c + (c + 0))* pow 2 k) with (c * pow 2 (S k)).
  Focus 2.
  unfold pow at 1. fold (pow 2 k).
  assert (forall x y, x * (2 * y) = (x + (x + 0)) * y).
  intros.

  simpl. simpl.
  rewrite mult_plus_distr_r.
  simpl.
  rewrite plus_0_r.
  rewrite plus_0_r.
  rewrite mult_plus_distr_l.
  reflexivity.
  apply H.


  replace (sub (dec1pow (S k))) with (pow 2 k + sub (dec1pow k)).
  Focus 2.
  assert (pow 2 k + pow 2 k = pow 2 (S k)).
  replace (pow 2 k + pow 2 k) with (2 * pow 2 k).
  unfold pow at 1. reflexivity.
  omega.
  assert (pow 2 k + pow 2 k >= 1).
  rewrite H.
  apply (dec1pow (S k)).
  Check subPlus.
  rewrite <- (@subPlus (pow 2 k + pow 2 k) _ _ 1 _ H0).
  apply subeq. assumption. reflexivity.
  reflexivity. reflexivity.
  omega.


  clear.
  unfold ord at 1. fold (ord j).
  remember (ord j) as x. clear Heqx j.
  rewrite mult_plus_distr_r.
  replace (2 * pow 2 k) with (pow 2 (S k)).
  replace (2 * x * pow 2 k) with (x * pow 2 (S k)).
  replace (sub (dec2pow (S k))) with (pow 2 (S k) + sub (dec2pow k)).
  omega.

  assert (pow 2 (S k) + pow 2 (S k) >= 2).
  assert (pow 2 (S k) + pow 2 (S k) = pow 2 (S (S k))).
  replace (pow 2 (S k) + pow 2 (S k)) with (2 * pow 2 (S k)).
  unfold pow at 1. reflexivity.
  omega.
  assert (pow 2 (S k) + pow 2 (S k) >= 2).
  rewrite H.
  apply (dec2pow (S k)). auto.

  rewrite <- (@subPlus (pow 2 (S k) + pow 2 (S k)) _ _ 2 _ H).
  apply subeq.
  unfold pow.
  fold (pow 2 k). omega. reflexivity.
  reflexivity.
  reflexivity.
  unfold pow. fold (pow 2 k).
  symmetry.
  rewrite mult_comm.
  rewrite mult_assoc. rewrite <- mult_comm. 
  f_equal.
  omega.
  unfold pow.
  fold (pow 2 k). reflexivity.
  
  clear.

  unfold ord.
  fold (ord b).
  remember (ord b) as g.
  clear Heqg b.
  simpl.
  remember (g + (g + 0)) as h.
  clear Heqh g.
  remember (h * pow 2 k) as g.
  clear Heqg h.

  assert (S (sub (dec2pow k)) = pow 2 k + sub (dec1pow k)).
  Focus 2.
  assert (forall a b c, S (a + b + c) = S c + (a + b)).
  intros. omega.
  rewrite H0.
  replace (S (sub (dec2pow k))) with (pow 2 k + sub (dec1pow k)).
  assert (forall a b c, a + a + b + c = (a + c) + (a + b)).
  intros. omega.
  rewrite H1.
  rewrite <- H. reflexivity.
  Unfocus.
  Check subOne.
  rewrite (@subOne (pow 2 (S k)) 1 (dec2pow k) (dec1pow (S k))).
  Check subPlus.
  erewrite (@subPlus (pow 2 (S k)) (pow 2 k) (pow 2 k) 1 1).
  reflexivity.
  unfold pow. fold (pow 2 k). omega.
  reflexivity.
Qed.

Check mainLemma.


Lemma iter :
  let P b := forall f x, bat (iterate f x) b = applyn (ord b) f x
    in forall b, P b.
Proof.
  intro P.
  apply (@well_founded_ind (list bool) bacc bwf).
  intros b IH.
  unfold P.
  intros.
  destruct b as [|a b].

  reflexivity.

(*  assert (bat (iterate f x) (a :: b) = applyn (ord (false :: b)) f x)*)

  destruct a.
  simpl.
  rewrite odeq.
  
  Focus 2.
  simpl.
  unfold ev.
  transitivity (f (bat (od f x) b)).
  Focus 2.
  f_equal.
  rewrite odeq.
  Check mainLemma.
  transitivity 
    (bat (oddFromEven f (applyn (sub (dec1pow 1)) f x) (ev f x)) b).
  unfold applyn.
  simpl. reflexivity.
  erewrite mainLemma.
  transitivity (applyn (S (ord b + ord b)) f x).
  rewrite applyMul.
  rewrite applyAdd.
  f_equal. simpl. Focus 2.
  simpl. 
  f_equal.
  f_equal.
  omega.
  Focus 4.
  intros.
  transitivity (bat (iterate f x) (false::j)).
  unfold bat. reflexivity.
  erewrite IH.
  rewrite applyMul.
  rewrite applyAdd.
  f_equal.
  simpl.
  Focus 2.
  simpl. unfold bacc.
  simpl. omega.







  transitivity
    (bat (oddFromEven f (applyn (sub (dec1pow 1)) f x) (ev f x)) b).
  reflexivity.
  rewrite mainLemma.
  rewrite applyMul.
  rewrite applyAdd.
  transitivity (applyn (S (ord b + (ord b + 0))) f x).
  f_equal. simpl.
  Focus 2.
  unfold applyn at 1.
  f_equal.
  Focus 2.
  intros.
  transitivity (bat (iterate f x) (false::j)).
  reflexivity.
  rewrite IH.
  rewrite applyMul.
  rewrite applyAdd.
  f_equal.
  simpl.
  Focus 2.
  unfold bacc.
  simpl.
  omega.
  omega.
  omega.
  Focus 2.
  omega.
  Focus 2.
  omega.
  clear.
  remember (od f x) as z.
  clear Heqz.
  generalize dependent z.
  induction b; destruct z; intros.
  reflexivity.
  destruct a.
  simpl. apply IHb.
  simpl. apply IHb.
Qed.

Check iter.

End type.

Check iter.