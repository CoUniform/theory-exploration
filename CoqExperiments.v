(* This file presents Coq formalisation of 
examples of coinductive proofs from ICLP'20 paper:

E.Komendantskaya, D.Rozplokhas, H.Basold:
The New Normal: We Cannot Eliminate Cuts in
Coinductive Sequent Calculus, But Can Explore Them.

*)


(* we encode our running examples in Coq, illustrating the practical use of the coinduction hypotheses discovery across different provers.
Coinductive Horn clause theories (logic programs) defined in this paper are encoded as coinductive data types in Coq,
in order to apply Coq's coinductive rule  cofix in place of the CO-FIX rule of the Coinductive CLJ.
The remaining proof structure is analogous. *) 
  


Section Infrastructure.

(*We define some minimal infrastructure *)

(*We define ``the signature Sigma consisting of some uninterpreted symbols, analogously to how they are used in logic programs*)

(* We could, but do not, use Coq's inductive types Bool or nat in these examples, as none of the examples in the ICLP'20 paper depends on induction on Booleans or natural numbers. 
In order to mimic the minimalistic logic programming style, we define ``constants'' a, O, I, and other function symbols *)

  
  Variable A : Set.
  Variable f : A -> A.
  Variable a: A.
  Variable O : A.
  Variable I : A.


(*Coinductive Types we will use*)

CoInductive Stream : Set :=
    Cons : A -> Stream -> Stream.

CoInductive Streamnat : Set :=
    ConsStreamnat : nat -> Streamnat -> Streamnat.



Set Implicit Arguments.

Section Lazy.

(*----------------Decomposition lemmas--------------------------*)
(* the lemmas mimic lazy beta reduction on the corecursive functions *)

Definition Stream_decompose (s: Stream) : Stream :=
match s with
| Cons n s' => Cons n s'
end.

Theorem Stream_decomposition_lemma :
forall s, s = Stream_decompose s.
Proof.
intros; case s. 
intros.
unfold Stream_decompose.
trivial.
Qed.

(*Ltac Snat_unfold term :=
apply trans_equal with (1 := Snat_decomposition_lemma term).*)

Definition Streamnat_decompose (s: Streamnat) : Streamnat :=
match s with
| ConsStreamnat n s' => ConsStreamnat n s'
end.

Theorem Snat_decomposition_lemma :
forall s, s = Streamnat_decompose s.
Proof.
intros; case s. 
intros.
unfold Streamnat_decompose.
trivial.
Qed.

Ltac Snat_unfold term :=
apply trans_equal with (1 := Snat_decomposition_lemma term).

(*------------------------------------------*)



Section ICLP20.

(*------------------------------------------*)
 
  
  (*   The logic program P_stream0:  *)
  
CoInductive stream0:   Stream -> Prop :=
  | k_stream0: forall (x : A) (t: Stream),  stream0 t  -> 
                stream0 (Cons O  t).

(*Desired goal: exists z, stream0 z. *)

(*Suggested stream:*)
CoFixpoint z_str : Stream :=
Cons O z_str.

(*Suggested Coinduction Hypothesis*)
Lemma stream0_CH: stream0 z_str.
(*coinductive hypothesis taken:*)
cofix CH.
(*forcing one-step stream reduction on z_str:*)
rewrite Stream_decomposition_lemma; simpl.
(*one step resolution with the Horn clause:*)
apply k_stream0. assumption.
(*application of coinductive hypothesis:*)
apply CH.
Qed.

(*Desired Goal proven:*)

Lemma stream0_goal: exists z, stream0 z.
exists z_str.
apply stream0_CH.
Qed.

(*------------------------------------------*)


(*  The logic program P_u:  *)

CoInductive pU:   A -> Prop :=
  | ku: forall  (x: A), pU (f x) -> pU x.

(*Desired goal: pU a. *)

(*Suggested Coinduction Hypothesis*)
Lemma pU_CH: forall x, pU x.
  (*coinductive hypothesis taken:*)
  cofix CH.
  intros.
  (*one step resolution with the Horn clause:*)
  apply ku.
  (*application of coinductive hypothesis:*)
  apply CH.
  Qed.

(*Desired Goal proven:*)
Lemma pU_goal: pU a.
  apply pU_CH.
Qed.

(*------------------------------------------*)


(* The logic program P3: *)

(* Note that the predicate q could be defined by induction or 
coinduction in the code below, this would not change the coinductive proofs
involving the predicate p3 below.  *)

Inductive q: A -> Prop := 
    | ki2: q a
    | ki3: forall (x:A), q x -> q(f  x).

 
CoInductive p3:   A -> Prop :=
    | ki1: forall (x: A), p3 (f x) /\ q x -> p3 x.

(*Desired goal: p3 a. *)

(*Suggested Coinduction Hypothesis*)
Lemma p3_CH: forall x, q x -> p3 x.
  (*coinductive hypothesis taken:*)
  cofix CH.
  intros.
  (*one step resolution with the Horn clause:*)
  apply ki1.
  split.
  (*application of coinductive hypothesis:*)
  apply CH.
  (*using definition of q and assumption*)
  apply ki3; assumption.
  assumption.
Qed.

(*Desired Goal proven:*)
Lemma p3_goal: p3 a.
  apply p3_CH.
  apply ki2.
Qed.

(*------------------------------------------*)


(* The logic program P_from: *)
Variable s: A -> A.

CoInductive from:  A -> Stream -> Prop :=
   | k_from: forall (x : A) (y: Stream),  from (s x) y  -> from x (Cons x y).

(*Desired goal: exists z, from 0 z. *)

(*Suggested stream:*)
CoFixpoint fromstr (x : A ) : Stream := Cons x (fromstr (s x)).

(*Suggested Coinduction Hypothesis*)
Lemma Pfrom_CH: forall x, from x (fromstr x).
   (*coinduction hypothesis taken:*)
   cofix CH.
   intros.
   (*forcing one-step stream reduction:*)
   rewrite Stream_decomposition_lemma; simpl.
   (*one step resolution with the Horn clause:*)
   apply k_from.
   (*application of coinductive hypothesis:*)
   apply CH.
Qed.

(*Desired Goal proven:*)

Lemma from_goal: exists z, from O z.
   exists (fromstr O).
   apply Pfrom_CH.
Qed.

(*------------------------------------------*)


(* The logic program P_fib: *)
Variable add: A -> A -> A.

CoInductive fib:  A ->  A -> Stream -> Prop :=
  | k_fib: forall (x y: A) (z: Stream),  fib y (add x y) z  -> fib x y (Cons x z).

(*Desired goal: exists z, fib O I z. *)

(*Suggested stream:*)
CoFixpoint fibstr (x y: A ) : Stream := Cons x (fibstr (y) (add x y)).

(*Suggested Coinduction Hypothesis*)
Lemma Pfib_CH: forall x y, fib x y (fibstr x y).
   (*coinduction hypothesis taken:*)
   cofix CH.
   intros.
   (*forcing one-step stream reduction:*)
   rewrite Stream_decomposition_lemma; simpl.
   (*one step resolution with the Horn clause:*)
   apply k_fib.
   (*application of coinductive hypothesis:*)
   apply CH.
Qed.

(*Desired Goal proven:*)

Lemma fib_goal: exists z, fib O I z.
   exists (fibstr O I).
   apply Pfib_CH.
Qed.
  
  End ICLP20. 





