(* This file presents Coq formalisation of 
examples of proofs in higher-order Hereditary Harrop Clause logic with Cofix rule (CoHOHH)
given in the paper ``Structural Resolution: a framework for coinductive proof search 
and proof construction in Horn Clause Logic''  by E.Komendantskaya, P.Johann, and M.Schmidt 
*)




(*Coinductive Types and Corecursive Functions*)

Section Coinduction.

Variable A : Set.

CoInductive Stream : Set :=
    Cons : A -> Stream -> Stream.

CoInductive Streamnat : Set :=
    ConsStreamnat : nat -> Streamnat -> Streamnat.


Set Implicit Arguments.


(*----------------Decomposition lemmas--------------------------*)
(* the lemmas mimic lazy beta reduction on the corecursive functions *)

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

Section SuggestedAutomation.

(* This is the general tactic for automation of proofs by coinduction in Horn clause logic*)


Ltac LP_Coind  lp_cons :=
cofix H; try intros; 
try rewrite Snat_decomposition_lemma; simpl;
try apply lp_cons;
try apply H.

(* Note the above tactic takes as an argument the name of the coinductive clause from the
coinductive logic program in question. *)

Section RegularProofs.
(*Proofs in Horn clause Logic for regular corecursion *)


(* Logic program zeros, computing the stream of 0: *)

CoInductive zeros:  Streamnat -> Prop :=
  | zeros_cons: forall (y: Streamnat), zeros y  -> zeros (ConsStreamnat 0 y).

(* First-order Definition of the stream in question *)

CoFixpoint zerostr : Streamnat :=
ConsStreamnat 0 (zerostr).

(* First-order coinductive lemma in Horn clause syntax, note the use of general tactic: *)

Lemma zerosQ: zeros (zerostr).
(*
cofix H.
rewrite Snat_decomposition_lemma. simpl.
apply zeros_cons.
apply H.*)
LP_Coind zeros_cons.
Qed.

(* A logic program query*)

Lemma zerosQ2: exists x, zeros x.
exists zerostr; apply zerosQ.
Qed.



Section IrregularProofs.

(*In this section, I am assuming one works with stream of natural numbers, 
with usual pattern-matching available on both data structures -- nat and Streamnat *)

(*Below is our running example program from:*)

CoInductive from:  nat -> Streamnat -> Prop :=
  | from_cons: forall (x : nat) (y: Streamnat),  from (S x) y  -> from x (ConsStreamnat x y).


(* in LP, we make a query "from 0 y", which in Coq woudl mean exists y, from 0 y. 
This will not work, as coinductive hypotheses cannot be formed with existentials 
(i.e. in negative position). *)

(*So we need to provide the term for this existetial first*)

CoFixpoint fromstr (n:nat) : Streamnat :=
ConsStreamnat n (fromstr (S n)).

(* Because of the above definition, we need higher-order logic to 
express the recursive scheme. It is no longer first-order Horn clause logic  *)

(*Now our LP query still cannot be proven directly by coinduction, we need a 
more general form:  


 The query  Lemma fromQ1: exists x, from 0 x. cannot be proven directly, 
as "from 0 fromstr 0" will not give a 
usable coinductive hypothesis.


This leads us to extend from Horn clauses to Hereditary Harrop clauses, to allow
universal quantification on the goals:
*)

Lemma fromQ: forall x, from x (fromstr x).
cofix H.
intros.
rewrite Snat_decomposition_lemma; simpl.
(*the above is just a forced pattern matching on stream*)
apply from_cons.
(*the above is one resolution step*)
apply H.
(*the last step applies coinductve hypothesis*)
Qed.



(* So the following goes through, using my general automated tactic instead of 
the manual tactic application as above *)
Lemma fromQ2: forall x, from x (fromstr x).
LP_Coind from_cons.
Qed. 



(*Essential thing to know in order to apply the tactic is the constructor of the coinductive type in question --
in LP terms it is the clause that defines the coinductive behaviour. *)

(*Now our initial LP query goes through as a particular case of more general lemma: *)
Lemma fromQ1: exists x, from 0 x.
exists (fromstr 0).
apply fromQ.
Qed.

(* Note that when reasoning with from, we did not need to know about 
the inductive structure of nat. 
 But we needed lazy beta-reduction (or case reasoning ) 
on constructor of Streamnat via Decomposition lemmas. *)



Section FibonacciLP.


(* Fibonacci, like from, requires second-order recursive scheme and on top, 
Hereditary Harrop clause syntax and
inductive reasoning, too:. The three Horn clause of the logic 
program Fibs are given below. *)

Inductive addp: nat -> nat -> nat -> Prop :=
| addp_0: forall y, addp 0 y y 
| addp_S: forall x y z, addp x y z -> addp (S x) y (S z).

CoInductive fibs:  nat -> nat -> Streamnat -> Prop :=
  | fibs_cons: forall (x y : nat) (s: Streamnat),  (exists z, addp x y z  /\  fibs y z s)  
                                           -> fibs x y  (ConsStreamnat x s).


(*For the above program, we may have a query in LP like exists x, fibs(0, s(0), x)?*)

(*So we need to provide the term for this existetial first*)

CoFixpoint fibstr (n m :nat) : Streamnat :=
ConsStreamnat n (fibstr m (n+m)).

(* Because of the above definition, we need higher-order logic to express the 
recursive schemes  *)

(*Unlike the example of "from", we need reasoning "modulo some theory" above: 
as n+m is pre-defined in the theory. 
So, not only the use of natural numbers is important for pattern-matching on 
inductive constructors, 
but also the presence of some theory.*)


(*Now our LP query still cannot be proven directly by coinduction, 
we need a more general form:  *)

(* The tactic LP_Coind fibs_cons. will no longer work, as essential here is reasoning on add, 
natural numbers and modulo theory *)

Lemma fibQ: forall x y, fibs x y (fibstr x y).
cofix H.
intros x y.
rewrite Snat_decomposition_lemma; simpl.
(*the above is just a forced pattern matching on stream*)
apply fibs_cons.
(*the above is one resolution step. Up to this step, my old tactic works, but now 
there is an existential proof for exists z : nat, add x y z /\ fibs y z (fibstr y (x + y))*)
exists (x+y).
apply conj.
(*apply nat_ind.*)
induction x.
simpl; apply addp_0.
simpl; apply addp_S.
apply IHx.
(*the above two lines take reasoning on add and nat*)
apply H.
(*the last step applies coinductve hypothesis*)
Qed.


(*So the tactic for more complex proof automation could  be:*)

Ltac LP_Coind2  lp_cons ipred icons1 icons2:=
cofix H; try intro x; try intro y;
try rewrite Snat_decomposition_lemma; simpl; try apply lp_cons;
repeat match goal with 
| [ x: nat , y: nat  |- exists _ , _   ] => exists (x+y) end;
try apply conj;
repeat match goal with 
| [ IHx: _ |- ipred ?x _  _ ] => try induction x; simpl; try apply icons1; try apply icons2; try apply IHx; auto end;
try apply H.

(*Testing the above tactic, all three previous lemmas are proven: *)
Lemma fibQ1: forall x y, fibs x y (fibstr x y).
LP_Coind2 fibs_cons addp addp_0 addp_S.
Qed.

Lemma zerosQ1: zeros (zerostr).
LP_Coind2 zeros_cons nat nat nat.
Qed.

Lemma fromQ4: forall x, from x (fromstr x).
LP_Coind2 from_cons nat nat nat.
Qed.

(*Now our initial LP query goes through as a particular case of more general lemma: *)
Lemma fromQ3: exists x, fibs 0 (S 0) x.
exists (fibstr 0 (S 0)).
apply fibQ.
Qed.












 









