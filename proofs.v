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


Section LogicPrograms.


  (*Experiments with coinductive hypotheses in CoLP/coALP*)

(*Natural numbers coinductively, Below is our running LP defining natural numbers*)

CoInductive natinf :=
 | zero : natinf
 | succ : natinf -> natinf.

CoInductive nat_lp: natinf -> Prop :=
  | nat_s: forall (x : natinf), nat_lp x  ->  nat_lp (succ x)
  | nat_0: nat_lp zero.

CoFixpoint infnat (n: natinf) : natinf :=
succ (infnat n).

(*----------------Decomposition lemmas--------------------------*)

Definition natinf_decompose (s: natinf) : natinf :=
match s with
| zero => zero
| succ n => succ n 
end.

Theorem natinf_decomposition_lemma :
forall s, s = natinf_decompose s.
Proof.
intros; case s; auto; intros.
(*unfold Streamnat_decompose.
trivial.*)
Qed.

Ltac natinf_unfold term :=
apply trans_equal with (1 := natinf_decomposition_lemma term).



(*------------------------------------------*)

Lemma nat_query: exists x, nat_lp x.
Proof.
exists (infnat zero).
cofix H.
rewrite natinf_decomposition_lemma; simpl.
  apply nat_s.
 apply H.
Qed.

Print nat_query.


(* Gives proof-term:

nat_query = 
ex_intro (fun x : natinf => nat_lp x) (infnat zero)
  (cofix H  : nat_lp (infnat zero) :=
     eq_ind_r nat_lp (nat_s H) (natinf_decomposition_lemma (infnat zero)))
     : exists x : natinf, nat_lp x

*)





(* Ofcourse, if we had: 


CoInductive nat_lp3: A -> Prop :=
  | natsi: forall (x : A), nat_lp3 (s_nat x)  ->  nat_lp3  x
  | nat0i: nat_lp3 o_nat.

(* then we would need to have a coinductive proof. Cf. Fu Peng's examples of non-terminating cases *)

Lemma nat_query3:  nat_lp3 (s_nat o_nat).
Proof.
  generalize o_nat.
  cofix CH.
  intros; apply natsi.
  apply CH.
  Qed.


Print nat_query3.

(* gives coinductive proof-term 

nat_query3 = 
(cofix CH (o_nat0 : A) : nat_lp3 (s_nat o_nat0) := natsi (CH (s_nat o_nat0)))
  o_nat
     : nat_lp3 (s_nat o_nat)

*) *)


(* You can do similar massaging with natlist in concrete and abstract form*)

CoInductive nat_list: (list nat) -> Prop :=
  | nat_cons: forall (x : nat) (y: list nat), nat_list y  ->  nat_list (cons x y)
  | nat_nil: nat_list nil.



Section LPCoinductiveProofs.

(*In this section, I am assuming one works with stream of natural numbers, 
with usual pattern-matching available on both data structures -- nat and Streamnat *)

(*Below is our running example program from:*)

CoInductive from:  nat -> Streamnat -> Prop :=
  | from_cons: forall (x : nat) (y: Streamnat),  from (S x) y  -> from x (ConsStreamnat x y).


(* in LP, we make a query from 0 y, which in Coq woudl mean exists y, from 0 y. 
This will not work, as coinductive hypotheses cannot be formed with existentials. *)

(*So we need to provide the term for this existetial first*)

CoFixpoint fromstr (n:nat) : Streamnat :=
ConsStreamnat n (fromstr (S n)).

(* Because of the above definition, we need higher-order logic to express the recursive schemes  *)

(*Now our LP query still cannot be proven directly by coinduction, we need a more general form:  *)


(* The query  Lemma fromQ1: exists x, from 0 x. cannot be proven directly, 
as "from 0 fromstr 0" will not give a 
usable coinductive hypothesis:
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

(* this inspires the folloiwng tactic:*)

Ltac LP_Coind  lp_cons :=
cofix H; try intros; 
try rewrite Snat_decomposition_lemma; simpl;
try apply lp_cons;
try apply H.

(* So the following goes through:
Lemma fromQ: forall x, from x (fromstr x).
LP_Coind from_cons.
Qed. *)


(*Now our initial LP query goes through as a particular case of more general lemma: *)
Lemma fromQ1: exists x, from 0 x.
exists (fromstr 0).
apply fromQ.
Qed.

(* Note that when reasoning with from, we did not need to know about inductive structure of nat. 
 But we did case on constructor of Streamnat. *)


(* I will now try to use and extend this tactic to work with other programs. *)

(* First of all, all programs with regular corecursion will work trivially, 
and indeed will not require second-order logic *)

(* Logic program zeros: *)
CoInductive zeros:  Streamnat -> Prop :=
  | zeros_cons: forall (y: Streamnat), zeros y  -> zeros (ConsStreamnat 0 y).

CoFixpoint zerostr : Streamnat :=
ConsStreamnat 0 (zerostr).

Lemma zerosQ: zeros (zerostr).
(*
cofix H.
rewrite Snat_decomposition_lemma. simpl.
apply zeros_cons.
apply H.*)
LP_Coind zeros_cons.
Qed.

Print zerosQ.

(*
Note that the above is proven by coinduction automatically, using my tactic *)

(*Essential thing to know in order to apply the tactic is the constructor of the coinductive type in question --
in LP terms it is the clause that defines the coinductive behaviour. *)

(* Now Fibonacci, which, like from, requires second-order recursive scheme and on top, inductive reasoning, too: *)

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

(* Because of the above definition, we need higher-order logic to express the recursive schemes  *)

(*Unlike the example from, we need reasoning "modulo some theory" above: as n+m is pre-defined in the theory. 
So, not only the use of natural numbers is important for pattern-matching on inductive constructors, 
but also the presence of some theory.*)


(*Now our LP query still cannot be proven directly by coinduction, we need a more general form:  *)

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

Print fibQ.
Print Nat.add.

(*So the tactic could  be:*)

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


(*Using implicative CH instead:*)

Lemma fibQ2: forall x y, (addp x y (x+y)) -> fibs x y (fibstr x y).
cofix H.
intros x1 y1 H0.
try rewrite Snat_decomposition_lemma; simpl.
apply fibs_cons.
exists (x1 + y1).
apply conj.
apply H0.
apply H.
apply  H0.
apply H.
Qed.





(*When productivity arises from realisability transformation, the coinductive constructor 
is in the proof term argument:*)

CoInductive prod:  nat -> natinf -> Prop :=
  | prod_cons: forall (x : nat) (y: natinf) ,  prod x y  
                                           -> prod x (succ y).

CoFixpoint prodstr  : natinf :=  
succ prodstr.

Lemma Qprod: exists x, prod 0 x.
exists prodstr.
cofix H.
try rewrite natinf_decomposition_lemma; simpl; try apply prod_cons.
try apply H.
Qed.

(*end of realisability transformation experiment*)



(*
Now coming to unguarded example
*)



Variables (x : A) (f: A -> A).


CoInductive bad: A -> Prop :=
  | bad_c: forall (x : A), bad x  ->  bad  x.


Lemma  bad_l: bad x.
  generalize x.
  cofix CH.
  intro.
apply bad_c.
apply CH.
Qed.

Print bad_l.

(* Gives coinductive proof-term

bad_l = cofix CH  : bad o_nat := bad_c CH
     : bad o_nat

*)

(*
CoInductive Stream : Set :=
    Cons : A -> Stream -> Stream.
*)


(* Compare with guarded but coinductive case *)

CoInductive stream_proof: Stream A -> Prop :=
| streamc: forall (x : A) (y: Stream A),  stream_proof y  ->  stream_proof (Cons A x y).

(* Not sure how to finalise this one yet: *)

Lemma stream_coind: forall x, stream_proof (x).
Proof.
   cofix CH.
  intros.
case x0.
intros.
apply streamc.
apply CH.
Qed.

Print stream_coind.


(* Gives the proof-term 

stream_coind = 
cofix CH (x0 : Stream A) : stream_proof x0 :=
  match x0 as s return (stream_proof s) with
  | Cons a s => streamc a (CH s)
  end
     : forall x : Stream A, stream_proof x


*)


(*
Now abstractly
 *)


Inductive some_type: Set :=
  g: some_type -> some_type.


CoInductive some_prop:  some_type -> Prop :=
| some_cons: forall (x : some_type),  some_prop x  -> some_prop ( g x).


Lemma some_proof: forall x,  some_prop x. 
Proof. 
cofix H.
intros.
case x0.
intros.
apply some_cons.
apply H.
Qed.

Print some_proof.

(* the proof term is:
some_proof = 
cofix H (x0 : some_type) : some_prop x0 :=
  match x0 as s return (some_prop s) with
  | g s => some_cons (H s)
  end
     : forall x : some_type, some_prop x

 *)


(* What if I try some harder cases of coinduction in CoALP?  *)

(*
CoInductive Stream : Set :=
    Cons : A -> Stream -> Stream.
 *)


CoFixpoint from (n: nat) : Stream nat := Cons nat n (from (S n)).

(*
CoInductive Sfrom: Stream  nat -> Set :=
  fc: forall x,  Sfrom (from x) .
*)




(*----------------Decomposition lemmas--------------------------*)

Definition Stream_decompose (A: Set) (l: Stream A) : Stream A :=
match l with
| Cons a l' => Cons A a l'
end.

Theorem Stream_decomposition_lemma :
forall (A : Set) (l: Stream A), l = Stream_decompose l.
Proof.
intros; case l. 
intros.
unfold Stream_decompose.
trivial.
Qed.

Ltac Stream_unfold term :=
apply trans_equal with (1 := Stream_decomposition_lemma term).

(*------------------------------------------*)


CoInductive from_lp: nat -> Stream nat -> Prop :=
| from_cons: forall (x : nat) ( z: Stream nat) ,
               from_lp (S x) z -> from_lp x (Cons nat x z).

(* below is the method ACM paper suggests to close the proof*)


CoInductive from_c: nat -> Stream nat -> Prop :=
  | from_con: forall (x : nat) ( z: Stream nat) ,
               from_c (S x) z -> from_c x (Cons nat x z)
| from_ch:  forall x, from_c 0 (Cons nat 0 (Cons nat (S 0) x)) -> from_c (S (S 0 )) x.


Variables (y z: Stream nat).

(* below is the proof I am getting for ACM paper *)

Lemma ACM_paper2: exists x,  from_c 0 (Cons nat 0 (Cons nat (S 0) (Cons nat (S (S 0)) x))).
  exists y.
    cofix H.
apply from_con.
apply from_con.
apply from_ch.
apply H.
Qed.

Print ACM_paper2.

(*
Lemma ACM_paper1: exists x,  from_lp 0 (Cons nat 0 (Cons nat (S 0) (Cons nat (S (S 0)) x))).
  exists y.
  generalize y.
  cofix H1 with (H2: forall x, from_lp 0 (Cons nat 0 (Cons nat (S 0) x)) -> from_lp (S (S 0 )) x). 
intro.
  apply from_cons.
apply from_cons.
apply H2.
apply H1.
intros.
(* 2 problems: not guarded and H2 is hard to prove*)
 *)

(* below says that coinductive hypothesis above follows from conductive view of this program *)

CoInductive from_c2: nat -> Stream nat -> Prop :=
| from_ch2:  forall x y, from_c2  x (Cons nat x y) -> from_c2 (S x) y.


Lemma ch_from: forall x, from_c2 0 (Cons nat 0 (Cons nat (S 0) x)) -> from_c2 (S (S 0 )) x.
intros.
apply from_ch2.  
apply from_ch2.
apply H.
Qed.

Print ch_from.

Lemma general:  (forall x, (exists y, from_lp x y)) -> forall x, ( exists z,  from_lp (S x) z).
  intros.
  exists (Cons nat (S x0) z).
(*generalize x0.
cofix H1 with (H2: forall x,  from_lp (S x) (Cons nat (S x) y)  ).
intros.*)
  generalize x0.
cofix.
intro.
apply from_cons.
apply H.
apply H2.

Guarded.
apply general.

(* the above two are likely hypotheses taken from Coalp execution of from*)

(*
Hypothesis CHyp:   from_lp 0 (Cons nat  0 (Cons nat (S 0) (Cons nat (S (S 0)) y)) ) ->  from_lp (S (S (S 0))) y.
(*The next hypothesis is taken from the "coinductive hypothesis" tree generated by CoALP*)


Hypothesis CHyp2: from_lp 0 (Cons nat  0 (Cons nat (S 0) y)) ->  from_lp (S (S 0)) y.


Hypothesis CHyp3: from_lp (S (S 0)) y -> from_lp 0 (Cons nat  0 (Cons nat (S 0) y)) .

*)

(* The following corresponds to the last tree CoALP constructs, and does not require any coinduction or additional hypotheses whatsover. *)


Lemma Coalp: exists x,  from_lp (S ( S 0)) x -> from_lp 0 (Cons nat 0 (Cons nat (S 0) x)).
  exists (Cons nat (S (S 0)) y).
 (*cofix.*)
  intros.
apply from_cons.
apply from_cons.
trivial.
Qed.

(*

Lemma CHyp_l: from_lp 0 (Cons nat  0 (Cons nat (S 0) y)) ->  from_lp (S (S 0)) y.
cofix.

 *)

Lemma mutual: exists x,  from_lp 0 x.
  exists (Cons nat ( 0 ) (Cons nat (S 0) z)).
  generalize z.
cofix CH  with  (CH2 : (forall z, from_lp (S 0) (Cons nat (S 0) z))).
intros.
apply from_cons.
apply CH2.
Guarded.
Admitted.
(* cant' finish it *)

Lemma query: exists x, from_lp 0 x.
  exists (Cons nat 0 (Cons nat (S  0) y)).
  (*cofix CH  with  (CH2 : from_lp 0 (Cons nat  0 (Cons nat (S 0) (Cons nat (S (S 0)) z)) )).*)
   cofix CH  with  (CH2 : from_lp (S ( S 0)) y).
repeat apply from_cons.
apply CH2.
Admitted.

(*Can't finish it*)


Lemma query2: exists x, from_lp 0 x.
exists (Cons nat 0 (Cons nat (S  0) y)).
cofix.
apply from_cons.
apply from_cons.
apply CHyp2.
apply query.
(* not guarded *)
Admitted.

(* So I am now taking CHyp2 as a constructor*)

CoInductive from_lp_updated: nat -> Stream nat -> Prop :=
| from_cons2: forall (x : nat) ( z: Stream nat) ,
               from_lp_updated (S x) z -> from_lp_updated x (Cons nat x z)
| from_hyp:   from_lp_updated 0 (Cons nat  0 (Cons nat (S 0) y)) ->  from_lp_updated (S (S 0)) y.                                         

(*I am taking the existential witness to be exactly the term given by "Coinductive hypothesis tree" in CoALP*)

Lemma query2: exists x, from_lp_updated 0 x.
exists (Cons nat 0 (Cons nat (S  0) y)).
cofix.
apply from_cons2.
apply from_cons2.
apply from_hyp.
apply query2.
Qed.

Print query2.

(*Note: the below alternative does not require a coinductive proof at all, 
similarly to how Fu Peng does it *)  

CoInductive from_lp_updated2: nat -> Stream nat -> Prop :=
| from_cons3: forall (x : nat) ( z: Stream nat) ,
               from_lp_updated2 (S x) z -> from_lp_updated2 x (Cons nat x z)
| from_hyp2:   from_lp_updated2 (S (S 0)) y.                                         


Lemma query3: exists x, from_lp_updated2 0 x.
exists (Cons nat 0 (Cons nat (S  0) y)).
cofix.
apply from_cons3.
apply from_cons3.
apply from_hyp2.
Qed.

Print query2.



(* the following is playing with Coq's function from *)

Lemma aux: forall x, (from x)  = Cons nat x (from (S x)).
intros.
  Stream_unfold (from x0).
simpl; trivial.
Qed.

Lemma query:  forall x, from_lp x (from x).
  (*  cofix H1 with  (H2 : forall x y, from_lp (S x) y -> from_lp  x ( Cons nat  x y) ).*)
  cofix CH.
  intros.
rewrite aux.
apply from_cons.
apply CH.
Qed.

 Lemma ex_query: forall x, (exists y,  (from_lp x y)). 
   intros.
   exists (from x0).
apply query.
 Qed.

 Print ex_query.


 (*
Lemma aux3: forall x y z, x = y -> from_lp x (Cons nat y z).
  intros.
  generalize x0 y z.
cofix CH.
intros.
apply from_cons.
case z0.
intros.
apply H.



Lemma aux2: forall x z,   from_lp x (Cons nat x z) -> from_lp (S x) z.
cofix H.
intros.
case z.
intros.
apply from_cons.
apply H.
*)


Lemma from_proof: forall x y, (x = Cons nat 0  y) -> from_lp (S 0) y   -> (from_lp 0 x).
  intros.
rewrite H.
apply from_cons.
trivial.
Qed.

Lemma aux: forall x y z, from_lp x y -> from_lp (S x) z ->  from_lp x (Cons nat x z).
cofix H.
intros.
apply from_cons.
trivial.
Qed.



Lemma query: forall x y,  from_lp x y.
  intros.
case from_lp.
  cofix H.
intros.
case y.
intros.
apply aux.
elim x.
  case x.
apply from_proof.



Section Flops.
  


Variables (int : A) (d: A -> A)(f: A -> A).


(* --- Residue of flops paper experiments -*)



(*(h: A -> A) (mu: (A -> A ) -> A -> A) . *)


CoInductive p2:  A -> Prop :=
p_c: forall (a : A), 
         p2 (f (f a)) ->  p2 (f a).

(*Lemma eqx: forall x, EQ (x).
 Admitted. *)



Lemma flop: p2 (f int).
  (*  generalize (inteq).*)
  Proof.
  generalize (int).
cofix H.
intros.
apply p_c.
apply H.
Qed.


CoInductive eq:  A -> Prop :=
  | eq_c: forall (a : A), eq a -> eq (d (d a)) ->  eq (d a)
  | eq_i: eq(int).


Definition F_eq: (forall x, eq (x) -> eq (d x)) -> forall x, eq ( x) -> eq (d x).
intros.
apply eq_c.
apply H0.
apply H.
apply H.
trivial.
Defined.

Print F_eq.

(* nested recursion*)
Lemma co_eq: forall x,  eq(x) ->  eq(d x).
Proof cofix H: forall x, (eq x -> eq (d x)) := F_eq H.
Admitted.
*)

Lemma eq_ch: eq (d int).
Proof.
generalize (eq_i);   generalize (int); cofix CH.
  intros x eqi; apply eq_c; try apply eqi; repeat apply CH; trivial.
Qed.
Admitted.




Lemma aux: forall x, eq x ->  eq(d x) .
  cofix H; intros; apply eq_c; trivial; repeat apply H; trivial.
Admitted.

Lemma eq_ch2: eq(d int).
apply aux; apply eq_i.
Admitted.  

CoInductive EQ:  A -> Prop :=
EQ_i: forall (a : A), 
        EQ a -> EQ (d (d a)) ->  EQ (d a).

(*Lemma eqx: forall x, EQ (x).
 Admitted. *)


Lemma flops: forall x, EQ x ->  EQ(d x) .
  cofix H. 
  intro.
  intro.
  apply EQ_i.
  auto.
  apply H.
  apply H.
auto.
Admitted.

Axiom inteq : EQ int.
  
Lemma flops2: EQ (d int).
apply flops.
apply inteq.  
Qed.

Print flops2. 

Lemma flop5: EQ (d int).
  generalize (inteq).
  generalize (int).
cofix H.
intros.
apply EQ_i.
trivial.
apply H.
apply H.
trivial.
Admitted.



(* But first note:

-- we actually marked EQ as coinductive to start with, thus allowing coinductive hypotheses on it

-- richer coinductive hypothesis -- in implicative form was needed*)

(* now cases that Lammel could do *)

Variables  (od: A -> A)(ev: A -> A).

CoInductive p:  A -> Prop :=
| p_od: forall (a : A), 
          p (od a) ->  p (ev a)
| p_ev: forall (a : A), 
         p (ev a) ->  p (od a).

(*Axiom inteql : EQl int.*)


Lemma p_coind: p (od int).
cofix CH.
   apply p_ev.
apply p_od.
apply CH.
Qed.

Print p_coind.


Definition F_p: (p (od int)) -> p (od int).
  intros.
apply p_ev; apply p_od.
trivial.
Defined.
  
Lemma p_coind2: p (od int).
Proof  cofix H: p(od int) := F_p H.


Print p_coind2.

CoInductive EQl:  A -> Prop :=
| EQ_od: forall (a : A), 
        EQl a ->  EQl (od a) ->  EQl (ev a)
| EQ_ev: forall (a : A), 
        EQl a -> EQl (ev a) ->  EQl (od a).

Axiom inteql : EQl int.

Lemma flopd: EQl (od int).
cofix Hod.
apply EQ_ev.
apply inteql.
apply EQ_od.
apply inteql.
apply Hod.
Qed.

Print flopd.

(*or below -- when coinductive lemma is taken later, but still in a simple form*) 

Lemma flopf: EQl (od int).
  apply EQ_ev.
  apply inteql.
cofix Hev.
apply EQ_od.
apply inteql.
apply EQ_ev.
apply inteql.
apply Hev.
Qed.


(* Bush tree *)

Variables (Star : Type) ( HPTree : (Star -> Star) -> Star -> Star) 
          (Mu : ((Star -> Star) -> Star -> Star) -> Star -> Star) (Pair : Star -> Star -> Star).

 
CoInductive Eq :  Star -> Prop :=
| K1 : forall (a : Star) (f : (Star -> Star) -> Star -> Star), 
         Eq (f (Mu f) a) -> Eq (Mu f a)
| K2 : forall (a : Star) (f : Star -> Star), 
         Eq a -> Eq (f (Pair a a)) -> Eq (HPTree f a)
| K3 : forall (a b : Star), 
         Eq a -> Eq b -> Eq (Pair a b). 

Lemma tree: forall (x : Star) , Eq x -> Eq (Mu HPTree x).
Proof. 
cofix alpha.
intros.
apply K1.
apply K2.
trivial.
apply alpha.
apply K3.
trivial.
trivial.
Qed.



  (* not needed for now:
Print list.

CoInductive odd: list  A -> Prop :=
  | Onil: odd nil
  | OCons: forall (a b :A) (l: list A),  odd(l) -> odd (cons a (cons b l) ).

CoInductive even : list A -> Prop :=
  | Econs: forall (a :A) (l: list A),  odd(l) -> even (cons a l ).*)




(*
CoInductive EQm:  A -> Prop :=
EQ_im: forall (h a : A), 
        EQm (h (mu h) a) -> EQ (d (d a)) ->  EQ (d a).

(*Lemma eqx: forall x, EQ (x).
 Admitted. *)
*)

























 









