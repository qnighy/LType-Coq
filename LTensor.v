(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.

(*************************************************)
(*           Multiplicative Conjunction          *)
(*************************************************)

Definition LTensor{E:LEnv} (A B:LType) : LType := {|
  ltype := ltype A * ltype B;
  lweight x := (lweight (fst x) + lweight (snd x))%LWeight
|}.
Definition LOne{E:LEnv} : LType := {|
  ltype := unit;
  lweight := fun _ => 0%LWeight
|}.
Notation "A * B" := (LTensor A%LL B%LL) : LL_scope.
Notation "1" := LOne : LL_scope.

Definition LTensorConstructor{E:LEnv} (A B:LType) :
  ltype (A -o B -o A * B).
Proof.
  refine {|
    lfun_val a := {|
      lfun_val b := (a, b) : ltype (A * B);
      lfun_weight := a;
      lfun_weight_eqn := _
    |} : ltype (B -o A * B);
    lfun_weight := 0%LWeight;
    lfun_weight_eqn := _
  |}.
  intros x; refine (lweight_eqn _).
Grab Existential Variables.
  intros x; refine (lweight_eqn _).
Defined.

Definition LOneConstructor{E:LEnv} : ltype 1 := tt.

Definition LTensorDestructor{E:LEnv} (A B C:LType) :
  ltype ((A -o B -o C) -o (A * B -o C)).
Proof.
  refine {|
    lfun_val := fun(f:ltype (A -o B -o C)) => {|
      lfun_val := fun(p:ltype (A * B)) => f (fst p) (snd p);
      lfun_weight := f;
      lfun_weight_eqn := _
    |} : ltype (A * B -o C);
    lfun_weight := 0%LWeight;
    lfun_weight_eqn := _
  |}.
  intros x; refine (lweight_eqn _).
Grab Existential Variables.
  intros x; refine (lweight_eqn _).
Defined.
Definition LOneDestructor{E:LEnv} (A:LType) :
  ltype (A -o (1 -o A)).
Proof.
  refine {|
    lfun_val := fun(f:ltype A) => {|
      lfun_val := fun(p:ltype 1) => f;
      lfun_weight := f;
      lfun_weight_eqn := _
    |} : ltype (1 -o A);
    lfun_weight := 0%LWeight;
    lfun_weight_eqn := _
  |}.
  intros x; refine (lweight_eqn _).
Grab Existential Variables.
  intros x; refine (lweight_eqn _).
Defined.

Local Ltac splitll_base ::=
  applyll LTensorConstructor ||
  applyll LOneConstructor ||
  fail "Constructor not found".
Local Ltac destructll_base ::=
  applyll LTensorDestructor ||
  applyll LOneDestructor ||
  fail "Destructor not found".

Local Open Scope LL_goal_scope.
Example TensorComm{E:LEnv} (A B:LType) :
  (ILL |- A * B -o B * A).
Proof.
  introsll x.
  destructll x as [y z].
  splitll
    carrying z into 1.
  - applyll z.
  - applyll y.
Defined.
Local Close Scope LL_goal_scope.
