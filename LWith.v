(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.

(*************************************************)
(*              Additive Conjunction             *)
(*************************************************)

Record LWithVal{E:LEnv} (A B:LType) := {
  lwithval_fst : ltype A;
  lwithval_snd : ltype B;
  lwithval_weight_eqn : lweight lwithval_fst = lweight lwithval_snd
}.
Arguments LWithVal [E] A%LL B%LL.
Arguments lwithval_fst [E] [A] [B] _.
Arguments lwithval_snd [E] [A] [B] _.
Arguments lwithval_weight_eqn [E] [A] [B] _.

Definition LWith{E:LEnv} (A B:LType) : LType := {|
  ltype := LWithVal A B;
  lweight x := lweight (lwithval_fst x)
|}.
Definition LTop{E:LEnv} : LType := {|
  ltype := LWeight;
  lweight x := x
|}.
Notation "A && B" := (LWith A%LL B%LL) : LL_scope.
Definition LIff{E:LEnv} (A B:LType) : LType :=
  ((A -o B) && (B -o A))%LL.
Notation "A o-o B" := (LIff A%LL B%LL) : LL_scope.

Definition LWithConstructor{E:LEnv} (A B:LType) {W:LWeight} :
  LGoal A W -> LGoal B W -> LGoal (A && B) W.
Proof.
  intros H0 H1.
  refine {|
    lgoal_proof := {|
      lwithval_fst := lgoal_proof H0;
      lwithval_snd := lgoal_proof H1;
      lwithval_weight_eqn :=
        eq_trans (eq_sym (lweight_eqn _)) (lweight_eqn _)
    |} : ltype (A && B);
    lgoal_weight_eqn := lgoal_weight_eqn H0
  |}.
Defined.

Definition LTopConstructor{E:LEnv} {W:LWeight} :
  LGoal LTop W.
Proof.
  refine {| lgoal_proof := W : ltype LTop |}.
Defined.

Definition LWithDestructorL{E:LEnv} {A B C:LType} {W:LWeight}
  (H0 : LGoal (A -o C) W) : LGoal (A && B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(x : ltype (A && B)) =>
        lfun_val (lgoal_proof H0) (lwithval_fst x);
      lfun_weight := W
    |} : ltype (A && B -o C)
  |}.
Grab Existential Variables.
  intros x; simpl.
  refine (lweight_eqn _).
Defined.
Definition LWithDestructorR{E:LEnv} {A B C:LType} {W:LWeight}
  (H1 : LGoal (B -o C) W) : LGoal (A && B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(x : ltype (A && B)) =>
        lfun_val (lgoal_proof H1) (lwithval_snd x);
      lfun_weight := W
    |} : ltype (A && B -o C)
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite lwithval_weight_eqn.
  refine (lweight_eqn _).
Defined.

Definition LWithFst{E:LEnv} {A B:LType} : ltype (A && B -o A).
Proof.
  refine {|
    lfun_val := fun(p:ltype (A && B)) => lwithval_fst p;
    lfun_weight := 0%LWeight
  |}.
  intros x; refine (lweight_eqn _).
Defined.
Definition LWithSnd{E:LEnv} {A B:LType} : ltype (A && B -o B).
Proof.
  refine {|
    lfun_val := fun(p:ltype (A && B)) => lwithval_snd p;
    lfun_weight := 0%LWeight
  |}.
  intros x; rewrite <-lwithval_weight_eqn; refine (lweight_eqn _).
Defined.

Instance lgoal_autoapply_with_fst{E:LEnv} {T:Type} {A B C:LType}
  {n:nat} {l:list (nat * LWeight)} {W:LWeight}
  {f:ltype (A && B)}
  {Impls:list Type}
  {H: LHintedApp n l Impls (LGoal C (W + lweight (LWithFst f))%LWeight)}
  : LHintedApp n l Impls (LGoal C (W + lweight f)%LWeight).
Proof.
  exists.
  destruct H as [H].
  revert H; apply implication_list_map; intros H.
  refine {|
    lgoal_proof := lgoal_proof H
  |}.
Defined.
Instance lgoal_autoapply_with_snd{E:LEnv} {T:Type} {A B C:LType}
  {n:nat} {l:list (nat * LWeight)} {W:LWeight}
  {f:ltype (A && B)}
  {Impls:list Type}
  {H: LHintedApp n l Impls (LGoal C (W + lweight (LWithSnd f))%LWeight)}
  : LHintedApp n l Impls (LGoal C (W + lweight f)%LWeight).
Proof.
  exists.
  destruct H as [H].
  revert H; apply implication_list_map; intros H.
  refine {|
    lgoal_proof := lgoal_proof H
  |}.
Defined.

Local Ltac splitll_base ::=
  apply LWithConstructor ||
  apply LTopConstructor ||
  fail "Constructor not found".
Local Ltac destructll_left_base ::=
  apply LWithDestructorL ||
  fail "Destructor not found".
Local Ltac destructll_right_base ::=
  apply LWithDestructorR ||
  fail "Destructor not found".

Local Open Scope LL_goal_scope.
Example LWithComm{E:LEnv} (A B:LType) :
  (ILL |- A && B -o B && A).
Proof.
  introsll x.
  splitll.
  - destructll x as [_ z].
    applyll z.
  - destructll x as [y _].
    applyll y.
Defined.
Local Close Scope LL_goal_scope.
