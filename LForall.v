(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.

(*************************************************)
(*         Linear Universal Quantification       *)
(*************************************************)

Record LForallVal{E:LEnv} {T:Type} (A:T -> LType) := {
  lforallval : forall t : T, ltype (A t);
  lforallval_weight : LWeight;
  lforallval_weight_eqn t : lweight (lforallval t) = lforallval_weight
}.
Arguments LForallVal [E] [T] A%LL.
Arguments lforallval [E] [T] [A] _ _.
Arguments lforallval_weight [E] [T] [A] _.
Arguments lforallval_weight_eqn [E] [T] [A] _ _.
Coercion lforallval : LForallVal >-> Funclass.

Definition LForall{E:LEnv} {T:Type} (A:T -> LType) : LType := {|
  ltype := LForallVal A;
  lweight := @lforallval_weight _ _ _
|}.
Notation "'lforall' x .. y , p"
    := (LForall (fun x => .. (LForall (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'lforall'  '/  ' x  ..  y ,  '/  ' p ']'")
  : LL_scope.

Instance LForall_weight_delegate{E:LEnv} {T:Type} (A:T->LType)
    (f : ltype (LForall A)) (t : T)
    : LWeightCastSelf (lweight (f t)) (lweight f).
Proof.
  rewrite lforallval_weight_eqn.
  exists; reflexivity.
Defined.

Definition LForallIntroduction{E:LEnv} {T:Type} (A:T -> LType) {W:LWeight}
    : (forall t, LGoal (A t) W) -> LGoal (LForall A) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lforallval t := H0 t;
      lforallval_weight := W
    |} : ltype (LForall A)
  |}.
Grab Existential Variables.
  intros t; simpl.
  refine (lweight_eqn _).
Defined.

Definition LForallSpecialization{E:LEnv} {T:Type} {A:T -> LType} {B:LType}
    {W:LWeight} (t:T)
    : LGoal (A t -o B) W -> LGoal (LForall A -o B) W.
Proof.
  intros H0.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(a:ltype (LForall A)) =>
        lgoal_proof H0 (lforallval a t);
      lfun_weight := W
    |} : ltype (LForall A -o B)
  |}.
Grab Existential Variables.
  intros x; simpl; refine (lweight_eqn _).
Defined.

Instance lgoal_autoapply_forall{E:LEnv} {T:Type} {A:T->LType} {B:LType}
  {n:nat} {l:list (nat * LWeight)} {W:LWeight}
  {f:ltype (LForall A)}
  {Impls:list Type}
  {t:T}
  {H: LHintedApp n l Impls (LGoal B (W + lweight (f t))%LWeight)}
  : LHintedApp n l Impls (LGoal B (W + lweight f)%LWeight).
Proof.
  exists.
  destruct H as [H].
  revert H; apply implication_list_map; intros H.
  refine {|
    lgoal_proof := lgoal_proof H
  |}.
Defined.

Local Ltac introll_base x ::=
  introll_base_limpl x ||
  (apply LForallIntroduction; intros x) ||
  fail "Linear Introduction Failed".
Tactic Notation "specializell" "(" constr(x) constr(t) ")" :=
  revertll x; apply (LForallSpecialization t); introll x.

Local Open Scope LL_goal_scope.
Example LForallComm{E:LEnv} {S T:Type} (A:S -> T -> LType) :
  (ILL |- (lforall s t, A s t) -o (lforall t s, A s t)).
Proof.
  introsll x t s.
  (* specializell (x s). *)
  (* specializell (x t). *)
  applyll x.
Defined.
Local Close Scope LL_goal_scope.