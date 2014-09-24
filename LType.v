(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)


(*************************************************)
(*      Environment for Linear Logic             *)
(*************************************************)
Class LEnv := {
  LWeight : Type;
  LWeightPlus : LWeight -> LWeight -> LWeight;
  LWeightZero : LWeight;
  LWeightPlusAssoc a b c :
    LWeightPlus a (LWeightPlus b c) = LWeightPlus (LWeightPlus a b) c;
  LWeightZeroL a : LWeightPlus a LWeightZero = a;
  LWeightZeroR a : LWeightPlus LWeightZero a = a;
  LWeightPlusComm a b : LWeightPlus a b = LWeightPlus b a
}.

Delimit Scope LWeight_scope with LWeight.
Arguments LWeightPlus [_] _%LWeight _%LWeight.
Notation "a + b" := (LWeightPlus a b) : LWeight_scope.
Notation "0" := LWeightZero : LWeight_scope.


(*************************************************)
(* Auto-derivation rules for proposition weights *)
(*************************************************)
Class LWeightMinus{E:LEnv} (W V X:LWeight) := {
  lweightminus_eqn : (V + X = W)%LWeight
}.
Arguments LWeightMinus [E] W%LWeight V%LWeight X%LWeight.
Arguments Build_LWeightMinus [E] [W] [V] [X] _.
Arguments lweightminus_eqn [E] [W] [V] [X] [_].
Class LWeightMinus1{E:LEnv} (W V X:LWeight) := {
  lweightminus1_eqn : (V + X = W)%LWeight
}.
Arguments LWeightMinus1 [E] W%LWeight V%LWeight X%LWeight.
Arguments Build_LWeightMinus1 [E] [W] [V] [X] _.
Arguments lweightminus1_eqn [E] [W] [V] [X] [_].
Class LWeightAnnihil{E:LEnv} (W:LWeight) := {
  lweightannihil_eqn : (W = 0)%LWeight
}.
Arguments LWeightAnnihil [E] W%LWeight.
Arguments Build_LWeightAnnihil [E] [W] _.
Arguments lweightannihil_eqn [E] [W] [_].

Class LWeightCastPlus{E:LEnv} (W V X:LWeight) := {
  lweightcastplus_eqn : (V + X = W)%LWeight
}.
Arguments LWeightCastPlus [E] W%LWeight V%LWeight X%LWeight.
Arguments Build_LWeightCastPlus [E] [W] [V] [X] _.
Arguments lweightcastplus_eqn [E] [W] [V] [X] [_].
Class LWeightCastZero{E:LEnv} (W:LWeight) := {
  lweightcastzero_eqn : (0 = W)%LWeight
}.
Arguments LWeightCastZero [E] W%LWeight.
Arguments Build_LWeightCastZero [E] [W] _.
Arguments lweightcastzero_eqn [E] [W] [_].

Instance LWeightCastPlus_self{E:LEnv} (V X:LWeight)
    : LWeightCastPlus (V + X)%LWeight V X := {|
  lweightcastplus_eqn := eq_refl
|}.
Instance LWeightCastZero_self{E:LEnv}
    : LWeightCastZero 0%LWeight := {|
  lweightcastzero_eqn := eq_refl
|}.

Instance LWeightMinus_VPlus{E:LEnv} {W W' X V V0 V1:LWeight}
    {H:LWeightCastPlus V V0 V1}
    {H0:LWeightMinus W V0 W'} {H1:LWeightMinus W' V1 X}
    : LWeightMinus W V X | 0.
Proof.
  rewrite <-(@lweightcastplus_eqn _ _ _ _ H).
  exists.
  rewrite <-LWeightPlusAssoc.
  rewrite (@lweightminus_eqn _ _ _ _ H1).
  apply (@lweightminus_eqn _ _ _ _ H0).
Defined.
Instance LWeightMinus_VZero{E:LEnv} {W V:LWeight}
    {H:LWeightCastZero V}
    : LWeightMinus W V W | 0.
Proof.
  rewrite <-(@lweightcastzero_eqn _ _ H).
  exists.
  apply LWeightZeroR.
Defined.
Instance LWeightMinus_Promote{E:LEnv} {W V X:LWeight}
    {H:LWeightMinus1 W V X}
    : LWeightMinus W V X | 1.
Proof.
  exists.
  apply lweightminus1_eqn.
Defined.

Instance LWeightMinus1_WPlusL{E:LEnv} {W V X W0 W1:LWeight}
    {H:LWeightCastPlus W W0 W1}
    {H0:LWeightMinus1 W0 V X}
    : LWeightMinus1 W V (X + W1) | 0.
Proof.
  rewrite <-(@lweightcastplus_eqn _ _ _ _ H).
  exists.
  rewrite LWeightPlusAssoc.
  f_equal.
  apply (@lweightminus1_eqn _ _ _ _ H0).
Defined.
Instance LWeightMinus1_WPlusR{E:LEnv} {W V X W0 W1:LWeight}
    {H:LWeightCastPlus W W0 W1}
    {H1:LWeightMinus1 W1 V X}
    : LWeightMinus1 W V (W0 + X) | 0.
Proof.
  rewrite <-(@lweightcastplus_eqn _ _ _ _ H).
  exists.
  rewrite (LWeightPlusComm V).
  rewrite <-LWeightPlusAssoc.
  f_equal.
  rewrite LWeightPlusComm.
  apply (@lweightminus1_eqn _ _ _ _ H1).
Defined.
Instance LWeightMinus1_self{E:LEnv} {W:LWeight}
    : LWeightMinus1 W W 0 | 0.
Proof.
  exists.
  apply LWeightZeroL.
Defined.

Instance LWeightAnnihil_plus{E:LEnv} {W W0 W1:LWeight}
    {H:LWeightCastPlus W W0 W1}
    {H0:LWeightAnnihil W0}
    {H1:LWeightAnnihil W1}
    : LWeightAnnihil W | 0.
Proof.
  rewrite <-lweightcastplus_eqn.
  exists.
  rewrite (@lweightannihil_eqn _ _ H0).
  rewrite (@lweightannihil_eqn _ _ H1).
  apply LWeightZeroL.
Defined.
Instance LWeightAnnihil_self{E:LEnv} {W:LWeight}
    {H:LWeightCastZero W}
    : LWeightAnnihil W | 0.
Proof.
  exists.
  symmetry; apply lweightcastzero_eqn.
Defined.

Lemma test{E:LEnv} : forall(a b c d:LWeight),
  exists e, ((c + a) + e = a + b + c)%LWeight.
Proof.
  intros a b c d.
  eexists.
  apply lweightminus_eqn.
Qed.




(*************************************************)
(*        Definition of Linear Type              *)
(*************************************************)

Delimit Scope ILL_scope with ILL.
Reserved Notation "'TT'".
Reserved Notation "A '-o' B"
  (at level 99, right associativity, y at level 200).

Record LType{E:LEnv} := {
  ltype : Type;
  lweight : ltype -> @LWeight E
}.
Arguments LType [E].
Arguments Build_LType [E] _ _.
Arguments ltype [E] _%ILL.
Arguments lweight [E] [_] _.

Coercion lweight : ltype >-> LWeight.

(* Linear Implication *)
Record LFun{E:LEnv} (A B:LType) := {
  lfun_val : ltype A -> ltype B;
  lfun_weight : @LWeight E;
  lfun_weight_eqn :
    forall x, (lfun_weight + lweight x = lweight (lfun_val x))%LWeight
}.
Arguments LFun [E] A B.
Arguments Build_LFun [E] [A] [B] _ _ _.
Arguments lfun_val [E] [A] [B] _ _.
Arguments lfun_weight [E] [A] [B] _.
Arguments lfun_weight_eqn [E] [A] [B] _ _.

Definition LImpl{E:LEnv} (A B:LType):LType := {|
  ltype := LFun A B;
  lweight := @lfun_weight _ _ _
|}.
Notation "A -o B" := (LImpl A%ILL B%ILL) : ILL_scope.

Instance LImpl_weight_decompose{E:LEnv} (A B:LType)
    (f : ltype (A -o B)) (x : ltype A)
    : LWeightCastPlus (lweight (lfun_val f x)) (lweight f) (lweight x).
Proof.
  rewrite <-lfun_weight_eqn.
  auto with typeclass_instances.
Defined.

Record LGoal{E:LEnv} (T:LType) (W:LWeight) : Type := {
  lgoal_proof : ltype T;
  lgoal_weight : W = lweight lgoal_proof
}.
Arguments LGoal [E] T%ILL W%LWeight.
Arguments Build_LGoal [E] [T] [W] _ _.
Arguments lgoal_proof [E] [T] [W] _.
Arguments lgoal_weight [E] [T] [W] _.

Notation "T [ 'using_hypotheses' W ]" :=
  (LGoal T%ILL W%LWeight)
  (at level 100,
   no associativity,
   format "'[' T '//' [ 'using_hypotheses'  W ] ']'").

Definition limpl_intro{E:LEnv} {A B:LType} {W:LWeight}
    (X : forall a : ltype A, LGoal B (W + lweight a)) :
    LGoal (A -o B) W := {|
  lgoal_proof := {|
    lfun_val a := lgoal_proof (X a);
    lfun_weight := W;
    lfun_weight_eqn a := lgoal_weight (X a)
  |} : ltype (A -o B);
  lgoal_weight := eq_refl
|}.

Definition limpl_revert{E:LEnv} {A B:LType} {W:LWeight} (x:ltype A)
    {X:LWeight} {mn:LWeightMinus W (lweight x) X}
    (H : LGoal (A -o B) X) : LGoal B W.
Proof.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof H) x
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  etransitivity; [|apply lfun_weight_eqn].
  rewrite LWeightPlusComm.
  f_equal.
  apply (@lgoal_weight _ _ _ H).
Defined.

Definition limpl_applygoal{E:LEnv} {A B:LType} {W:LWeight}
    (x:ltype (A -o B)) {X:LWeight} {mn:LWeightMinus W (lweight x) X} :
    LGoal A X -> LGoal B W.
Proof.
  intros a.
  refine {|
    lgoal_proof := lfun_val x (lgoal_proof a)
  |}.
  etransitivity; [|apply lfun_weight_eqn].
  etransitivity; [symmetry; apply lweightminus_eqn|].
  f_equal.
  apply lgoal_weight.
Defined.

Definition linear_exact{E:LEnv} {A:LType} {W:LWeight}
    (x:ltype A) {X:LWeight} {mn:LWeightMinus W (lweight x) X}
    {ann:LWeightAnnihil X} : LGoal A W.
Proof.
  refine {|
    lgoal_proof := x
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  rewrite (@lweightannihil_eqn _ _ ann).
  apply LWeightZeroL.
Defined.

Definition linear_cut{E:LEnv} (A:LType) {B:LType} {W:LWeight} (V:LWeight)
    {X:LWeight} {mn:LWeightMinus W V X}
    : LGoal (A -o B) V -> LGoal A X -> LGoal B W.
Proof.
  intros X0 X1.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof X0) (lgoal_proof X1)
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  rewrite <-lfun_weight_eqn.
  f_equal.
  - apply (@lgoal_weight _ _ _ X0).
  - apply (@lgoal_weight _ _ _ X1).
Defined.
Arguments linear_cut [E] A%ILL [B] [W] V%LWeight [X] [mn] _ _.

Definition LTensor{E:LEnv} (A B:LType) : LType := {|
  ltype := ltype A * ltype B;
  lweight x := (lweight (fst x) + lweight (snd x))%LWeight
|}.
Definition LOne{E:LEnv} : LType := {|
  ltype := unit;
  lweight := fun _ => 0%LWeight
|}.
Notation "A * B" := (LTensor A%ILL B%ILL) : ILL_scope.
Notation "1" := LOne : ILL_scope.

Definition ltensor_split{E:LEnv} {A B:LType} {W:LWeight} (V:LWeight)
    {X:LWeight} {mn:LWeightMinus W V X} :
    LGoal A V -> LGoal B X -> LGoal (A * B) W.
Proof.
  intros a b.
  refine {|
    lgoal_proof := (lgoal_proof a, lgoal_proof b) : ltype (A * B)
  |}.
  etransitivity; [symmetry; apply lweightminus_eqn|].
  simpl.
  f_equal; apply lgoal_weight.
Defined.

Definition lone_split{E:LEnv} {W:LWeight}
  {annihil:LWeightAnnihil W} : LGoal 1 W.
Proof.
  refine {|
    lgoal_proof := tt : ltype 1
  |}.
  apply lweightannihil_eqn.
Defined.

Definition ltensor_uncurry{E:LEnv} {A B C:LType} {W:LWeight} :
  LGoal (A -o B -o C) W -> LGoal (A * B -o C) W.
Proof.
  intros H.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype (A * B)) =>
        lfun_val (lfun_val (lgoal_proof H) (fst x)) (snd x);
      lfun_weight := W
    |} : ltype (A * B -o C)
  |}.
  reflexivity.
Grab Existential Variables.
  intros x; simpl.
  rewrite <-lfun_weight_eqn.
  rewrite LWeightPlusAssoc.
  f_equal.
  etransitivity; [|apply (@lfun_weight_eqn _ _ _ (lgoal_proof H))].
  f_equal.
  apply (@lgoal_weight _ _ _ H).
Defined.

Definition lone_uncurry{E:LEnv} {A:LType} {W:LWeight} :
  LGoal A W -> LGoal (1 -o A) W.
Proof.
  intros H.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype 1) => lgoal_proof H;
      lfun_weight := W
    |} : ltype (1 -o A)
  |}.
  reflexivity.
Grab Existential Variables.
  intros x; simpl.
  rewrite LWeightZeroL.
  apply lgoal_weight.
Defined.


Record LWithVal{E:LEnv} (A B:LType) := {
  lwithval_fst : ltype A;
  lwithval_snd : ltype B;
  lwithval_weight_eqn : lweight lwithval_fst = lweight lwithval_snd
}.
Arguments LWithVal [E] A%ILL B%ILL.
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
Notation "A && B" := (LWith A%ILL B%ILL) : ILL_scope.
Notation "'TT'" := LTop : ILL_scope.

Definition lwith_split{E:LEnv} {A B:LType} {W:LWeight}
  (H0 : LGoal A W) (H1 : LGoal B W) : LGoal (A && B) W.
Proof.
  refine {|
    lgoal_proof := {|
      lwithval_fst := lgoal_proof H0;
      lwithval_snd := lgoal_proof H1;
      lwithval_weight_eqn :=
        eq_trans (eq_sym (lgoal_weight H0)) (lgoal_weight H1)
    |} : ltype (A && B);
    lgoal_weight := lgoal_weight H0
  |}.
Defined.
Definition ltop_split{E:LEnv} {W:LWeight} : LGoal TT W.
Proof.
  refine {|
    lgoal_proof := W : ltype TT;
    lgoal_weight := eq_refl
  |}.
Defined.

Definition lwith_uncurry_l{E:LEnv} {A B C:LType} {W:LWeight}
  (H0 : LGoal (A -o C) W) : LGoal (A && B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(x : ltype (A && B)) =>
        lfun_val (lgoal_proof H0) (lwithval_fst x);
      lfun_weight := W
    |} : ltype (A && B -o C);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite <-lfun_weight_eqn.
  f_equal.
  apply (@lgoal_weight _ _ _ H0).
Defined.
Definition lwith_uncurry_r{E:LEnv} {A B C:LType} {W:LWeight}
  (H1 : LGoal (B -o C) W) : LGoal (A && B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun(x : ltype (A && B)) =>
        lfun_val (lgoal_proof H1) (lwithval_snd x);
      lfun_weight := W
    |} : ltype (A && B -o C);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros x; simpl.
  rewrite lwithval_weight_eqn.
  rewrite <-lfun_weight_eqn.
  f_equal.
  apply (@lgoal_weight _ _ _ H1).
Defined.

Ltac ll_cleanup :=
  rewrite ?LWeightZeroL, ?LWeightZeroR;
  repeat match goal with
  | [ x : ltype _ |- _ ] => clear x
  end.

Tactic Notation "introll" ident(x) :=
  refine (limpl_intro _); intro x; ll_cleanup.
Tactic Notation "introll" :=
  let x := fresh in introll x.
Tactic Notation "introll" ident(x0) ident(x1) :=
  introll x0; introll x1.
Tactic Notation "introll" ident(x0) ident(x1) ident(x2) :=
  introll x0; introll x1; introll x2.
Tactic Notation "introll" ident(x0) ident(x1) ident(x2) ident(x3) :=
  introll x0; introll x1; introll x2; introll x3.
Tactic Notation "introll" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) :=
  introll x0; introll x1; introll x2; introll x3; introll x4.

Tactic Notation "revertll" ident(x) :=
  refine (limpl_revert x _); ll_cleanup.

Tactic Notation "applyll" constr(x) :=
  refine (limpl_applygoal x _); ll_cleanup.

Tactic Notation "exactll" constr(x) :=
  refine (linear_exact x).

Tactic Notation "cutll" constr(A) "carrying" constr(V) :=
  refine (linear_cut A V _ _); ll_cleanup.

Tactic Notation "splitll" "carrying" constr(V) :=
  refine (ltensor_split V _ _); ll_cleanup.
Tactic Notation "splitll" :=
  (refine lone_split; ll_cleanup) ||
  (refine (lwith_split _ _); ll_cleanup) ||
  (refine ltop_split).

Tactic Notation "destructll" ident(x) "as" "[" ident(y) ident(z) "]" :=
  revertll x; refine (ltensor_uncurry _); introll y z.
Tactic Notation "destructll" ident(x) :=
  revertll x; refine (lone_uncurry _); ll_cleanup.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) "_" "]" :=
  revertll x; refine (lwith_uncurry_l _); introll y.
Tactic Notation "destructll" ident(x) "as" "[" "_" ident(z) "]" :=
  revertll x; refine (lwith_uncurry_r _); introll z.




(*************************************************)
(*                  Sample Proof                 *)
(*************************************************)

Lemma CombinatorB{E:LEnv} (A B C:LType) :
  (B -o C) -o (A -o B) -o (A -o C)
  [using_hypotheses 0].
Proof.
  introll x.
  introll y.
  introll z.
  applyll x.
  applyll y.
  exactll z.
Qed.

Lemma CombinatorC{E:LEnv} (A B C:LType) :
  (A -o B -o C) -o (B -o A -o C)
  [using_hypotheses 0].
Proof.
  introll x.
  introll y.
  introll z.
  applyll (lfun_val x z).
  exactll y.
Qed.

Lemma TensorComm{E:LEnv} (A B:LType) :
  A * B -o B * A
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x y].
  splitll carrying y.
  - exactll y.
  - exactll x.
Qed.

Lemma WithComm{E:LEnv} (A B:LType) :
  A && B -o B && A
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  - destructll x as [_ x].
    exactll x.
  - destructll x as [x _].
    exactll x.
Qed.
