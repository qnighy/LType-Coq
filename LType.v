(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base LGoal.


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

Definition LPlus{E:LEnv} (A B:LType) : LType := {|
  ltype := ltype A + ltype B;
  lweight x :=
    match x with
    | inl xl => lweight xl
    | inr xr => lweight xr
    end
|}.
Definition LZero{E:LEnv} : LType := {|
  ltype := Empty_set;
  lweight x := match x with end
|}.
Notation "A + B" := (LPlus A%ILL B%ILL) : ILL_scope.
Notation "0" := LZero : ILL_scope.

Definition lplus_left{E:LEnv} {A B:LType} {W:LWeight}
    (H0 : LGoal A W) : LGoal (A + B) W.
Proof.
  refine {|
    lgoal_proof := inl (lgoal_proof H0) : ltype (A + B)
  |}.
  apply lgoal_weight.
Defined.
Definition lplus_right{E:LEnv} {A B:LType} {W:LWeight}
    (H1 : LGoal B W) : LGoal (A + B) W.
Proof.
  refine {|
    lgoal_proof := inr (lgoal_proof H1) : ltype (A + B)
  |}.
  apply lgoal_weight.
Defined.

Definition lplus_uncurry{E:LEnv} {A B C:LType} {W:LWeight}
    (H0 : LGoal (A -o C) W) (H1 : LGoal (B -o C) W) : LGoal (A + B -o C) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype (A + B)) =>
        match x with
        | inl xl => lfun_val (lgoal_proof H0) xl
        | inr xr => lfun_val (lgoal_proof H1) xr
        end;
      lfun_weight := W
    |} : ltype (A + B -o C);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros [xl|xr]; simpl.
  - rewrite <-lfun_weight_eqn.
    f_equal.
    apply (@lgoal_weight _ _ _ H0).
  - rewrite <-lfun_weight_eqn.
    f_equal.
    apply (@lgoal_weight _ _ _ H1).
Defined.
Definition lzero_uncurry{E:LEnv} {A:LType} {W:LWeight}
    : LGoal (0 -o A) W.
Proof.
  refine {|
    lgoal_proof := {|
      lfun_val := fun (x:ltype 0) =>
        match x with end;
      lfun_weight := W
    |} : ltype (0 -o A);
    lgoal_weight := eq_refl
  |}.
Grab Existential Variables.
  intros [].
Defined.

Record LOfcourseVal{E:LEnv} (A:LType) := {
  lofcourseval : ltype A;
  lofcourseval_nil : lweight lofcourseval = 0%LWeight
}.
Arguments LOfcourseVal [E] A%ILL.
Arguments Build_LOfcourseVal [E] [A] _ _.
Arguments lofcourseval [E] [A] _.
Arguments lofcourseval_nil [E] [A] _.

Definition LOfcourse{E:LEnv} (A:LType) : LType := {|
  ltype := LOfcourseVal A;
  lweight := fun _ => 0%LWeight
|}.
Notation "! A" := (LOfcourse A%ILL) : ILL_scope.

Instance LOfcouse_weight_decompose{E:LEnv} (A:LType)
    (x : ltype (!A))
    : LWeightCastZero x.
Proof.
  exists.
  reflexivity.
Defined.

Definition lofcourse_promote{E:LEnv} {A:LType}
    {W:LWeight} {annihil:LWeightAnnihil W}
    (H0 : LGoal A 0) : LGoal (!A) W.
Proof.
  refine {|
    lgoal_proof := {|
      lofcourseval := lgoal_proof H0;
      lofcourseval_nil := eq_sym (lgoal_weight H0)
    |} : ltype (!A)
  |}.
  apply lweightannihil_eqn.
Defined.

Definition lofcourse_derelict{E:LEnv} {A B:LType} {W:LWeight}
    (a : ltype (!A))
    (H0 : LGoal (A -o B) W) : LGoal B W.
Proof.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof H0) (lofcourseval a)
  |}.
  rewrite <-lfun_weight_eqn.
  rewrite lofcourseval_nil, LWeightZeroL.
  apply (@lgoal_weight _ _ _ H0).
Defined.

Tactic Notation "exactll" constr(x) :=
  refine (linear_exact x).

Tactic Notation "cutll" constr(A) "carrying" constr(V) :=
  refine (linear_cut A V _ _); ll_cleanup.

Tactic Notation "splitll" "carrying" constr(V) :=
  refine (ltensor_split V _ _); ll_cleanup.
Tactic Notation "splitll" :=
  (refine lone_split; ll_cleanup) ||
  (refine (lwith_split _ _); ll_cleanup) ||
  (refine ltop_split) ||
  (refine (lofcourse_promote _); ll_cleanup).

Tactic Notation "leftll" :=
  refine (lplus_left _); ll_cleanup.
Tactic Notation "rightll" :=
  refine (lplus_right _); ll_cleanup.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) ident(z) "]" :=
  revertll x; refine (ltensor_uncurry _); introll y z.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) "_" "]" :=
  revertll x; refine (lwith_uncurry_l _); introll y.
Tactic Notation "destructll" ident(x) "as" "[" "_" ident(z) "]" :=
  revertll x; refine (lwith_uncurry_r _); introll z.

Tactic Notation "destructll" ident(x) "as" "[" ident(y) "|" ident(z) "]" :=
  revertll x; refine (lplus_uncurry _ _); [introll y | introll z].
Tactic Notation "destructll" ident(x) "as" "[" "]" :=
  revertll x; refine lzero_uncurry.

Tactic Notation "destructll" ident(x) :=
  (refine (lofcourse_derelict x _); clear x; introll x) ||
  (revertll x; refine (lone_uncurry _); ll_cleanup) ||
  let y := fresh in let z := fresh in
  destructll x as [y z] ||
  destructll x as [y _] ||
  destructll x as [_ y] ||
  destructll x as [y | y] ||
  destructll x as [].
  


(*************************************************)
(*                  Sample Proof                 *)
(*************************************************)

Lemma CombinatorB{E:LEnv} (A B C:LType) :
  ((B -o C) -o (A -o B) -o (A -o C))
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
  ((A -o B -o C) -o (B -o A -o C))
  [using_hypotheses 0].
Proof.
  introll x.
  introll y.
  introll z.
  applyll (lfun_val x z).
  exactll y.
Qed.

Lemma TensorComm{E:LEnv} (A B:LType) :
  (A * B -o B * A)
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x y].
  splitll carrying y.
  - exactll y.
  - exactll x.
Qed.

Lemma WithComm{E:LEnv} (A B:LType) :
  (A && B -o B && A)
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  - destructll x as [_ x].
    exactll x.
  - destructll x as [x _].
    exactll x.
Qed.

Lemma PlusComm{E:LEnv} (A B:LType) :
  (A + B -o B + A)
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x | x].
  - rightll.
    exactll x.
  - leftll.
    exactll x.
Qed.

Lemma OfcDiggL{E:LEnv} (A:LType) :
  ((!!A) -o !A)
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  destructll x.
  destructll x.
  exactll x.
Qed.

Lemma OfcDiggR{E:LEnv} (A:LType) :
  ((!A) -o !!A)
  [using_hypotheses 0].
Proof.
  introll x.
  splitll.
  splitll.
  destructll x.
  exactll x.
Qed.

Lemma TensorPlusCommL{E:LEnv} (A B C:LType) :
  (A * B + A * C -o A * (B + C))
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x | x].
  - destructll x as [x y].
    splitll carrying x.
    + exactll x.
    + leftll.
      exactll y.
  - destructll x as [x y].
    splitll carrying x.
    + exactll x.
    + rightll.
      exactll y.
Qed.

Lemma TensorPlusCommR{E:LEnv} (A B C:LType) :
  (A * (B + C) -o A * B + A * C)
  [using_hypotheses 0].
Proof.
  introll x.
  destructll x as [x y].
  destructll y as [y | y].
  - leftll.
    splitll carrying x.
    + exactll x.
    + exactll y.
  - rightll.
    splitll carrying x.
    + exactll x.
    + exactll y.
Qed.

Lemma ExponentialLawL{E:LEnv} (A B:LType) :
  (!(A && B) -o (!A) * (!B))
  [using_hypotheses 0].
Proof.
  introll x.
  splitll carrying 0%LWeight.
  - splitll.
    destructll x.
    destructll x as [x _].
    exactll x.
  - splitll.
    destructll x.
    destructll x as [_ x].
    exactll x.
Qed.
Lemma ExponentialLawR{E:LEnv} (A B:LType) :
  ((!A) * (!B) -o !(A && B))
  [using_hypotheses 0].
Proof.
  introll x.
Qed.
