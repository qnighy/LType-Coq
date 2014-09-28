(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Import LWeight LType_base.

(*************************************************)
(*   Virtual Goal for solving Linear Logic       *)
(*************************************************)

Record LGoal{E:LEnv} (T:LType) (W:LWeight) : Type := {
  lgoal_proof :> ltype T;
  lgoal_weight_eqn : LWeightEquation W (lweight lgoal_proof)
}.
Arguments LGoal [E] T%LL W%LWeight.
Arguments Build_LGoal [E] [T] [W] _ _.
Arguments lgoal_proof [E] [T] [W] _.
Arguments lgoal_weight_eqn [E] [T] [W] _.
Existing Instance lgoal_weight_eqn.

Instance lgoal_weight_self{E:LEnv} {T:LType} {W:LWeight}
    (H:LGoal T W) : LWeightCastSelf (lweight (lgoal_proof H)) W.
Proof.
  exists.
  apply lweight_eqn, lgoal_weight_eqn.
Defined.

Class QuantifiedLType{E:LEnv} {T:Type} {TT:LType} (f:T) := {
  ltype_unfold_quantifier : ltype TT
}.
Arguments QuantifiedLType [E] [T] [TT] f.
Arguments Build_QuantifiedLType [E] [T] [TT] [f] _.
Arguments ltype_unfold_quantifier [E] [T] [TT] f [_].
Instance QuantifiedLTypeSelf{E:LEnv} {TT:LType} (f:ltype TT) :
  @QuantifiedLType _ (ltype TT) TT f := {|
  ltype_unfold_quantifier := f
|}.
Instance QuantifiedLTypeForall{E:LEnv} {A:Type} {T:A->Type} {TT:LType}
    (f:forall a, T a)
    {a:A} {H:@QuantifiedLType E (T a) TT (f a)}
    : @QuantifiedLType E (forall a, T a) TT f := {|
  ltype_unfold_quantifier := ltype_unfold_quantifier (f a)
|}.

Fixpoint implication_list(T:list Type) (G:Type) : Type :=
  match T with
  | nil => G
  | cons Th Tl => Th -> implication_list Tl G
  end.

Fixpoint implication_list_map{T:list Type} {A B:Type}
    (f : A -> B) : implication_list T A -> implication_list T B :=
  match T with
  | nil => f
  | cons Th Tl => fun g x => implication_list_map f (g x)
  end.

Definition LHinted{E:LEnv} (l:list (nat * LWeight)) (G:Type) := G.
Arguments LHinted [E] l%LWeight G.

Class LHintedApp{E:LEnv} (n:nat) (l:list (nat * LWeight))
                (Impls:list Type) (G:Type) := {
  lhinted_app_val : implication_list Impls G
}.
Arguments LHintedApp [E] n l%LWeight Impls G.
Arguments Build_LHintedApp [E] n l%LWeight Impls [G] _.
Arguments lhinted_app_val [E] [n] [l] [Impls] [G] _.

Instance lgoal_autoapply_self{E:LEnv} {T:LType} {n:nat}
   {l:list (nat * LWeight)} {a:ltype T}
   : LHintedApp n l nil (LGoal T (0 + lweight a)%LWeight).
Proof.
  exists.
  refine {|
    lgoal_proof := a
  |}.
Defined.

Definition lgoal_autoapply_take{E:LEnv} {A B T:LType} {n:nat}
  {l:list (nat * LWeight)} {W:LWeight} (HintWeight:LWeight)
  {f:ltype (A -o B)}
  {Impls:list Type}
  {H:forall a:LGoal A HintWeight,
       LHintedApp (S n) l Impls (LGoal T (W + lweight (f a))%LWeight)}
  : LHintedApp n l (LGoal A HintWeight :: Impls)%list
                      (LGoal T (W + HintWeight + lweight f)%LWeight).
Proof.
  exists.
  intros a.
  generalize (lhinted_app_val (H a)); clear H.
  apply implication_list_map.
  intros H.
  refine {| lgoal_proof := H |}.
Defined.

(* manual instance for lgoal_autoapply_take. *)
Hint Extern 1 (LHintedApp ?n ?l _ (LGoal ?T (_ + lweight ?f)%LWeight)) =>
  lazymatch l with
  | context ctx [(n,?W)] =>
      (* idtac "weight is " W; *)
      eapply (lgoal_autoapply_take W)
  | _ =>
      (* idtac "hint not found"; *)
      eapply (lgoal_autoapply_take (lweight_hole _))
  end
  : typeclass_instances.


Definition lhinted_init{E:LEnv} {G:Type}
    (H : LHinted nil G) : G := H.

Definition lhinted_add{E:LEnv} {G:Type} {l:list (nat * LWeight)}
    (n:nat) (W:LWeight)
    (H : LHinted ((n,W)::l)%list G) : LHinted l G := H.

Definition lgoal_autoapply_getvalue{E:LEnv} {l:list (nat * LWeight)}
    {T:LType} {W:LWeight} {X:LWeight} {A:LType} (a:ltype A)
    {Tl:list Type}
    {H:LHintedApp 1 l Tl (LGoal T (X + a))}
    (H0:(W = X + a)%LWeight)
    (Next:implication_list Tl (LGoal T W) -> LGoal T W)
    : LHinted l (LGoal T W).
Proof.
  apply Next; clear Next.
  generalize (lhinted_app_val H); clear H.
  apply implication_list_map.
  intros H.
  refine {|
    lgoal_proof := lgoal_proof H
  |}.
  rewrite H0; refine _.
Defined.

Ltac lweight_solve_equation :=
  lazymatch goal with
  | [ |- ?W = ?V ] =>
      lazymatch V with
      | context ctx [lweight_hole ?h] =>
          (* idtac "found 1 or more hole"; *)
          lazymatch context ctx [0%LWeight] with
          | context ctx2 [lweight_hole ?h2] =>
              (* idtac "found 2 or more hole"; *)
              fail 2 "Linear application failed: "
                     "there are more than one subgoal "
                     "and I can't determine where to "
                     "carry hypotheses. "
                     "Use 'carrying' tacticals to "
                     "specify that."
          | _ =>
              (* idtac "found 1 hole"; *)
              (
                let VC := context ctx [0%LWeight] in
                let H := fresh "H" in
                assert (H := _ : LWeightMinus W VC h);
                rewrite lweight_hole_unfold;
                refine (lweight_eqn _);
                fail
              ) ||
              fail 2 "Linear application failed: "
                     "cannot solve a weight equation."
          end
      | _ =>
          (* idtac "found no hole"; *)
          refine (lweight_eqn _);
          fail 2 "Linear application failed: "
                 "cannot solve a weight equation."
      end
  end.

Ltac lhinted_conditional_init :=
  lazymatch goal with
  | [ |- LHinted _ _ ] => idtac
  | _ => apply lhinted_init
  end.

Ltac lhinted_add n W :=
  lhinted_conditional_init;
  apply (lhinted_add n W).

Tactic Notation (at level 2)
    tactic2(t) "carrying" constr(W) "into" constr(n) :=
  lhinted_add n (W%LWeight);
  t.

Ltac ll_fold_weights := idtac.

Ltac ll_cleanup :=
  repeat (
    rewrite <-!lweightcastzero_eqn ||
    rewrite !LWeightZeroL ||
    rewrite !LWeightZeroR);
  repeat match goal with
  | [ x : ltype ?A |- _ ] => clear x
  end;
  ll_fold_weights.

Ltac applyll_base f :=
  lhinted_conditional_init;
  eapply (lgoal_autoapply_getvalue (ltype_unfold_quantifier f));
    [ lweight_solve_equation
    | rewrite ?lweight_hole_unfold;
      let H := fresh "H" in
      intros H; apply H; clear H;
      ll_cleanup ].

Example applyll_base_test{E:LEnv} {A B C D:LType}
  (x:ltype A) (y:ltype B) (z:ltype (A -o B -o C -o D)) : LGoal (C -o D) (x+y+z).
Proof.
  (applyll_base z)
    carrying x into 1.
  - refine {| lgoal_proof := x |}.
  - refine {| lgoal_proof := y |}.
Defined.

Definition limpl_intro{E:LEnv} {A B:LType} {W:LWeight}
    (X : forall a : ltype A, LGoal B (W + lweight a)) :
    LGoal (A -o B) W := {|
  lgoal_proof := {|
    lfun_val a := lgoal_proof (X a);
    lfun_weight := W;
    lfun_weight_eqn a := lweight_eqn _
  |} : ltype (A -o B)
|}.

Definition limpl_revert{E:LEnv} {A B:LType} {W:LWeight} (x:ltype A)
    {X:LWeight} {mn:LWeightMinus W (lweight x) X}
    (H : LGoal (A -o B) X) : LGoal B W.
Proof.
  refine {|
    lgoal_proof := lfun_val (lgoal_proof H) x;
    lgoal_weight_eqn := {| lweight_eqn := _ |}
  |}.
  rewrite <-lweightminus_eqn.
  apply (lweight_eqn _).
Defined.

Notation "'ILL' |- T" := (LGoal T%LL 0%LWeight) (at level 200)
    : LL_goal_scope.
Notation "'ILL' |- T [ 'using_hypotheses' W  ]" :=
    (LGoal T%LL W%LWeight) (at level 200) : LL_goal_scope.

Ltac introll_base_limpl x :=
  (refine (limpl_intro _); intro x) ||
  intro x.

Ltac introll_base x :=
  introll_base_limpl x ||
  fail "Linear Introduction Failed".

Tactic Notation "introll" ident(x) :=
  introll_base x; ll_cleanup.
Ltac introsll_auto :=
  let x := fresh "H" in introll x; try introsll_auto.
Tactic Notation "introsll" := introsll_auto.
Tactic Notation "introsll" ident(x0) :=
  introll x0.
Tactic Notation "introsll" ident(x0) ident(x1) :=
  introll x0; introll x1.
Tactic Notation "introsll" ident(x0) ident(x1) ident(x2) :=
  introll x0; introll x1; introll x2.
Tactic Notation "introsll" ident(x0) ident(x1) ident(x2) ident(x3) :=
  introll x0; introll x1; introll x2; introll x3.
Tactic Notation "introsll" ident(x0) ident(x1) ident(x2) ident(x3) ident(x4) :=
  introll x0; introll x1; introll x2; introll x3; introll x4.

Tactic Notation "revertll" constr(x) :=
  refine (limpl_revert x _); ll_cleanup.

Tactic Notation "applyll" constr(x) :=
  applyll_base x.

Local Open Scope LL_goal_scope.
Example CombinatorB{E:LEnv} (A B C:LType) :
  (ILL |- (B -o C) -o (A -o B) -o (A -o C)).
Proof.
  introsll.
  applyll H.
  applyll H0.
  applyll H1.
Defined.

Example CombinatorC{E:LEnv} (A B C:LType) :
  (ILL |- (A -o B -o C) -o (B -o A -o C)).
Proof.
  introsll x y z.
  applyll (x z).
  applyll y.
Defined.
Local Close Scope LL_goal_scope.

Ltac splitll_base := fail "Constructor not found".
Ltac leftll_base := fail "Constructor not found".
Ltac rightll_base := fail "Constructor not found".
Ltac existsll_base x := fail "Constructor not found".

Tactic Notation "splitll" := splitll_base; ll_cleanup.
Tactic Notation "leftll" := leftll_base; ll_cleanup.
Tactic Notation "rightll" := rightll_base; ll_cleanup.
Tactic Notation "existsll" := splitll_base; ll_cleanup.
Tactic Notation "existsll" constr(x) := existsll_base x; ll_cleanup.

Ltac destructll_base := fail "Destructor not found".
Ltac destructll_left_base := fail "Destructor not found".
Ltac destructll_right_base := fail "Destructor not found".
Ltac clonell_base := fail "Destructor not found".
Ltac clearll_base := fail "Destructor not found".

Tactic Notation "destructll" constr(x) :=
  (* TODO stop introsll at an appropriate point *)
  revertll x; destructll_base; introsll.
Tactic Notation "destructll" constr(x) "as" "[" "]" :=
  revertll x; destructll_base; ll_cleanup.
Tactic Notation "destructll" constr(x) "as" "[" ident(y) "]" :=
  revertll x; destructll_base; introsll y.
Tactic Notation "destructll" constr(x) "as" "[" ident(y) ident(z) "]" :=
  revertll x; destructll_base; introsll y z.

Tactic Notation "destructll" constr(x) "as" "[" ident(y) "|" ident(z) "]" :=
  revertll x; destructll_base; [introsll y | introsll z].

Tactic Notation "destructll" constr(x) "as" "[" ident(y) "_" "]" :=
  revertll x; destructll_left_base; introsll y.
Tactic Notation "destructll" constr(x) "as" "[" "_" ident(z) "]" :=
  revertll x; destructll_right_base; introsll z.

Tactic Notation "clonell" constr(x) "as" "[" ident(y) ident(z) "]" :=
  revertll x; clonell_base; introsll y z.
Tactic Notation "clonell" constr(x) "into" ident(y) :=
  revertll x; clonell_base; introsll x y.
Tactic Notation "clearll" constr(x) :=
  revertll x; clearll_base; ll_cleanup.