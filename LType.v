(* Author: Masaki Hara, 2014 *)
(* Linear Logic Toy for Coq *)
Require Export LWeight LType_base LGoal.
Require Export LTensor LWith LPlus LOfcourse LForall LExists.

Ltac splitll_base ::=
  splitll_base_tensor ||
  apply LWithConstructor ||
  apply LTopConstructor ||
  apply LOfcConstructor ||
  fail "Constructor not found".

Ltac leftll_base ::=
  apply LPlusConstructorL ||
  fail "Constructor not found".

Ltac rightll_base ::=
  apply LPlusConstructorR ||
  fail "Constructor not found".

Ltac destructll_base ::=
  destructll_base_tensor ||
  apply LPlusDestructor ||
  apply LZeroDestructor ||
  apply LOfcDestructor ||
  apply LExistsDestructor ||
  fail "Destructor not found".

Ltac destructll_left_base ::=
  apply LWithDestructorL ||
  fail "Destructor not found".

Ltac destructll_right_base ::=
  apply LWithDestructorR ||
  fail "Destructor not found".

Ltac clonell_base ::=
  apply LOfcClone ||
  fail "Destructor not found".

Ltac clearll_base ::=
  apply LOfcClear ||
  fail "Destructor not found".

Ltac introll_base x ::=
  introll_base_limpl x ||
  (apply LForallIntroduction; intros x) ||
  fail "Linear Introduction Failed".

Ltac existsll_base x ::=
  apply (LExistsConstructor x) ||
  fail "Constructor not found".

Ltac ll_fold_weights ::=
  repeat lazymatch goal with
  | [ |- ?G ] =>
      lazymatch G with
      | context ctx [@lfun_weight ?E ?A ?B ?f] =>
          let Gnew := context ctx [@lweight E (@LImpl E A B) f] in
          change Gnew
      | context ctx [@lweight ?E (@LTensor _ ?A ?B) (?x, ?y)] =>
          let Gnew := context ctx [(@lweight E A x + @lweight E B y)%LWeight] in
          change Gnew
      end
  end.

Global Open Scope LL_goal_scope.