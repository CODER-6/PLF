(** * Equiv: Program Equivalence *)
(** * Equiv: 程序等价性 *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import EqNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

(** *** Before You Get Started:
(** *** 开始之前：

    - Create a fresh directory for this volume. (Do not try to mix the
      files from this volume with files from _Logical Foundations_ in
      the same directory: the result will not make you happy.)  You
      can either start with an empty directory and populate it with
      the files listed below, or else download the whole PLF zip file
      and unzip it.
    - 为本卷创建一个新目录。（不要试图将本卷的文件与《逻辑基础》的文件
      混合在同一个目录中：结果会让你不高兴。）你可以从空目录开始，
      填充下面列出的文件，或者下载整个PLF压缩文件并解压。

    - The new directory should contain at least the following files:
         - [Imp.v] (make sure it is the one from the PLF distribution,
           not the one from LF: they are slightly different);
         - [Maps.v] (ditto)
         - [Equiv.v] (this file)
         - [_CoqProject], containing the following line:

           -Q . PLF
    - 新目录应至少包含以下文件：
         - [Imp.v]（确保是PLF发行版中的版本，而不是LF中的：它们略有不同）；
         - [Maps.v]（同上）
         - [Equiv.v]（本文件）
         - [_CoqProject]，包含以下行：

           -Q . PLF

    - If you see errors like this...

             Compiled library PLF.Maps (in file
             /Users/.../plf/Maps.vo) makes inconsistent assumptions
             over library Coq.Init.Logic

      ... it may mean something went wrong with the above steps.
      Doing "[make clean]" (or manually removing everything except
      [.v] and [_CoqProject] files) may help.
    - 如果你看到这样的错误...

             Compiled library PLF.Maps (in file
             /Users/.../plf/Maps.vo) makes inconsistent assumptions
             over library Coq.Init.Logic

      ...这可能意味着上述步骤出了问题。执行"[make clean]"
     （或手动删除除[.v]和[_CoqProject]文件之外的所有内容）可能会有帮助。

    - If you are using VSCode with the VSCoq extension, you'll then
      want to open a new window in VSCode, click [Open Folder > plf],
      and run [make].  If you get an error like "Cannot find a
      physical path..." error, it may be because you didn't open plf
      directly (you instead opened a folder containing both lf and
      plf, for example). *)
    - 如果你使用带有VSCoq扩展的VSCode，那么你需要在VSCode中打开一个新窗口，
      点击[Open Folder > plf]，然后运行[make]。如果你得到类似
      "Cannot find a physical path..."的错误，可能是因为你没有直接打开plf
     （例如，你打开了一个同时包含lf和plf的文件夹）。 *)

(** *** Advice for Working on Exercises:

    - Most of the Coq proofs we ask you to do in this chapter are
      similar to proofs that we've provided.  Before starting to work
      on exercises, take the time to work through our proofs (both
      informally and in Coq) and make sure you understand them in
      detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them by random
      experimentation or following your nose.  You need to start with
      an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter can get
      pretty long if you try to write out all the cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)
(** * 行为等价性 *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language -- in particular, assignment -- we need to
    consider the role of mutable state and develop a more
    sophisticated notion of correctness, which we'll call _behavioral
    equivalence_. *)
(** 在前面的章节中，我们研究了一个非常简单的程序变换的正确性：
    [optimize_0plus]函数。我们考虑的编程语言是算术表达式语言的第一个版本
    —— 没有变量 —— 所以在那种情况下，定义程序变换正确的含义非常容易：
    它应该总是产生一个与原始程序求值结果相同的程序。

    要讨论完整Imp语言程序变换的正确性 —— 特别是赋值 —— 我们需要考虑
    可变状态的作用，并开发一个更复杂的正确性概念，我们称之为_行为等价性_。 *)

(** For example:
      - [X + 2] is behaviorally equivalent to [1 + X + 1]
      - [X - X] is behaviorally equivalent to [0]
      - [(X - 1) + 1] is _not_ behaviorally equivalent to [X]   *)
(** 例如：
      - [X + 2] 在行为上等价于 [1 + X + 1]
      - [X - X] 在行为上等价于 [0]
      - [(X - 1) + 1] _不_在行为上等价于 [X]   *)

(* ================================================================= *)
(** ** Definitions *)
(** ** 定义 *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear: Two [aexp]s or [bexp]s are "behaviorally equivalent" if
    they evaluate to the same result in every state. *)
(** 对于带有变量的[aexp]和[bexp]，我们想要的定义很清楚：
    如果两个[aexp]或[bexp]在每个状态下都求值为相同的结果，
    那么它们是"行为等价的"。 *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)
(** 这里是算术和布尔表达式等价性的一些简单例子。 *)

Theorem aequiv_example:
  aequiv
    <{ X - X }>
    <{ 0 }>.
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example:
  bequiv
    <{ X - X = 0 }>
    <{ true }>.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We
    can't simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!

    What we need instead is this: two commands are behaviorally
    equivalent if, for any given starting state, they either (1) both
    diverge or (2) both terminate in the same final state.  A compact
    way to express this is "if the first one terminates in a
    particular state then so does the second, and vice versa." *)
(** 对于命令，情况稍微复杂一些。我们不能简单地说"如果两个命令在相同的初始状态下
    启动时都求值到相同的结束状态，那么它们在行为上等价"，因为某些命令在某些
    起始状态下运行时，根本不会在任何最终状态中终止！

    我们需要的是：对于任何给定的起始状态，如果两个命令要么(1)都发散，
    要么(2)都在相同的最终状态中终止，那么它们在行为上等价。
    表达这一点的简洁方式是"如果第一个在特定状态中终止，那么第二个也是如此，
    反之亦然。" *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(** We can also define an asymmetric variant of this relation: We say
    that [c1] _refines_ [c2] if they produce the same final states
    _when [c1] terminates_ (but [c1] may not terminate in some cases
    where [c2] does). *)
(** 我们也可以定义这个关系的不对称变体：我们说[c1]_细化_[c2]，
    如果_当[c1]终止时_它们产生相同的最终状态（但[c1]可能在[c2]终止的
    某些情况下不终止）。 *)

Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** Simple Examples *)
(** ** 简单例子 *)

(** For examples of command equivalence, let's start by looking at
    a trivial program equivalence involving [skip]: *)
(** 对于命令等价性的例子，让我们从一个涉及[skip]的简单程序等价性开始： *)

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    + apply E_Skip.
    + assumption.
Qed.

(** **** Exercise: 2 stars, standard (skip_right)

    Prove that adding a [skip] after a command results in an
    equivalent program *)
(** **** 练习：2星，标准 (skip_right)

    证明在命令后添加[skip]会产生等价的程序 *)

Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  intros c st st'.
  split; intros H.
  - inversion H; subst.
    inversion H5. subst.
    assumption.
  - apply E_Seq with st'.
    +assumption.
    +apply E_Skip.
  Show Proof. 
Qed.

(** [] *)

(** Similarly, here is a simple equivalence that optimizes [if]
    commands: *)
(** 类似地，这里是一个优化[if]命令的简单等价性： *)

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + assumption.
    + discriminate.
  - (* <- *)
    apply E_IfTrue.
    + reflexivity.
    + assumption.  Qed.

(** Of course, no (human) programmer would write a conditional whose
    condition is literally [true].  But they might write one whose
    condition is _equivalent_ to true:

    _Theorem_: If [b] is equivalent to [true], then [if b then c1
    else c2 end] is equivalent to [c1].
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [st =[
       if b then c1 else c2 end ]=> st'] then [st =[ c1 ]=> st'].

       Proceed by cases on the rules that could possibly have been
       used to show [st =[ if b then c1 else c2 end ]=> st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule in the derivation of [st =[ if b
         then c1 else c2 end ]=> st'] was [E_IfTrue].  We then have,
         by the premises of [E_IfTrue], that [st =[ c1 ]=> st'].
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [st =[ if b then c1 else c2 end ]=> st'] was [E_IfFalse].
         We then know that [beval st b = false] and [st =[ c2 ]=> st'].

         Recall that [b] is equivalent to [true], i.e., forall [st],
         [beval st b = beval st <{true}> ].  In particular, this means
         that [beval st b = true], since [beval st <{true}> = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if
       [st =[ c1 ]=> st'] then
       [st =[ if b then c1 else c2 end ]=> st'].

       Since [b] is equivalent to [true], we know that [beval st b] =
       [beval st <{true}> ] = [true].  Together with the assumption that
       [st =[ c1 ]=> st'], we can apply [E_IfTrue] to derive
       [st =[ if b then c1 else c2 end ]=> st'].  []

   Here is the formal version of this proof: *)
(** 当然，没有（人类）程序员会写一个条件字面上是[true]的条件语句。
    但他们可能会写一个条件_等价于_true的语句：

    _定理_：如果[b]等价于[true]，那么[if b then c1 else c2 end]等价于[c1]。
   _证明_：

     - ([->]) 我们必须证明，对于所有[st]和[st']，如果[st =[
       if b then c1 else c2 end ]=> st']，那么[st =[ c1 ]=> st']。

       对可能用来证明[st =[ if b then c1 else c2 end ]=> st']的规则进行分类讨论，
       即[E_IfTrue]和[E_IfFalse]。

       - 假设[st =[ if b then c1 else c2 end ]=> st']推导中的最终规则是[E_IfTrue]。
         那么根据[E_IfTrue]的前提，我们有[st =[ c1 ]=> st']。
         这正是我们要证明的。

       - 另一方面，假设[st =[ if b then c1 else c2 end ]=> st']推导中的最终规则
         是[E_IfFalse]。那么我们知道[beval st b = false]和[st =[ c2 ]=> st']。

         回忆[b]等价于[true]，即对所有[st]，[beval st b = beval st <{true}> ]。
         特别地，这意味着[beval st b = true]，因为[beval st <{true}> = true]。
         但这是一个矛盾，因为[E_IfFalse]要求[beval st b = false]。
         因此，最终规则不可能是[E_IfFalse]。

     - ([<-]) 我们必须证明，对于所有[st]和[st']，如果[st =[ c1 ]=> st']，
       那么[st =[ if b then c1 else c2 end ]=> st']。

       由于[b]等价于[true]，我们知道[beval st b] = [beval st <{true}> ] = [true]。
       结合假设[st =[ c1 ]=> st']，我们可以应用[E_IfTrue]来推导
       [st =[ if b then c1 else c2 end ]=> st']。 []

   这是此证明的形式化版本： *)

Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_false) *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H; subst.
    + (* b 求值为 true *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5. inversion H5.
    + (* b 求值为 false *)
      assumption.
  - (* <- *)
    apply E_IfFalse.
    +unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity.
    +assumption.
Qed.


(** **** Exercise: 3 stars, standard (swap_if_branches)

    Show that we can swap the branches of an [if] if we also negate its
    condition. *)
(** **** 练习：3星，标准 (swap_if_branches)

    证明如果我们同时否定条件，我们可以交换[if]的分支。 *)

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros b e1 e2.
  split; intros H.
  - inversion H; subst.
    +apply E_IfFalse.
      ++unfold bequiv in H5. simpl.
        rewrite H5. reflexivity.
      ++assumption.
    +apply E_IfTrue.
      ++unfold bequiv in H5. simpl.
        rewrite H5. reflexivity.
      ++assumption.
  - inversion H; subst.
    +apply E_IfFalse.
      ++simpl in H5.
        apply negb_true_iff.
        assumption.
      ++assumption.
    +subst.
      apply E_IfTrue.
      ++simpl in H5.
        apply negb_false_iff.
        assumption.
      ++assumption.
Qed.
(** [] *)

(** For [while] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [false] is equivalent to [skip],
    while a loop whose guard is equivalent to [true] is equivalent to
    [while true do skip end] (or any other non-terminating program). *)
(** 对于[while]循环，我们可以给出类似的一对定理。守卫等价于[false]的循环
    等价于[skip]，而守卫等价于[true]的循环等价于[while true do skip end]
    （或任何其他不终止的程序）。 *)

(** The first of these facts is easy. *)
(** 第一个事实很容易证明。 *)

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. discriminate.
  - (* <- *)
    inversion H. subst.
    apply E_WhileFalse.
    apply Hb.  Qed.

(** **** Exercise: 2 stars, advanced, optional (while_false_informal)

    Write an informal proof of [while_false].

(* FILL IN HERE *)
*)
(** **** 练习：2星，高级，可选 (while_false_informal)

    写出[while_false]的非形式化证明。

(* 在此填写 *)
*)
(** [] *)

(** To prove the second fact, we need an auxiliary lemma stating that
    [while] loops whose guards are equivalent to [true] never
    terminate. *)
(** 要证明第二个事实，我们需要一个辅助引理，说明守卫等价于[true]的
    [while]循环永远不会终止。 *)

(** _Lemma_: If [b] is equivalent to [true], then it cannot be
    the case that [st =[ while b do c end ]=> st'].

    _Proof_: Suppose that [st =[ while b do c end ]=> st'].  We show,
    by induction on a derivation of [st =[ while b do c end ]=> st'],
    that this assumption leads to a contradiction. The only two cases
    to consider are [E_WhileFalse] and [E_WhileTrue], the others
    are contradictory.

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileFalse].  Then by assumption [beval st b = false].  But
      this contradicts the assumption that [b] is equivalent to
      [true].

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileTrue].  We must have that:

      1. [beval st b = true],
      2. there is some [st0] such that [st =[ c ]=> st0] and
         [st0 =[ while b do c end ]=> st'],
      3. and we are given the induction hypothesis that
         [st0 =[ while b do c end ]=> st'] leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)
(** _引理_：如果[b]等价于[true]，那么不可能有[st =[ while b do c end ]=> st']。

    _证明_：假设[st =[ while b do c end ]=> st']。我们通过对
    [st =[ while b do c end ]=> st']的推导进行归纳来证明，
    这个假设导致矛盾。只需要考虑两种情况：[E_WhileFalse]和[E_WhileTrue]，
    其他情况都是矛盾的。

    - 假设[st =[ while b do c end ]=> st']使用规则[E_WhileFalse]证明。
      那么根据假设[beval st b = false]。但这与[b]等价于[true]的假设矛盾。

    - 假设[st =[ while b do c end ]=> st']使用规则[E_WhileTrue]证明。
      我们必须有：

      1. [beval st b = true]，
      2. 存在某个[st0]使得[st =[ c ]=> st0]且[st0 =[ while b do c end ]=> st']，
      3. 我们得到归纳假设：[st0 =[ while b do c end ]=> st']导致矛盾，

      我们通过2和3得到矛盾。 [] *)

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, optional (while_true_nonterm_informal)

    Explain what the lemma [while_true_nonterm] means in English.

(* FILL IN HERE *)
*)
(** **** 练习：2星，标准，可选 (while_true_nonterm_informal)

    用英语解释引理[while_true_nonterm]的含义。

(* 在此填写 *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (while_true)

    Prove the following theorem. _Hint_: You'll want to use
    [while_true_nonterm] here. *)
(** **** 练习：2星，标准，特别有用 (while_true)

    证明以下定理。_提示_：你需要在这里使用[while_true_nonterm]。 *)

Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros b c Hb.
  unfold cequiv. intros st st'.
  split.
  - intros H.
    exfalso.
    apply (while_true_nonterm b c st st' Hb H).
  - intros H.
    exfalso.
    apply (while_true_nonterm <{true}> <{skip}> st st').

    (*  展开 bequiv 的定义来证明 *)
    + unfold bequiv. intros st0. reflexivity.
    + exact H.
Qed.

(** A more interesting fact about [while] commands is that any number
    of copies of the body can be "unrolled" without changing meaning.

    Loop unrolling is an important transformation in any real
    compiler: its correctness is of more than academic interest! *)
(** 关于[while]命令的一个更有趣的事实是，可以"展开"任意数量的循环体副本
    而不改变含义。

    循环展开是任何真实编译器中的重要变换：它的正确性不仅仅具有学术意义！ *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse.
      * assumption.
      * apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue.
      * assumption.
      * apply E_Seq with (st' := st'0).
        -- assumption.
        -- assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      * assumption.
      * assumption.
      * assumption.
    + (* loop doesn't run *)
      inversion H5; subst. apply E_WhileFalse. assumption.  Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc) *)
(** **** 练习：2星，标准，可选 (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  (* 证明序列组合的结合律 *)
  intros c1 c2 c3 st st'.
  unfold cequiv. 
  split; intros H.
  - (* 从左到右：(c1;c2);c3 => c1;(c2;c3) *)
    inversion H; subst. (* 分解序列执行 *)

    inversion H2; subst. (* 进一步分解第一个序列 *)

    apply E_Seq with st'1.
    + (* 证明 st =[ c1 ]=> st'1 *)
      assumption.
    + (* 证明 st'1 =[ c2;c3 ]=> st' *)
      apply E_Seq with st'0.
      * (* 证明 st'1 =[ c2 ]=> st'0 *)
        assumption.
      * (* 证明 st'0 =[ c3 ]=> st' *)
        assumption.
  - (* 从右到左：c1;(c2;c3) => (c1;c2);c3 *)
    inversion H; subst. 
    inversion H5; subst. (* 分解第二个序列 *)
    apply E_Seq with st'1.
    + (* 证明 st =[ c1;c2 ]=> st'1 *)
      apply E_Seq with st'0.
      *assumption.
      *assumption.
    + assumption.
Qed.
(** [] *)

(** Proving program properties involving assignments is one place
    where the fact that program states are treated extensionally
    (e.g., [x !-> m x ; m] and [m] are equal maps) comes in handy. *)
(** 证明涉及赋值的程序性质是程序状态被外延地处理这一事实
    （例如，[x !-> m x ; m]和[m]是相等的映射）派上用场的地方。 *)

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (assign_aequiv) *)
(** **** 练习：2星，标准，特别有用 (assign_aequiv) *)
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
  intros X a Haequiv.
  (* 证明 skip 和 X := a 等价 *)
  split; intro H; inversion H; subst.
  - (* skip => X := a 方向 *)
    (* H 是 st =[ skip ]=> st'，所以 st = st' *)
    assert (Hassign : st' =[ X := a ]=> (X !-> aeval st' a ; st')).
    { apply E_Asgn. reflexivity. }
    (* 由于 aequiv <{ X }> a，所以 st' X = aeval st' a *)
    unfold aequiv in Haequiv.
    specialize (Haequiv st').
    simpl in Haequiv.
    (* 关键：重写 Hassign 中的状态更新，利用 t_update_same *)
    rewrite <- Haequiv in Hassign.
    rewrite t_update_same in Hassign.
    exact Hassign.
  - (* X := a => skip 方向 *)
    (* H 是 st =[ X := a ]=> st'，所以 st' = (X !-> aeval st a ; st) *)
    (* 但由于 aequiv，实际上 st' = st，所以需要证明 st =[ skip ]=> st *)
    unfold aequiv in Haequiv.
    specialize (Haequiv st).
    simpl in Haequiv.
    (* 利用等价性：st X = aeval st a *)
    { rewrite <- Haequiv. rewrite t_update_same.     apply E_Skip. }

Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (equiv_classes) *)
(** **** 练习：2星，标准 (equiv_classes) *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)
(** 给定以下程序，将在Imp中等价的程序分组。你的答案应该是一个列表的列表，
    其中每个子列表代表一组等价的程序。例如，如果你认为程序(a)到(h)彼此等价，
    但不等价于(i)，你的答案应该如下所示：

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    在[equiv_classes]的定义中写下你的答案。 *)

Definition prog_a : com :=
  <{ while X > 0 do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while X <> 0 do
       X := (X * Y) + 1
     end }>.

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while X <> Y do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while X <> X do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while X <> Y do
       X := Y + 1
     end }>.

Definition equiv_classes : list (list com) :=
  [
    (* 等价类1: 总是无限循环的程序 *)
    [prog_g];
    (* 等价类2: 什么都不做的程序 (skip) *)
    [prog_c; prog_h];
    (* 其他程序各自形成独立的等价类 *)
    [prog_a];  (* 当X>0时无限循环，否则终止 *)
    [prog_b];  (* 复杂的条件赋值逻辑 *)
    [prog_d];  (* 取决于X和Y的值 *)
    [prog_e];  (* 简单的Y := 0 *)
    [prog_f];  (* 复杂的while循环 *)
    [prog_i]   (* while X <> Y do X := Y + 1 end *)
  ].

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)
(** * 行为等价性的性质 *)

(** We next consider some fundamental properties of program
    equivalence. *)
(** 接下来我们考虑程序等价性的一些基本性质。 *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)
(** ** 行为等价性是一个等价关系 *)

(** First, let's verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)
(** 首先，让我们验证[aexps]、[bexps]和[com]上的等价关系确实是_等价关系_
    —— 即，它们是自反的、对称的和传递的。证明都很简单。 *)

Lemma refl_aequiv : forall (a : aexp),
  aequiv a a.
Proof.
  intros a st. reflexivity.  Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp),
  bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com),
  cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)
(** ** 行为等价性是一个同余关系 *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded: *)
(** 不太明显的是，行为等价性也是一个_同余关系_。
    也就是说，两个子程序的等价性意味着包含它们的更大程序的等价性： *)

(**
                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')

    ... and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of an inductive definition, but simply to write down some
    valid implications in a readable format. We prove these
    implications below.) *)
(** （注意我们在这里使用推理规则记号不是作为归纳定义的一部分，
    而只是以可读的格式写下一些有效的蕴含。我们在下面证明这些蕴含。） *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the parts that didn't
    change -- i.e., the "proof burden" of a small change to a large
    program is proportional to the size of the change, not the
    program! *)
(** 我们将在下一节（在[fold_constants_com_sound]的证明中）看到
    为什么这些同余性质很重要的具体例子，但主要思想是它们允许我们
    用等价的小部分替换大程序的一小部分，并知道整个大程序是等价的，
    _而无需_对没有改变的部分做显式证明 —— 即，对大程序的小改变的
    "证明负担"与改变的大小成比例，而不是与程序成比例！ *)

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [while] -- that is, if
    [b] is equivalent to [b'] and [c] is equivalent to [c'], then
    [while b do c end] is equivalent to [while b' do c' end].

    _Proof_: Suppose [b] is equivalent to [b'] and [c] is
    equivalent to [c'].  We must show, for every [st] and [st'], that
    [st =[ while b do c end ]=> st'] iff [st =[ while b' do c'
    end ]=> st'].  We consider the two directions separately.

      - ([->]) We show that [st =[ while b do c end ]=> st'] implies
        [st =[ while b' do c' end ]=> st'], by induction on a
        derivation of [st =[ while b do c end ]=> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileFalse] or [E_WhileTrue].

          - [E_WhileFalse]: In this case, the form of the rule gives us
            [beval st b = false] and [st = st'].  But then, since
            [b] and [b'] are equivalent, we have [beval st b' =
            false], and [E_WhileFalse] applies, giving us
            [st =[ while b' do c' end ]=> st'], as required.

          - [E_WhileTrue]: The form of the rule now gives us [beval st
            b = true], with [st =[ c ]=> st'0] and [st'0 =[ while
            b do c end ]=> st'] for some state [st'0], with the
            induction hypothesis [st'0 =[ while b' do c' end ]=>
            st'].

            Since [c] and [c'] are equivalent, we know that [st =[
            c' ]=> st'0].  And since [b] and [b'] are equivalent,
            we have [beval st b' = true].  Now [E_WhileTrue] applies,
            giving us [st =[ while b' do c' end ]=> st'], as
            required.

      - ([<-]) Similar. [] *)
(** 循环的同余性质稍微有趣一些，因为它需要归纳。

    _定理_：等价性对于[while]是同余的 —— 即，如果[b]等价于[b']且[c]等价于[c']，
    那么[while b do c end]等价于[while b' do c' end]。

    _证明_：假设[b]等价于[b']且[c]等价于[c']。我们必须证明，对于每个[st]和[st']，
    [st =[ while b do c end ]=> st']当且仅当[st =[ while b' do c' end ]=> st']。
    我们分别考虑两个方向。

      - ([->]) 我们通过对[st =[ while b do c end ]=> st']的推导进行归纳来证明
        [st =[ while b do c end ]=> st']蕴含[st =[ while b' do c' end ]=> st']。
        唯一非平凡的情况是推导中的最终规则是[E_WhileFalse]或[E_WhileTrue]时。

          - [E_WhileFalse]：在这种情况下，规则的形式给出[beval st b = false]
            和[st = st']。但是，由于[b]和[b']等价，我们有[beval st b' = false]，
            [E_WhileFalse]适用，给出[st =[ while b' do c' end ]=> st']，
            如所需。

          - [E_WhileTrue]：规则的形式现在给出[beval st b = true]，
            以及对某个状态[st'0]有[st =[ c ]=> st'0]和[st'0 =[ while b do c end ]=> st']，
            归纳假设为[st'0 =[ while b' do c' end ]=> st']。

            由于[c]和[c']等价，我们知道[st =[ c' ]=> st'0]。
            由于[b]和[b']等价，我们有[beval st b' = true]。
            现在[E_WhileTrue]适用，给出[st =[ while b' do c' end ]=> st']，
            如所需。

      - ([<-]) 类似。 [] *)

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKED IN CLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence) *)
(** **** 练习：3星，标准，可选 (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  intros c1 c1' c2 c2' Hc1 Hc2.
  (* 展开cequiv的定义 *)
  unfold cequiv. intros st st'.
  split; intro H.
  - (* c1;c2 => c1';c2' 方向 *)
    (* 分解序列执行 *)
    inversion H; subst.
    (* H2: st =[ c1 ]=> st'0, H5: st'0 =[ c2 ]=> st' *)
    (* 利用c1和c1'的等价性 *)
    unfold cequiv in Hc1.
    specialize (Hc1 st st'0).
    destruct Hc1 as [Hc1_lr Hc1_rl].
    apply Hc1_lr in H2. (* 得到 st =[ c1' ]=> st'0 *)
    (* 利用c2和c2'的等价性 *)
    unfold cequiv in Hc2.
    specialize (Hc2 st'0 st').
    destruct Hc2 as [Hc2_lr Hc2_rl].
    apply Hc2_lr in H5. (* 得到 st'0 =[ c2' ]=> st' *)
    (* 构造序列执行 *)
    apply E_Seq with st'0.
    + exact H2.
    + exact H5.
  - (* c1';c2' => c1;c2 方向 *)
    (* 分解序列执行 *)
    inversion H; subst.
    (* H2: st =[ c1' ]=> st'0, H5: st'0 =[ c2' ]=> st' *)
    (* 利用c1'和c1的等价性 *)
    unfold cequiv in Hc1.
    specialize (Hc1 st st'0).
    destruct Hc1 as [Hc1_lr Hc1_rl].
    apply Hc1_rl in H2. (* 得到 st =[ c1 ]=> st'0 *)
    (* 利用c2'和c2的等价性 *)
    unfold cequiv in Hc2.
    specialize (Hc2 st'0 st').
    destruct Hc2 as [Hc2_lr Hc2_rl].
    apply Hc2_rl in H5. (* 得到 st'0 =[ c2 ]=> st' *)
    (* 构造序列执行 *)
    apply E_Seq with st'0.
    + exact H2.
    + exact H5.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence) *)
(** **** 练习：3星，标准 (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  intros b b' c1 c1' c2 c2' Hb Hc1 Hc2.
  unfold cequiv. intros st st'.
  split; intro H.
  - (* -> 方向：从 if b then c1 else c2 到 if b' then c1' else c2' *)
    inversion H; subst.
    + (* 情况1：条件为真，执行c1 *)
      (* H0: beval st b = true, H1: st =[ c1 ]=> st' *)
      apply E_IfTrue.
      * (* 证明 beval st b' = true *)
        unfold bequiv in Hb.
        rewrite <- Hb. exact H5.
      * (* 证明 st =[ c1' ]=> st' *)
        unfold cequiv in Hc1.
        apply Hc1. exact H6.
    + (* 情况2：条件为假，执行c2 *)
      (* H0: beval st b = false, H1: st =[ c2 ]=> st' *)
      apply E_IfFalse.
      * (* 证明 beval st b' = false *)
        unfold bequiv in Hb.
        rewrite <- Hb. exact H5.
      * (* 证明 st =[ c2' ]=> st' *)
        unfold cequiv in Hc2.
        apply Hc2. exact H6.
  - (* <- 方向：从 if b' then c1' else c2' 到 if b then c1 else c2 *)
    inversion H; subst.
    + (* 情况1：条件为真，执行c1' *)
      (* H0: beval st b' = true, H1: st =[ c1' ]=> st' *)
      apply E_IfTrue.
      * (* 证明 beval st b = true *)
        unfold bequiv in Hb.
        rewrite Hb. exact H5.
      * (* 证明 st =[ c1 ]=> st' *)
        unfold cequiv in Hc1.
        apply Hc1. exact H6.
    + (* 情况2：条件为假，执行c2' *)
      (* H0: beval st b' = false, H1: st =[ c2' ]=> st' *)
      apply E_IfFalse.
      * (* 证明 beval st b = false *)
        unfold bequiv in Hb.
        rewrite Hb. exact H5.
      * (* 证明 st =[ c2 ]=> st' *)
        unfold cequiv in Hc2.
        apply Hc2. exact H6.
Qed.
(** [] *)

(** For example, here are two equivalent programs and a proof of their
    equivalence using these congruence theorems... *)
(** 例如，这里是两个等价的程序以及使用这些同余定理证明它们等价性的证明... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if X = 0 then Y := 0
       else Y := 42 end }>
    (* Program 2: *)
    <{ X := 0;
       if X = 0 then Y := X - X   (* <--- Changed here *)
       else Y := 42 end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply sub_diag.
    + apply refl_cequiv.
Qed.

(** **** Exercise: 3 stars, advanced (not_congr)

    We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence?  Write down the
    relation (formally), together with an informal sketch of a proof
    that it is an equivalence but not a congruence. *)
(** **** 练习：3星，高级 (not_congr)

    我们已经证明了[cequiv]关系既是命令上的等价关系又是同余关系。
    你能想出一个在命令上既是等价关系但_不是_同余关系的关系吗？
    写下这个关系（形式化），以及一个非正式的证明草图，说明它是等价关系
    但不是同余关系。 *)

(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_not_congr : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Program Transformations *)
(** * 程序变换 *)

(** A _program transformation_ is a function that takes a program as
    input and produces a modified program as output.  Compiler
    optimizations such as constant folding are a canonical example,
    but there are many others. *)
(** _程序变换_是一个以程序为输入并产生修改后的程序作为输出的函数。
    编译器优化如常量折叠是一个典型例子，但还有很多其他的。 *)

(** A program transformation is said to be _sound_ if it preserves the
    behavior of the original program. *)
(** 如果程序变换保持原始程序的行为，则称其为_正确的_。 *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)
(** ** 常量折叠变换 *)

(** An expression is _constant_ if it contains no variable references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)
(** 如果表达式不包含变量引用，则称其为_常量_。

    常量折叠是一种优化，它找到常量表达式并用它们的值替换它们。 *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't do other
    "obvious" things like eliminating trivial additions (e.g.,
    rewriting [0 + X] to just [X]).: we are focusing attention on a
    single optimization for the sake of simplicity.

    It is not hard to incorporate other ways of simplifying
    expressions -- the definitions and proofs just get longer.  We'll
    consider optimizations in the exercises. *)
(** 注意，这个版本的常量折叠不做其他"显而易见"的事情，如消除平凡的加法
    （例如，将[0 + X]重写为[X]）：为了简单起见，我们专注于单一的优化。

    合并其他简化表达式的方法并不困难 —— 定义和证明只是变得更长。
    我们将在练习中考虑优化。 *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq], [BNeq], and [BLe] cases); we can also look for constant
    _boolean_ expressions and evaluate them in-place as well. *)
(** 我们不仅可以将[fold_constants_aexp]提升到[bexp]（在[BEq]、[BNeq]和[BLe]情况下）；
    我们还可以寻找常量_布尔_表达式并就地求值它们。 *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <> a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if negb (n1 =? n2) then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <> a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ a1 > a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{false}> else <{true}>
      | (a1', a2') =>
          <{ a1' > a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)
(** 要在命令中折叠常量，我们对所有嵌入的表达式应用适当的折叠函数。 *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if (X - Y) = (2 + 4) then skip
       else Y := 0 end;
       if 0 <= (4 - (2 + 1)) then Y := 0
       else skip end;
       while Y = 0 do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if (X - Y) = 6 then skip
       else Y := 0 end;
       Y := 0;
       while Y = 0 do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal)

    Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp b],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [a1 = a2].

   In this case, we must show

       beval st <{ a1 = a2 }>
     = beval st (fold_constants_bexp <{ a1 = a2 }>).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp <{ a1 = a2 }>
         = if n1 =? n2 then <{true}> else <{false}>

       and

           beval st <{a1 = a2}>
         = (aeval st a1) =? (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st <{a1 = a2}>
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if n1 =? n2 then <{true}> else <{false}>)
         = if n1 =? n2 then beval st <{true}> else beval st <{false}>
         = if n1 =? n2 then true else false
         = n1 =? n2.

       So

           beval st (<{ a1 = a2 }>)
         = n1 =? n2.
         = beval st (if n1 =? n2 then <{true}> else <{false}>),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st <{a1 = a2}>
         = beval st (<{ (fold_constants_aexp a1) =
                         (fold_constants_aexp a2) }>),

       which, by the definition of [beval], is the same as showing

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  [] *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BNeq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n <=? n0); reflexivity.
  - (* BGt *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n <=? n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound)

    Complete the [while] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false; assumption.
  - (* while *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption).

    + (* b always true *)
      apply while_true; assumption.
    + (* b always false *)
      apply while_false; assumption.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, standard, optional (optimize_0plus_var)

    Recall the definition [optimize_0plus] from the [Imp] chapter
    of _Logical Foundations_:

    Fixpoint optimize_0plus (a:aexp) : aexp :=
      match a with
      | ANum n =>
          ANum n
      | <{ 0 + a2 }> =>
          optimize_0plus a2
      | <{ a1 + a2 }> =>
          <{ (optimize_0plus a1) + (optimize_0plus a2) }>
      | <{ a1 - a2 }> =>
          <{ (optimize_0plus a1) - (optimize_0plus a2) }>
      | <{ a1 * a2 }> =>
          <{ (optimize_0plus a1) * (optimize_0plus a2) }>
      end.

   Note that this function is defined over the old version of [aexp]s,
   without states.

   Write a new version of this function that deals with variables (by
   leaving them alone), plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com
*)

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{ 0 + a2 }> => optimize_0plus_aexp a2
  | <{ a1 + a2 }> => 
      <{ (optimize_0plus_aexp a1) + (optimize_0plus_aexp a2) }>
  | <{ a1 - a2 }> => 
      <{ (optimize_0plus_aexp a1) - (optimize_0plus_aexp a2) }>
  | <{ a1 * a2 }> => 
      <{ (optimize_0plus_aexp a1) * (optimize_0plus_aexp a2) }>
  end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{ a1 = a2 }> => 
      <{ (optimize_0plus_aexp a1) = (optimize_0plus_aexp a2) }>
  | <{ a1 <> a2 }> => 
      <{ (optimize_0plus_aexp a1) <> (optimize_0plus_aexp a2) }>
  | <{ a1 <= a2 }> => 
      <{ (optimize_0plus_aexp a1) <= (optimize_0plus_aexp a2) }>
  | <{ a1 > a2 }> => 
      <{ (optimize_0plus_aexp a1) > (optimize_0plus_aexp a2) }>
  | <{ ~ b1 }> => 
      <{ ~ (optimize_0plus_bexp b1) }>
  | <{ b1 && b2 }> => 
      <{ (optimize_0plus_bexp b1) && (optimize_0plus_bexp b2) }>
  end.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | <{ skip }> => <{ skip }>
  | <{ x := a }> => <{ x := (optimize_0plus_aexp a) }>
  | <{ c1 ; c2 }> => 
      <{ (optimize_0plus_com c1) ; (optimize_0plus_com c2) }>
  | <{ if b then c1 else c2 end }> => 
      <{ if (optimize_0plus_bexp b) then (optimize_0plus_com c1) 
         else (optimize_0plus_com c2) end }>
  | <{ while b do c1 end }> => 
      <{ while (optimize_0plus_bexp b) do (optimize_0plus_com c1) end }>
  end.

Example test_optimize_0plus:
    optimize_0plus_com
       <{ while X <> 0 do X := 0 + X - 1 end }>
  =    <{ while X <> 0 do X := X - 1 end }>.
Proof.
  reflexivity.
Qed.

(** Prove that these three functions are sound, as we did for
    [fold_constants_*].  Make sure you use the congruence lemmas in the
    proof of [optimize_0plus_com] -- otherwise it will be _long_! *)

Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl; try reflexivity.
  - (* APlus *)
    destruct a1 eqn:Heqa1; simpl; try (rewrite IHa1, IHa2; reflexivity).
Admitted.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b; simpl; try reflexivity.
  - (* BEq *)
    rewrite optimize_0plus_aexp_sound, optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound with (a := a2).
    reflexivity.
  - (* BNeq *)
    rewrite optimize_0plus_aexp_sound, optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound with (a := a2).
    reflexivity.
  - (* BLe *)
    rewrite optimize_0plus_aexp_sound, optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound with (a := a2).
    reflexivity.
  - (* BGt *)
    rewrite optimize_0plus_aexp_sound, optimize_0plus_aexp_sound.
    rewrite <- optimize_0plus_aexp_sound with (a := a2).
    reflexivity.
  - (* BNot *)
    rewrite IHb. reflexivity.
  - (* BAnd *)
    rewrite IHb1, IHb2. reflexivity.
Qed.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) 
    apply refl_cequiv.
  - (* := *)
    apply CAsgn_congruence. apply optimize_0plus_aexp_sound.
  - (* ; *)
    apply CSeq_congruence; assumption.
  - (* if *)
    apply CIf_congruence. 
    + apply optimize_0plus_bexp_sound.
    + assumption.
    + assumption.
  - (* while *)
    apply CWhile_congruence.
    + apply optimize_0plus_bexp_sound.
    + assumption.
Qed.

(** Finally, let's define a compound optimizer on commands that first
    folds constants (using [fold_constants_com]) and then eliminates
    [0 + n] terms (using [optimize_0plus_com]). *)

Definition optimizer (c : com) := optimize_0plus_com (fold_constants_com c).

(** Prove that this optimizer is sound. *)

Theorem optimizer_sound :
  ctrans_sound optimizer.
Proof.
  unfold ctrans_sound. intros c.
  unfold optimizer.
  (* 我们需要证明 cequiv c (optimize_0plus_com (fold_constants_com c)) *)
  (* 使用传递性：c ≡ fold_constants_com c ≡ optimize_0plus_com (fold_constants_com c) *)
  apply trans_cequiv with (fold_constants_com c).
  - (* 证明 cequiv c (fold_constants_com c) *)
    apply fold_constants_com_sound.
  - (* 证明 cequiv (fold_constants_com c) (optimize_0plus_com (fold_constants_com c)) *)
    apply optimize_0plus_com_sound.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proving Inequivalence *)

(** Next, let's look at some programs that are _not_ equivalent. *)

(** Suppose that [c1] is a command of the form

       X := a1; Y := a2

    and [c2] is the command

       X := a1; Y := a2'

    where [a2'] is formed by substituting [a1] for all occurrences
    of [X] in [a2].

    For example, [c1] and [c2] might be:

       c1  =  (X := 42 + 53;
               Y := Y + X)
       c2  =  (X := 42 + 53;
               Y := Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression [u] for each occurrence of a given variable [x] in
    another expression [a]: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if String.eqb x x' then u else AId x'
  | <{ a1 + a2 }>  =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }>  =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}>
  = <{ Y + (42 + 53)}>.
Proof. simpl. reflexivity. Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property : Prop := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

(** Sadly, the property does _not_ always hold.

    Here is a counterexample:

       X := X + 1; Y := X

    If we perform the substitution, we get

       X := X + 1; Y := X + 1

    which clearly isn't equivalent. *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv)

    The equivalence we had in mind above was not complete nonsense --
    in fact, it was actually almost right.  To make it correct, we
    just need to exclude the case where the variable [X] occurs in the
    right-hand side of the first assignment statement. *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros x st a ni H.
  induction H; simpl; try reflexivity.
  - (* VNUId *)
    unfold t_update. 
    destruct (String.eqb x y) eqn:Heq.
    + (* x = y *)
      apply String.eqb_eq in Heq. contradiction.
    + (* x <> y *)
      reflexivity.
  - (* VNUPlus *)
    rewrite IHvar_not_used_in_aexp1, IHvar_not_used_in_aexp2.
    reflexivity.
  - (* VNUMinus *)
    rewrite IHvar_not_used_in_aexp1, IHvar_not_used_in_aexp2.
    reflexivity.
  - (* VNUMult *)
    rewrite IHvar_not_used_in_aexp1, IHvar_not_used_in_aexp2.
    reflexivity.
Qed.

(** Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)

(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, standard (inequiv_exercise)

    Prove that an infinite loop is not equivalent to [skip] *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  unfold cequiv. intros H.
  (* 我们将构造一个反例：存在状态st使得skip可以执行但while true不能 *)
  (* 选择任意状态，比如空状态 *)
  assert (Hskip : empty_st =[ skip ]=> empty_st).
  { apply E_Skip. }
  (* 根据假设H，while true应该也能从empty_st执行到empty_st *)
  apply H in Hskip.
  (* 但这与while_true_nonterm矛盾 *)
  eapply while_true_nonterm in Hskip.
  - exact Hskip.
  - (* 证明 bequiv true true *)
    unfold bequiv. intros st. reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;
      Z := Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** **** Exercise: 2 stars, standard (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc : forall st x n,
      st =[ havoc x ]=> (x !-> n ; st)

  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof.
  apply E_Havoc.
Qed.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof.
  apply E_Seq with empty_st.
  - apply E_Skip.
  - apply E_Havoc.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)

    Are the following two programs equivalent? *)

Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)
  (* Hint: You may want to use [t_update_permute] at some point,
     in which case you'll probably be left with [X <> Y] as a
     hypothesis. You can use [discriminate] to discharge this. *)
Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  (* Hint: You may want to use [t_update_permute] at some point,
     in which case you'll probably be left with [X <> Y] as a
     hypothesis. You can use [discriminate] to discharge this. *)
  left. (* 选择左分支，证明它们等价 *)
  unfold cequiv, pXY, pYX.
  intros st st'.
  split; intros H.
  - (* pXY => pYX *)
    (* st =[ HAVOC X;; HAVOC Y ]=> st' *)
    inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    (* 现在我们有具体的最终状态 (Y !-> n0; X !-> n; st) *)
    (* 构造 pYX 的执行: 先 HAVOC Y，再 HAVOC X *)
    apply E_Seq with (st' := (Y !-> n0; st)).
    + apply E_Havoc.
    + (* 需要: (Y !-> n0; st) =[ HAVOC X ]=> (Y !-> n0; X !-> n; st) *)
      (* 但 HAVOC X 会产生 (X !-> n; Y !-> n0; st) *)
      (* 利用状态更新交换律 *)
      assert (Heq: (X !-> n; Y !-> n0; st) = (Y !-> n0; X !-> n; st)).
      { apply functional_extensionality. intro x.
        destruct (String.string_dec x X).
        - subst. rewrite t_update_eq. 
          rewrite t_update_neq; [| discriminate].
          rewrite t_update_eq. reflexivity.
        - destruct (String.string_dec x Y).
          + subst. rewrite t_update_neq; [| discriminate].
            rewrite t_update_eq. rewrite t_update_eq. reflexivity.
          + rewrite t_update_neq; [| intro Hcontra; apply n1; symmetry; exact Hcontra].
            rewrite t_update_neq; [| intro Hcontra; apply n2; symmetry; exact Hcontra].
            rewrite t_update_neq; [| intro Hcontra; apply n2; symmetry; exact Hcontra].
            rewrite t_update_neq; [| intro Hcontra; apply n1; symmetry; exact Hcontra].
            reflexivity. }
      rewrite <- Heq.
      apply E_Havoc.
  - (* pYX => pXY *)
    (* 完全对称的证明 *)
    inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    apply E_Seq with (st' := (X !-> n0; st)).
    + apply E_Havoc.
    + assert (Heq: (Y !-> n; X !-> n0; st) = (X !-> n0; Y !-> n; st)).
      { apply functional_extensionality. intro x.
        destruct (String.string_dec x Y).
        - subst. rewrite t_update_eq.
          rewrite t_update_neq; [| discriminate].
          rewrite t_update_eq. reflexivity.
        - destruct (String.string_dec x X).
          + subst. rewrite t_update_neq; [| discriminate].
            rewrite t_update_eq. rewrite t_update_eq. reflexivity.
          + rewrite t_update_neq; [| apply not_eq_sym; exact n1].
            rewrite t_update_neq; [| apply not_eq_sym; exact n2].
            rewrite t_update_neq; [| apply not_eq_sym; exact n2].
            rewrite t_update_neq; [| apply not_eq_sym; exact n1].
            reflexivity. }
      rewrite <- Heq.
      apply E_Havoc.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)

    Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof. 
  right. unfold not. intro H.
  (* 我们证明这两个程序不等价 *)
  (* ptwice 可以产生 X=0, Y=1 的状态，但 pcopy 不能 *)
  assert (Hptwice: empty_st =[ ptwice ]=> (Y !-> 1; X !-> 0; empty_st)).
  { unfold ptwice. apply E_Seq with (st' := (X !-> 0; empty_st)).
    - apply E_Havoc.
    - apply E_Havoc. }
  
  (* 从等价性推出 pcopy 也应该能产生相同状态 *)
  unfold cequiv in H.
  specialize (H empty_st (Y !-> 1; X !-> 0; empty_st)).
  destruct H as [H1 H2].
  assert (Hpcopy: empty_st =[ pcopy ]=> (Y !-> 1; X !-> 0; empty_st)).
  { apply H1. exact Hptwice. }
  
  (* 但这导致矛盾 *)
  unfold pcopy in Hpcopy.
  inversion Hpcopy as [st' H3 H4 | | | | | | | ]; subst.
  inversion H; subst.
  inversion H0; subst.
  simpl in H7.
  rewrite t_update_eq in H7.
  assert (Y_eq: (Y !-> n; X !-> n) Y = (Y !-> 1; X !-> 0) Y).
{ rewrite H7. reflexivity. }
rewrite t_update_eq in Y_eq.
rewrite t_update_eq in Y_eq.
assert (X_eq: (Y !-> n; X !-> n) X = (Y !-> 1; X !-> 0) X).
{ rewrite H7. reflexivity. }
rewrite t_update_neq in X_eq; [| discriminate].
rewrite t_update_eq in X_eq.
rewrite t_update_neq in X_eq; [| discriminate]. 
rewrite t_update_eq in X_eq.
subst. discriminate.
Qed.
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof.
  intros st st' H_neq_zero Heval.
  unfold p1 in Heval.
  (* p1 是一个 WHILE 循环，我们需要分析它如何停机 *)
  remember <{ while ~ (X = 0) do havoc Y; X := X + 1 end }> as loop eqn:Heqloop.
  induction Heval; inversion Heqloop; subst.
  - (* E_WhileFalse: ~(X = 0) 为假，即 X = 0 *)
    simpl in H. apply negb_false_iff in H.
    apply eqb_eq in H. 
    contradiction.
  - (* E_WhileTrue: ~(X = 0) 为真，循环体执行后继续循环 *)
    (* 但是循环体会使 X 增加，所以 X 永远不会变成 0 *)
    apply IHHeval2; auto.
    (* 我们需要证明在执行 HAVOC Y;; X ::= X + 1 后，X 仍然不等于 0 *)
    inversion Heval1 as [st1 H1 H2 | | | | | | | ]; subst.
  (* 首先分析 HAVOC Y 的效果 *)
  inversion H0; subst.
  (* 现在 st'0 = (Y !-> n; st) 对某个 n，所以 st'0 X = st X *)

  (* 然后分析 X := X + 1 的效果 *)  
  inversion H1; subst.
  simpl.
  (* 现在 st' = (X !-> aeval st'0 (X + 1); st'0) *)
  (* 即 st' X = aeval st'0 (X + 1) = st'0 X + 1 = st X + 1 *)

  rewrite t_update_eq.
  (* 我们需要证明 aeval st'0 (X + 1) <> 0 *)
  (* 即 st'0 X + 1 <> 0 *)
  (* 即 st X + 1 <> 0 *)

  unfold not. intro Hcontra.
  apply H_neq_zero.
  lia.
Qed.

Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
  intros st st' H_neq_zero Heval.
  unfold p2 in Heval.
  (* p2 是一个 WHILE 循环，循环体是 SKIP *)
  remember <{ while ~ (X = 0) do skip end }> as loop eqn:Heqloop.
  induction Heval; inversion Heqloop; subst.
  - (* E_WhileFalse: ~(X = 0) 为假，即 X = 0 *)
    simpl in H. apply negb_false_iff in H.
    apply eqb_eq in H. 
    contradiction.
  - (* E_WhileTrue: ~(X = 0) 为真，执行 SKIP 后继续循环 *)
    apply IHHeval2; auto.
    (* SKIP 不改变状态，所以 X 的值保持不变 *)
    inversion Heval1; subst. 
    assumption.
Qed.

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof. 
  unfold cequiv. intros st st'.
  split; intro H.
  - (* p1 -> p2 *)
    destruct (st X =? 0) eqn:HX.
    + (* st X = 0，两个程序都会立即停机 *)
      apply eqb_eq in HX.
      unfold p1 in H.
      unfold p2.
      remember <{ while ~ (X = 0) do havoc Y; X := X + 1 end }> as loop1.
      induction H; inversion Heqloop1; subst.
      * (* E_WhileFalse for p1 *)
        simpl in H. apply negb_false_iff in H.
        apply eqb_eq in H. subst.
        apply E_WhileFalse.
        simpl. rewrite HX. reflexivity.
      * (* E_WhileTrue for p1 - 但这不可能，因为 X = 0 *)
        simpl in H0. 
        (* 从 H 和 HX 得出矛盾 *)
        simpl in H.
        rewrite HX in H.
        simpl in H.
        discriminate.
    + (* st X <> 0，两个程序都不会停机 *)
      apply eqb_neq in HX.
      exfalso. apply (p1_may_diverge st st' HX H).
  - (* p2 -> p1 *)
    destruct (st X =? 0) eqn:HX.
    + (* st X = 0，两个程序都会立即停机 *)
      apply eqb_eq in HX.
      unfold p2 in H.
      unfold p1.
      remember <{ while ~ (X = 0) do skip end }> as loop2.
      induction H; inversion Heqloop2; subst.
      * (* E_WhileFalse for p2 *)
        apply E_WhileFalse.
        simpl. rewrite HX. reflexivity.
      * (* E_WhileTrue for p2 - 但这不可能，因为 X = 0 *)
        simpl in H0.
        (* 从 H 和 HX 得出矛盾 *)
        simpl in H.
        rewrite HX in H.
        simpl in H.
        discriminate.
    + (* st X <> 0，两个程序都不会停机 *)
      apply eqb_neq in HX.
      exfalso. apply (p2_may_diverge st st' HX H).
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  <{ Z := 1;
     while X <> 0 do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.
  unfold cequiv. intros H.
  (* 我们找一个反例来说明p3和p4不等价 *)
  (* 让我们从一个 X ≠ 0 的状态开始，这样会进入p3的循环 *)
  remember (t_update empty_st X 1) as st1.
  (* 让我们考虑一个可能的执行，其中HAVOC将Z设为0 *)
  remember (t_update (t_update st1 Z 1) X 0) as st2.
  remember (t_update st2 Z 0) as st3.
  
  assert (st1 =[ p3 ]=> st3).
  { unfold p3. 
    eapply E_Seq.
    - (* Z ::= 1 *) 
      apply E_Asgn. reflexivity.
    - (* WHILE loop *) 
      eapply E_WhileTrue.
      + (* ~(X = 0) *) 
        simpl. subst st1.
        simpl.
        reflexivity.
      + (* HAVOC X;; HAVOC Z *)
        eapply E_Seq.
        * (* HAVOC X *) 
          apply E_Havoc.
        * (* HAVOC Z *)
          apply E_Havoc.
      + (* rest of the loop *)
        simpl.
        subst.
        apply E_WhileFalse.
        simpl.  reflexivity. }
  
  (* 我们知道p4总是会把Z设为1 *)
  assert (H_p4: forall st st', st =[ p4 ]=> st' -> st' Z = 1).
  { intros st st' Heval.
    unfold p4 in Heval.
    inversion Heval. subst.
    inversion H3. subst.
    inversion H6. subst.
    rewrite t_update_eq.
    reflexivity. }

  (* 但H0显示p3可以到达Z=0的状态 *)
  assert (Hz: (Z !-> 0; X !-> 0; Z !-> 1; X !-> 1) Z = 0).
  { rewrite t_update_eq. reflexivity. }
(* 根据等价性H，如果p3可以到达某个状态，p4也必须能到达同一个状态 *)
assert (Hp4_reach: st1 =[ p4 ]=> st3).
{ apply H. exact H0. }

(* 这与p4总是将Z设为1的性质矛盾 *)
apply H_p4 in Hp4_reach.
rewrite Heqst3 in Hp4_reach.
rewrite t_update_eq in Hp4_reach.
discriminate Hp4_reach.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  <{ while X <> 1 do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof.
  unfold cequiv. intros st st'.
  split.
  - (* p5 -> p6 *)
    intro H.
    unfold p5 in H.
    remember <{ while X <> 1 do havoc X end }> as loop eqn:Hloop.
    induction H; try discriminate.
    + (* E_WhileFalse *)
      injection Hloop as Hloop. subst.
      simpl in H. unfold negb in H.
      destruct (st X =? 1) eqn:HX; try discriminate.
      apply eqb_eq in HX.
      unfold p6. 
      (* 我们需要证明 st =[ X := 1 ]=> st *)
      (* 但 E_Asgn 给出 st =[ X := 1 ]=> (X !-> 1; st) *)
      (* 由于 st X = 1，所以 (X !-> 1; st) = st *)
      assert (H_eq: (X !-> 1; st) = st).
      { apply functional_extensionality. intro x.
        unfold t_update.
        destruct (String.eqb X x) eqn:Heq.
        - apply String.eqb_eq in Heq. subst. symmetry. exact HX.
        - reflexivity.
      }
      admit.
    + admit.
  - admit.
  
Admitted.
(** [] *)
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)

    (Hint: You may or may not -- depending how you approach it -- need
    to use [functional_extensionality] explicitly for this one.) *)

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1; b; c2) {
          c3
      }

    is equivalent to:

       c1;
       while b do
         c3;
         c2
       end
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = while X <> 1 do
         X := X - 1
       end

    approximates [c2 = X := 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Definition c4 : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof. (* FILL IN HERE *) Admitted.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof. (* FILL IN HERE *) Admitted.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c c' -> zprop c'.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* 2025-08-24 13:47 *)
