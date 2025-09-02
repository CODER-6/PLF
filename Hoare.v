(** * Hoare: Hoare Logic, Part I *)
(** * Hoare: 霍尔逻辑，第一部分 *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat.
From Stdlib Require Import PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From PLF Require Export Imp.
Set Default Goal Selector "!".

(** In the final chaper of _Logical Foundations_ (_Software
    Foundations_, volume 1), we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - We defined a type of _abstract syntax trees_ for Imp, together
      with an _evaluation relation_ (a partial function on states)
      that specifies the _operational semantics_ of programs.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    - We proved a number of _metatheoretic properties_ -- "meta" in
      the sense that they are properties of the language as a whole,
      rather than of particular programs in the language.  These
      included:

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a number
          of useful program transformations

        - behavioral equivalence of programs (in the [Equiv]
          chapter). *)
(** 在《逻辑基础》（《软件基础》第一卷）的最后一章中，我们开始将课程前半部分
    开发的数学工具应用于研究一个小型编程语言 Imp 的理论。

    - 我们为 Imp 定义了_抽象语法树_的类型，以及一个_求值关系_（状态上的偏函数），
      用于指定程序的_操作语义_。

      我们定义的语言虽然很小，但捕获了像 C、C++、Java 这样的完整语言的一些
      关键特性，包括可变状态的基本概念和一些常见的控制结构。

    - 我们证明了许多_元理论性质_ —— "元"的意思是它们是整个语言的性质，
      而不是语言中特定程序的性质。这些包括：

        - 求值的确定性

        - 写下定义的一些不同方式的等价性（例如，算术表达式求值的
          函数式和关系式定义）

        - 某些程序类别的保证终止性

        - 许多有用的程序转换的正确性（在保持意义的意义上）

        - 程序的行为等价性（在 [Equiv] 章节中）。 *)

(** If we stopped here, we would already have something useful: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  All of
    these properties are things that language designers, compiler
    writers, and users might care about knowing.  Indeed, many of them
    are so fundamental to our understanding of the programming
    languages we deal with that we might not consciously recognize
    them as "theorems."  But properties that seem intuitively obvious
    can sometimes be quite subtle (sometimes also subtly wrong!).

    We'll return to the theme of metatheoretic properties of whole
    languages later in this volume when we discuss _types_ and _type
    soundness_.  In this chapter, though, we turn to a different set
    of issues.
*)
(** 如果我们在这里停下来，我们已经拥有了一些有用的东西：一套用于定义和讨论
    编程语言和语言特性的工具，这些工具在数学上是精确的、灵活的、易于使用的，
    并应用于一组关键性质。所有这些性质都是语言设计者、编译器编写者和用户
    可能关心了解的。实际上，其中许多性质对于我们理解所处理的编程语言来说
    是如此基础，以至于我们可能没有有意识地将它们识别为"定理"。但是看起来
    直觉上显而易见的性质有时可能相当微妙（有时也是微妙地错误的！）。

    当我们讨论_类型_和_类型可靠性_时，我们将在本卷的后面回到整个语言的
    元理论性质这个主题。不过，在本章中，我们转向一组不同的问题。
*)

(** Our goal in this chapter is to carry out some simple examples of
    _program verification_ -- i.e., to use the precise definition of
    Imp to prove formally that particular programs satisfy particular
    specifications of their behavior.

    We'll develop a reasoning system called _Floyd-Hoare Logic_ --
    often shortened to just _Hoare Logic_ -- in which each of the
    syntactic constructs of Imp is equipped with a generic "proof
    rule" that can be used to reason compositionally about the
    correctness of programs involving this construct. *)
(** 我们在本章的目标是执行一些_程序验证_的简单例子 —— 即，使用 Imp 的精确
    定义来形式化地证明特定程序满足其行为的特定规范。

    我们将开发一个称为_弗洛伊德-霍尔逻辑_（Floyd-Hoare Logic）的推理系统 ——
    通常简称为_霍尔逻辑_（Hoare Logic）—— 在这个系统中，Imp 的每个语法构造
    都配备了一个通用的"证明规则"，可以用来组合地推理涉及该构造的程序的正确性。 *)

(** Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems. *)
(** 霍尔逻辑起源于20世纪60年代，直到今天仍然是密集研究的主题。它位于
    学术界和工业界用于指定和验证真实软件系统的众多工具的核心。 *)

(** Hoare Logic combines two beautiful ideas: a natural way of writing
    down _specifications_ of programs, and a _structured proof
    technique_ for proving that programs are correct with respect to
    such specifications -- where by "structured" we mean that the
    structure of proofs directly mirrors the structure of the programs
    that they are about. *)
(** 霍尔逻辑结合了两个美妙的想法：一种编写程序_规范_的自然方式，以及一种
    _结构化证明技术_，用于证明程序相对于这些规范是正确的 —— 这里的"结构化"
    意味着证明的结构直接反映了它们所涉及的程序的结构。 *)

(* ################################################################# *)
(** * Assertions *)
(** * 断言 *)

(** An _assertion_ is a logical claim about the state of a program's
    memory -- formally, a property of [state]s. *)
(** _断言_是关于程序内存状态的逻辑声明 —— 形式上，是 [state] 的一个性质。 *)

Definition Assertion := state -> Prop.

(** For example,

    - [fun st => st X = 3] holds for states [st] in which value of [X]
      is [3],

    - [fun st => True] hold for all states, and

    - [fun st => False] holds for no states. *)
(** 例如，

    - [fun st => st X = 3] 对于 [X] 的值为 [3] 的状态 [st] 成立，

    - [fun st => True] 对于所有状态都成立，而

    - [fun st => False] 对于没有状态都成立。 *)

(** **** Exercise: 1 star, standard, optional (assertions)

    Paraphrase the following assertions in English (or your favorite
    natural language). *)
(** **** 练习：1 星，标准，可选 (assertions)

    用英语（或你喜欢的自然语言）解释以下断言。 *)

Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* FILL IN HERE *)
End ExAssertions.
(** [] *)

(* ================================================================= *)
(** ** Notations for Assertions *)
(** ** 断言的记号 *)

(** This way of writing assertions can be a little bit heavy,
    for two reasons: (1) every single assertion that we ever write is
    going to begin with [fun st => ]; and (2) this state [st] is the
    only one that we ever use to look up variables in assertions (we
    will almost never need to talk about two different memory states at the
    same time).  For discussing examples informally, we'll adopt some
    simplifying conventions: we'll drop the initial [fun st =>], and
    we'll write just [X] to mean [st X].  Thus, instead of writing

      fun st => st X = m

    we'll write just

      {{ X = m }}.
*)
(** 这种编写断言的方式可能有点繁重，有两个原因：(1) 我们写的每一个断言都要
    以 [fun st => ] 开头；(2) 这个状态 [st] 是我们在断言中用来查找变量的
    唯一状态（我们几乎永远不需要同时讨论两个不同的内存状态）。为了非正式地
    讨论例子，我们将采用一些简化约定：我们将省略开头的 [fun st =>]，并且
    只写 [X] 来表示 [st X]。因此，不写

      fun st => st X = m

    我们只写

      {{ X = m }}。
*)

(** Here the "doubly curly" braces [{{] and [}}] delimit
    the scope of an assertion.  We'll see more examples below. *)
(** 这里的"双花括号" [{{] 和 [}}] 界定了断言的范围。我们将在下面看到更多例子。 *)

(** This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Coq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)
(** 这个例子还说明了我们在整个霍尔逻辑章节中将使用的约定：在非正式断言中，
    像 [X]、[Y] 和 [Z] 这样的大写字母是 Imp 变量，而像 [x]、[y]、[m] 
    和 [n] 这样的小写字母是普通的 Coq 变量（类型为 [nat]）。这就是为什么
    在从非正式转换为正式时，我们将 [X] 替换为 [st X] 但保持 [m] 不变。 *)

(** The convention described above can be implemented in Coq with a
    little syntax magic, using coercions and annotation scopes, much
    as we did with the [<{ com }>] notation in [Imp]. This new
    notation automatically lifts [aexp]s, numbers, and [Prop]s into
    [Assertion]s when they appear in the [{{ _ }}] scope, or when Coq
    knows that the type of an expression is [Assertion].

    There is no need to understand the details of how these notation
    hacks work, so we hide them in the HTML version of the notes.  (We
    barely understand some of it ourselves!)  For the gory details,
    see the Coq development.  *)
(** 上述约定可以在 Coq 中通过一些语法魔法来实现，使用强制转换和注释作用域，
    就像我们在 [Imp] 中使用 [<{ com }>] 记号一样。这种新记号在 [aexp]、
    数字和 [Prop] 出现在 [{{ _ }}] 作用域中时，或当 Coq 知道表达式的类型
    是 [Assertion] 时，自动将它们提升为 [Assertion]。

    没有必要理解这些记号技巧如何工作的细节，所以我们在笔记的 HTML 版本中
    隐藏了它们。（我们自己也仅仅理解其中的一部分！）关于血腥的细节，
    请参见 Coq 开发。 *)

(** Define syntax notations for working with [Assertion]s *)
(** 定义用于处理 [Assertion] 的语法记号 *)

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
(** 霍尔逻辑断言的语法 *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

(** One small limitation of this approach is that we don't have
    an automatic way to coerce a function application that appears
    within an assertion to make appropriate use of the state when its
    arguments should be interpets as Imp arithmetic expressions.
    Instead, we introduce a notation [#f e1 .. en] that stands for [(fun
    st => f (e1 st) .. (en st)], letting us manually mark such function
    calls when they're needed as part of an assertion.  *)
(** 这种方法的一个小限制是，我们没有自动的方法来强制转换出现在断言中的
    函数应用，使其在参数应被解释为 Imp 算术表达式时适当地使用状态。
    相反，我们引入一个记号 [#f e1 .. en]，它表示 [(fun st => f (e1 st) .. (en st)]，
    让我们在需要作为断言的一部分时手动标记这样的函数调用。 *)

Notation "# f x .. y" := (fun st => (.. (f ((x:Aexp) st)) .. ((y:Aexp) st)))
                  (in custom assn at level 2,
                  f constr at level 0, x custom assn at level 1,
                  y custom assn at level 1) : assertion_scope.

Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : assertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : assertion_scope.

Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : assertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : assertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : assertion_scope.
Notation "a = b" := (fun st => (a:Aexp) st = (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <> b" := (fun st => (a:Aexp) st <> (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <= b" := (fun st => (a:Aexp) st <= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a < b" := (fun st => (a:Aexp) st < (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a >= b" := (fun st => (a:Aexp) st >= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a > b" := (fun st => (a:Aexp) st > (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "'True'" := True.
Notation "'True'" := (fun st => True) (in custom assn at level 0) : assertion_scope.
Notation "'False'" := False.
Notation "'False'" := (fun st => False) (in custom assn at level 0) : assertion_scope.

Notation "a + b" := (fun st => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun st => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun st => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

(** Occasionally we need to "escape" a raw "Coq-defined" function to express
    a particularly complicated assertion.  We can do that using a [$] prefix,
    as in [{{ $(raw_coq) }}].

    For example, [{{ $(fun st => forall X, st X = 0) }}] indicates an assertion that
    every variable of [X] maps to [0] in the given state.
 *)
(** 有时我们需要"转义"一个原始的"Coq定义的"函数来表达一个特别复杂的断言。
    我们可以使用 [$] 前缀来做到这一点，如 [{{ $(raw_coq) }}]。

    例如，[{{ $(fun st => forall X, st X = 0) }}] 表示一个断言，即给定状态中
    [X] 的每个变量都映射到 [0]。
 *)


Notation "$ f" := f (in custom assn at level 0, f constr at level 0) : assertion_scope.
Notation "x" := (x%assertion) (in custom assn at level 0, x constr at level 0) : assertion_scope.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "{{ e }}" := e (at level 2, e custom assn at level 99) : assertion_scope.
Open Scope assertion_scope.

(* ================================================================= *)
(** ** Example Assertions *)
(** ** 断言示例 *)

(** Here are some example assertions that take advantage of this
    new notation.
 *)
(** 这里有一些利用这种新记号的断言示例。
 *)

Module  ExamplePrettyAssertions.
Definition assertion1 : Assertion := {{ X = 3 }}.
Definition assertion2 : Assertion := {{ True }}.
Definition assertion3 : Assertion := {{ False }}.
Definition assertion4 : Assertion := {{ True \/ False }}.
Definition assertion5 : Assertion := {{ X <= Y }}.
Definition assertion6 : Assertion := {{ X = 3 \/ X <= Y }}.
Definition assertion7 : Assertion := {{ Z = (#max X Y) }}.
Definition assertion8 : Assertion := {{ Z * Z <= X
                                        /\  ~ (((# S Z) * (# S Z)) <= X) }}.
Definition assertion9 : Assertion := {{ #add X Y > #max Y X }}.
End ExamplePrettyAssertions.

(* ================================================================= *)
(** ** Assertion Implication *)
(** ** 断言蕴含 *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)
(** 给定两个断言 [P] 和 [Q]，我们说 [P] _蕴含_ [Q]，写作 [P ->> Q]，
    如果无论何时 [P] 在某个状态 [st] 中成立，[Q] 也成立。 *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

(** Note that the notation for _assertion implication_ is analogous
to the "usual" Coq implication [->]. *)
(** 注意，_断言蕴含_的记号类似于"常见的" Coq 蕴含 [->]。 *)

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.

(** We'll also want the "iff" variant of implication between
    assertions: *)
(** 我们还需要断言之间蕴含的"当且仅当"变体： *)

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.) *)
(** （这里的 [hoare_spec_scope] 注释告诉 Coq 这个记号不是全局的，
    而是意图在特定上下文中使用。） *)

(* ################################################################# *)
(** * Hoare Triples, Informally *)
(** * 霍尔三元组，非正式地 *)

(** A _Hoare triple_ is a claim about the state before and
    after executing a command.  The standard notation is

      {P} c {Q}

    meaning:

      - If command [c] begins execution in a state satisfying assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q] is
    the _postcondition_.

    Because single braces are already used for other things in Coq, we'll write
    Hoare triples with double braces:

       {{P}} c {{Q}}
*)
(** _霍尔三元组_是关于执行命令前后状态的声明。标准记号是

      {P} c {Q}

    含义是：

      - 如果命令 [c] 在满足断言 [P] 的状态中开始执行，
      - 并且如果 [c] 最终在某个最终状态中终止，
      - 那么最终状态将满足断言 [Q]。

    断言 [P] 称为三元组的_前条件_，[Q] 是_后条件_。

    由于单花括号在 Coq 中已用于其他用途，我们将用双花括号写霍尔三元组：

       {{P}} c {{Q}}
*)
(** For example,

    - [{{X = 0}} X := X + 1 {{X = 1}}] is a valid Hoare triple,
      stating that command [X := X + 1] will transform a state in
      which [X = 0] to a state in which [X = 1].

    - [forall m, {{X = m}} X := X + 1 {{X = m + 1}}] is a
      _proposition_ stating that the Hoare triple [{{X = m}} X := X +
      1 {{X = m + 1}}] is valid for any choice of [m].  Note that [m]
      in the two assertions is a reference to the _Coq_ variable [m],
      which is bound outside the Hoare triple. *)
(** 例如，

    - [{{X = 0}} X := X + 1 {{X = 1}}] 是一个有效的霍尔三元组，
      声明命令 [X := X + 1] 将把 [X = 0] 的状态转换为 [X = 1] 的状态。

    - [forall m, {{X = m}} X := X + 1 {{X = m + 1}}] 是一个_命题_，
      声明霍尔三元组 [{{X = m}} X := X + 1 {{X = m + 1}}] 对于 [m] 的
      任何选择都是有效的。注意两个断言中的 [m] 是对_Coq_变量 [m] 的引用，
      它在霍尔三元组外被绑定。 *)

(** **** Exercise: 1 star, standard, optional (triples) *)
(* FILL IN HERE

    [] *)

(** **** Exercise: 1 star, standard, optional (valid_triples)

    Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X ::= 5 {{X = 5}} 真

   2) {{X = 2}} X ::= X + 1 {{X = 3}} 真
 
   3) {{True}} X ::= 5;; Y ::= 0 {{X = 5}} 真

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}} 假错了   ⭐️ 真

   5) {{True}} SKIP {{False}} 假

   6) {{False}} SKIP {{True}} 真

   7) {{True}} WHILE true DO SKIP END {{False}} 真

   8) {{X = 0}}
        WHILE X = 0 DO X ::= X + 1 END
      {{X = 1}} 真

   9) {{X = 1}}
        WHILE ~(X = 0) DO X ::= X + 1 END
      {{X = 100}} 假
*)
(* FILL IN HERE




    [] *)

(* ################################################################# *)
(** * Hoare Triples, Formally *)

(** We can formalize valid Hoare triples in Coq as follows: *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     (P st)  ->
     (Q st').

(** Notation for Hoare triples *)

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** **** Exercise: 1 star, standard (hoare_post_true) *)

(** Prove that if [Q] holds in every state, then any triple with [Q]
    as its postcondition is valid. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold valid_hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.
(** [] *)

(** **** Exercise: 1 star, standard (hoare_pre_false) *)

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold valid_hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.
(** [] *)

(* ################################################################# *)
(** * Proof Rules *)
(** * 证明规则 *)

(** The goal of Hoare logic is to provide a _compositional_
    method for proving the validity of specific Hoare triples.  That
    is, we want the structure of a program's correctness proof to
    mirror the structure of the program itself.  To this end, in the
    sections below, we'll introduce a rule for reasoning about each of
    the different syntactic forms of commands in Imp -- one for
    assignment, one for sequencing, one for conditionals, etc. -- plus
    a couple of "structural" rules for gluing things together.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [valid_hoare_triple]. *)
(** 霍尔逻辑的目标是提供一种_组合的_方法来证明特定霍尔三元组的有效性。
    也就是说，我们希望程序正确性证明的结构反映程序本身的结构。为此，
    在下面的章节中，我们将介绍一个规则来推理 Imp 中命令的每种不同语法形式 
    —— 一个用于赋值，一个用于顺序执行，一个用于条件等等 —— 加上几个
    用于将事物粘合在一起的"结构性"规则。然后我们将能够使用这些证明规则
    来证明程序的正确性，而无需展开 [valid_hoare_triple] 的定义。 *)

(* ================================================================= *)
(** ** Skip *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)
(** 由于 [skip] 不改变状态，它保持任何断言 [P]：

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.

(* ================================================================= *)
(** ** Sequencing *)
(** ** 顺序执行 *)

(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)
(** 如果命令 [c1] 将任何满足 [P] 的状态转换为满足 [Q] 的状态，
    并且如果 [c2] 将任何满足 [Q] 的状态转换为满足 [R] 的状态，
    那么先执行 [c1] 再执行 [c2] 将把任何满足 [P] 的状态转换为满足 [R] 的状态：

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

  (** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)
  (** 注意，在形式规则 [hoare_seq] 中，前提是以逆序给出的（[c2] 在 [c1] 之前）。
      这与我们使用该规则的许多情况下信息的自然流动相匹配，因为构建霍尔逻辑
      证明的自然方式是从程序的末尾开始（使用最终后条件），然后通过命令向后
      推送后条件，直到我们到达开始。 *)(* ================================================================= *)
(** ** Assignment *)
(** ** 赋值 *)

(** The rule for assignment is the most fundamental of the Hoare
    logic proof rules.  Here's how it works.

    Consider this incomplete Hoare triple:

       {{ ??? }}  X := Y  {{ X = 1 }}

    We want to assign [Y] to [X] and finish in a state where [X] is [1].
    What could the precondition be?

    One possibility is [Y = 1], because if [Y] is already [1] then
    assigning it to [X] causes [X] to be [1].  That leads to a valid
    Hoare triple:

       {{ Y = 1 }}  X := Y  {{ X = 1 }}

    It may seem as though coming up with that precondition must have
    taken some clever thought.  But there is a mechanical way we could
    have done it: if we take the postcondition [X = 1] and in it
    replace [X] with [Y]---that is, replace the left-hand side of the
    assignment statement with the right-hand side---we get the
    precondition, [Y = 1]. *)
(** 赋值规则是霍尔逻辑证明规则中最基础的。它是这样工作的。

    考虑这个不完整的霍尔三元组：

       {{ ??? }}  X := Y  {{ X = 1 }}

    我们想要将 [Y] 赋值给 [X] 并在 [X] 为 [1] 的状态中结束。
    前条件可能是什么？

    一种可能是 [Y = 1]，因为如果 [Y] 已经是 [1]，那么将它赋值给 [X] 
    会使 [X] 为 [1]。这导致一个有效的霍尔三元组：

       {{ Y = 1 }}  X := Y  {{ X = 1 }}

    看起来想出那个前条件必须经过一些巧妙的思考。但是有一个机械的方法
    我们可以做到：如果我们取后条件 [X = 1] 并在其中用 [Y] 替换 [X]
    ——也就是说，用赋值语句的右边替换左边——我们得到前条件 [Y = 1]。 *)

(** That same idea works in more complicated cases.  For
    example:

       {{ ??? }}  X := X + Y  {{ X = 1 }}

    If we replace the [X] in [X = 1] with [X + Y], we get [X + Y = 1].
    That again leads to a valid Hoare triple:

       {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}

    Why does this technique work?  The postcondition identifies some
    property [P] that we want to hold of the variable [X] being
    assigned.  In this case, [P] is "equals [1]".  To complete the
    triple and make it valid, we need to identify a precondition that
    guarantees that property will hold of [X].  Such a precondition
    must ensure that the same property holds of _whatever is being
    assigned to_ [X].  So, in the example, we need "equals [1]" to
    hold of [X + Y].  That's exactly what the technique guarantees. *)
(** 同样的想法在更复杂的情况下也有效。例如：

       {{ ??? }}  X := X + Y  {{ X = 1 }}

    如果我们在 [X = 1] 中用 [X + Y] 替换 [X]，我们得到 [X + Y = 1]。
    这再次导致一个有效的霍尔三元组：

       {{ X + Y = 1 }}  X := X + Y  {{ X = 1 }}

    为什么这种技术有效？后条件确定了我们希望被赋值的变量 [X] 保持的某个
    性质 [P]。在这种情况下，[P] 是"等于 [1]"。为了完成三元组并使其有效，
    我们需要确定一个前条件来保证该性质将在 [X] 上成立。这样的前条件必须
    确保相同的性质在_被赋值给_ [X] 的任何内容上成立。因此，在这个例子中，
    我们需要"等于 [1]"在 [X + Y] 上成立。这正是该技术所保证的。 *)


(** In general, the postcondition could be some arbitrary assertion
    [Q], and the right-hand side of the assignment could be some
    arbitrary arithmetic expression [a]:

       {{ ??? }}  X := a  {{ Q }}

    The precondition would then be [Q], but with any occurrences of
    [X] in it replaced by [a].

    Let's introduce a notation for this idea of replacing occurrences:
    Define [Q [X |-> a]] to mean "[Q] where [a] is substituted in
    place of [X]".

    This yields the Hoare logic rule for assignment:

      {{ Q [X |-> a] }}  X := a  {{ Q }}

    One way of reading this rule is: If you want statement [X := a]
    to terminate in a state that satisfies assertion [Q], then it
    suffices to start in a state that also satisfies [Q], except
    where [a] is substituted for every occurrence of [X]. *)
(** 一般来说，后条件可以是某个任意断言 [Q]，赋值的右边可以是某个任意
    算术表达式 [a]：

       {{ ??? }}  X := a  {{ Q }}

    那么前条件就是 [Q]，但是将其中任何 [X] 的出现都替换为 [a]。

    让我们为这种替换出现的想法引入一个记号：
    定义 [Q [X |-> a]] 表示"[Q] 中 [a] 替换 [X] 的位置"。

    这产生了赋值的霍尔逻辑规则：

      {{ Q [X |-> a] }}  X := a  {{ Q }}

    读这个规则的一种方式是：如果你想要语句 [X := a] 在满足断言 [Q] 的
    状态中终止，那么在也满足 [Q] 的状态中开始就足够了，除了用 [a] 替换
    [X] 的每个出现。 *)

(** To many people, this rule seems "backwards" at first, because
    it proceeds from the postcondition to the precondition.  Actually
    it makes good sense to go in this direction: the postcondition is
    often what is more important, because it characterizes what we
    can assume afer running the code.

    Nonetheless, it's also possible to formulate a "forward" assignment
    rule.  We'll do that later in some exercises. *)
(** 对许多人来说，这个规则起初似乎是"反向的"，因为它从后条件推向前条件。
    实际上，朝这个方向进行是很有意义的：后条件通常更重要，因为它刻画了
    运行代码后我们可以假设的内容。

    尽管如此，也可以表述一个"正向"赋值规则。我们将在后面的练习中这样做。 *)

(** Here are some valid instances of the assignment rule:

      {{ (X <= 5) [X |-> X + 1] }}   (that is, X + 1 <= 5)
        X := X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3] }}        (that is, 3 = 3)
        X := 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]  (that is, 0 <= 3 /\ 3 <= 5)
        X := 3
      {{ 0 <= X /\ X <= 5 }}
*)
(** 这里是赋值规则的一些有效实例：

      {{ (X <= 5) [X |-> X + 1] }}   (即 X + 1 <= 5)
        X := X + 1
      {{ X <= 5 }}

      {{ (X = 3) [X |-> 3] }}        (即 3 = 3)
        X := 3
      {{ X = 3 }}

      {{ (0 <= X /\ X <= 5) [X |-> 3]  (即 0 <= 3 /\ 3 <= 5)
        X := 3
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assertion_sub].  That
    is, intuitively, given a proposition [P], a variable [X], and an
    arithmetic expression [a], we want to derive another proposition
    [P'] that is just the same as [P] except that [P'] should mention
    [a] wherever [P] mentions [X]. *)
(** 为了形式化这个规则，我们必须首先形式化"在断言中用表达式替换 Imp 变量"
    的想法，我们称之为断言替换，或 [assertion_sub]。也就是说，直觉上，
    给定一个命题 [P]、一个变量 [X] 和一个算术表达式 [a]，我们想要推导
    另一个命题 [P']，它与 [P] 完全相同，除了 [P'] 应该在 [P] 提及 [X] 
    的地方提及 [a]。 *)

(** This operation is related to the idea of substituting Imp
    expressions for Imp variables that we saw in [Equiv]
    ([subst_aexp] and friends). The difference is that, here,
    [P] is an arbitrary Coq assertion, so we can't directly
    "edit" its text. *)
(** 这个操作与我们在 [Equiv] 中看到的用 Imp 表达式替换 Imp 变量的想法
    相关（[subst_aexp] 及其同类）。区别在于，这里 [P] 是一个任意的 Coq 
    断言，所以我们不能直接"编辑"它的文本。 *)

(** However, we can achieve the same effect by evaluating [P] in an
    updated state, defined as follows: *)
(** 但是，我们可以通过在更新的状态中求值 [P] 来达到同样的效果，定义如下： *)

Definition assertion_sub X (a:aexp) (P:Assertion) : Assertion :=
  fun (st : state) =>
    (P%_assertion) (X !-> ((a:Aexp) st); st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
                              (in custom assn at level 10, left associativity, P custom assn, X global, a custom com) : assertion_scope.

(**  This notation allows us to write this operation as:

     [P[ X |-> a]]
*)
(**  这个记号允许我们将这个操作写作：

     [P[ X |-> a]]
*)

(** That is, [P [X |-> a]] stands for an assertion -- let's call it
    [P'] -- that is just like [P] except that, wherever [P] looks up
    the variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)
(** 也就是说，[P [X |-> a]] 表示一个断言——我们称它为 [P']——它与 [P] 
    完全相同，除了在 [P] 在当前状态中查找变量 [X] 的任何地方，[P'] 
    都使用表达式 [a] 的值。 *)

(** To see how this works in more detail, let's calculate what happens with a couple
    of examples.  First, suppose [P'] is [(X <= 5) [X |-> 3]] -- that
    is, more formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),

    which simplifies to

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)

    and further simplifies to

    fun st =>
      ((X !-> 3 ; st) X) <= 5

    and finally to

    fun st =>
      3 <= 5.

    That is, [P'] is the assertion that [3] is less than or equal to
    [5] (as expected). *)
(** 为了更详细地了解这是如何工作的，让我们计算几个例子会发生什么。
    首先，假设 [P'] 是 [(X <= 5) [X |-> 3]] —— 也就是说，更正式地，
    [P'] 是 Coq 表达式

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st 3 ; st),

    它简化为

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> 3 ; st)

    进一步简化为

    fun st =>
      ((X !-> 3 ; st) X) <= 5

    最后简化为

    fun st =>
      3 <= 5.

    也就是说，[P'] 是断言 [3] 小于或等于 [5]（如预期的那样）。 *)

(** For a more interesting example, suppose [P'] is [(X <= 5) [X |->
    X + 1]].  Formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    which simplifies to

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    and further simplifies to

    fun st =>
      (aeval st (X + 1)) <= 5.

    That is, [P'] is the assertion that [X + 1] is at most [5].
*)
(** 对于一个更有趣的例子，假设 [P'] 是 [(X <= 5) [X |-> X + 1]]。
    形式上，[P'] 是 Coq 表达式

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    它简化为

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    进一步简化为

    fun st =>
      (aeval st (X + 1)) <= 5.

    也就是说，[P'] 是断言 [X + 1] 最多为 [5]。
*)

(** We can demonstrate formally that we have captured intuitive meaning of
    "assertion subsitution" by proving some example logical equivalences: *)
(** 我们可以通过证明一些逻辑等价的例子来形式化地证明我们已经捕获了
    "断言替换"的直觉含义： *)

Module ExampleAssertionSub.
Example equivalent_assertion1 :
  {{ (X <= 5) [X |-> 3] }} <<->> {{ 3 <= 5 }}.
Proof.
  split; unfold assert_implies, assertion_sub; intros st H; simpl in *; apply H.
Qed.

Example equivalent_assertion2 :
  {{ (X <= 5) [X |-> X + 1] }} <<->> {{ (X + 1) <= 5 }}.
Proof.
  split; unfold assert_implies, assertion_sub; intros st H; simpl in *; apply H.
Qed.
End ExampleAssertionSub.

(** Now, using the substitution operation we've just defined, we can
    give the precise proof rule for assignment:

      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
*)
(** 现在，使用我们刚刚定义的替换操作，我们可以给出赋值的精确证明规则：

      ---------------------------- (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)
(** 我们可以形式化地证明这个规则确实是有效的。 *)

Theorem hoare_asgn : forall Q X (a:aexp),
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. simpl in HQ. assumption.  Qed.

(** Here's a first formal proof using this rule. *)
(** 这是使用这个规则的第一个形式化证明。 *)

Example assertion_sub_example :
  {{(X < 5) [X |-> X + 1]}}
    X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_asgn.  Qed.

(** Of course, what we'd probably prefer is to prove this
    simpler triple:

      {{X < 4}} X := X + 1 {{X < 5}}

   We will see how to do so in the next section. *)
(** 当然，我们可能更愿意证明这个更简单的三元组：

      {{X < 4}} X := X + 1 {{X < 5}}

   我们将在下一节中看到如何做到这一点。 *)

(** Complete these Hoare triples by providing an appropriate
    precondition using [exists], then prove then with [apply
    hoare_asgn]. If you find that tactic doesn't suffice, double check
    that you have completed the triple properly. *)
(** 通过使用 [exists] 提供适当的前条件来完成这些霍尔三元组，然后用 
    [apply hoare_asgn] 来证明。如果你发现该策略不够用，请再次检查你是否
    正确地完成了三元组。 *)

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples1) *)
Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  (* 注意格式霍尔三元组的格式 *)
  exists {{(X <= 10) [X |-> 2 * X]}}.
  apply hoare_asgn.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples2) *)
Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <=  X /\ X <= 5 }}.
Proof. 
  exists {{(0 <= X /\ X <= 5) [X |-> 3]}}.
  apply hoare_asgn.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (hoare_asgn_wrong) *)
(** **** 练习：2 星，标准，特别有用 (hoare_asgn_wrong) *)

(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems puzzling to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X := a {{ X = a }}

    Give a counterexample showing that this rule is incorrect and use
    it to complete the proof below, showing that it is really a
    counterexample.  (Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work.) *)
(** 赋值规则对几乎每个第一次看到它的人来说都显得是"反向的"。如果它对你
    来说仍然令人困惑，思考一些替代的"正向"规则可能会有帮助。这里是一个
    看似自然的规则：

      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X := a {{ X = a }}

    给出一个反例来说明这个规则是不正确的，并用它来完成下面的证明，表明
    它确实是一个反例。（提示：这个规则对算术表达式 [a] 进行全称量化，
    你的反例需要展示一个使规则不起作用的 [a]。） *)

Theorem hoare_asgn_wrong : exists a:aexp,
  ~ {{ True }} X := a {{ X = a }}.
Proof.
  (* 反例：a = X + 1 *)
  exists <{ X + 1 }>.
  unfold not, valid_hoare_triple. intro H.
  (* 考虑空状态 empty_st，其中所有变量都是 0 *)
  assert (Hexec: empty_st =[ X := X + 1 ]=> (X !-> 1; empty_st)).
  { apply E_Asgn. reflexivity. }
  (* 根据假设的错误规则，后条件应该成立 *)
  (* specialize 用于将一个全称量化的假设应用到具体的参数上。 *)
  (* empty_st：初始状态
  (X !-> 1; empty_st)：最终状态
  Hexec：证明 empty_st =[ X := X + 1 ]=> (X !-> 1; empty_st)
  I：True 的证明（I 是 True 的构造子） *)

  specialize (H empty_st (X !-> 1; empty_st) Hexec I).
  (* 在最终状态中：X = 1，但 aeval (X !-> 1; empty_st) (X + 1) = 1 + 1 = 2 *)
  simpl in H.
  rewrite t_update_eq in H.
  (* H 现在是 1 = 2，这是矛盾 *)
  discriminate H.
Qed.
(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, advanced (hoare_asgn_fwd)
(** **** 练习：3 星，高级 (hoare_asgn_fwd)

    By using a _parameter_ [m] (a Coq number) to remember the
    original value of [X] we can define a Hoare rule for assignment
    that does, intuitively, "work forwards" rather than backwards.

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}

    Note that we need to write out the postcondition in "desugared"
    form, because it needs to talk about two different states: we use
    the original value of [X] to reconstruct the state [st'] before the
    assignment took place.  (Also note that this rule is more complicated
    than [hoare_asgn]!)

    Prove that this rule is correct. *)
    通过使用一个_参数_ [m]（一个 Coq 数字）来记住 [X] 的原始值，我们可以
    定义一个赋值的霍尔规则，该规则直觉上是"正向工作的"而不是反向的。

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X := a
       {{fun st => P (X !-> m ; st) /\ st X = aeval (X !-> m ; st) a }}

    注意我们需要以"去糖"形式写出后条件，因为它需要讨论两个不同的状态：
    我们使用 [X] 的原始值来重建赋值发生之前的状态 [st']。（还要注意
    这个规则比 [hoare_asgn] 更复杂！）

    证明这个规则是正确的。 *)
Require Import FunctionalExtensionality.
Theorem hoare_asgn_fwd :
  forall (m:nat) (a:aexp) (P : Assertion),
  {{P /\ X = m}}
    X := a
  {{ $(fun st => (P (X !-> m ; st)
             /\ st X = aeval (X !-> m ; st) a))  }}.
Proof.
  unfold valid_hoare_triple.  
  intros m a P st st' Hpre Heval.
  inversion Heval; subst.
  split.
  -
  (* 在中文版本中证明成功了，迁移到现在的新版本出现问题，正在排查 *)

Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced, optional (hoare_asgn_fwd_exists)
(** **** 练习：2 星，高级，可选 (hoare_asgn_fwd_exists)

    Another way to define a forward rule for assignment is to
    existentially quantify over the previous value of the assigned
    variable.  Prove that it is correct.

      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X := a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
*)
    定义赋值正向规则的另一种方法是对被赋值变量的先前值进行存在量化。
    证明它是正确的。

      ------------------------------------ (hoare_asgn_fwd_exists)
      {{fun st => P st}}
        X := a
      {{fun st => exists m, P (X !-> m ; st) /\
                     st X = aeval (X !-> m ; st) a }}
*)

Theorem hoare_asgn_fwd_exists :
  forall a (P : Assertion),
  {{ P }}
    X := a
  {{ $(fun st => exists m, P (X !-> m ; st) /\
                st X = aeval (X !-> m ; st) a) }}.
Proof.
  intros a P.
  unfold valid_hoare_triple.
  intros st st' H_exec H_pre.
  
  (* 分析赋值的执行 *)
  inversion H_exec; subst.
  clear H_exec.
  
  (* 现在目标状态是 (X !-> aeval st a; st) *)
  (* 我们需要证明后置条件在这个状态中成立 *)
  
  (* 选择 m = st X，即 X 在原始状态中的值 *)
  exists (st X).
  split.
  
  - (* 证明 P (X !-> st X; X !-> aeval st a; st) *)
    (* 关键观察：(X !-> st X; X !-> aeval st a; st) = (X !-> st X; st) *)
    (* 因为第二个更新会覆盖第一个更新 *)
    
    assert (H_eq: (X !-> st X; X !-> aeval st a; st) = (X !-> st X; st)).
    {
      unfold t_update.
      apply functional_extensionality.
      intros y.
      destruct (String.eqb X y) eqn:Heq.
      - (* X = y 的情况 *)
        reflexivity.
      - (* X <> y 的情况 *)
        reflexivity.
    }
    
    rewrite H_eq.
    
    (* 现在我们需要证明 P (X !-> st X; st) *)
    (* 这等于 P st，因为用相同值更新不改变状态 *)
    assert (H_st_eq: (X !-> st X; st) = st).
    {
      unfold t_update.
      apply functional_extensionality.
      intros y.
      destruct (String.eqb X y) eqn:Heq.
      - (* X = y *)
        apply String.eqb_eq in Heq.
        subst.
        reflexivity.
      - (* X <> y *)
        reflexivity.
    }
    
    rewrite H_st_eq.
    exact H_pre.
    
  - (* 证明 (X !-> aeval st a; st) X = aeval (X !-> st X; X !-> aeval st a; st) a *)
    (* 左边：(X !-> aeval st a; st) X = aeval st a *)
    (* 右边：aeval (X !-> st X; X !-> aeval st a; st) a = aeval (X !-> st X; st) a *)
    
    (* 首先简化左边 *)
    rewrite t_update_eq.
    
    (* 然后简化右边，使用前面的等式 *)
    assert (H_eq: (X !-> st X; X !-> aeval st a; st) = (X !-> st X; st)).
    {
      unfold t_update.
      apply functional_extensionality.
      intros y.
      destruct (String.eqb X y) eqn:Heq.
      - reflexivity.
      - reflexivity.
    }
    
    rewrite H_eq.
    
    (* 现在需要证明 aeval st a = aeval (X !-> st X; st) a *)
    (* 由于 (X !-> st X; st) = st，这是显然的 *)
    assert (H_st_eq: (X !-> st X; st) = st).
    {
      unfold t_update.
      apply functional_extensionality.
      intros y.
      destruct (String.eqb X y) eqn:Heq.
      - apply String.eqb_eq in Heq.
        subst.
        reflexivity.
      - reflexivity.
    }
    
    rewrite H_st_eq.
    reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Consequence *)
(** ** 推理 *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. *)
(** 有时我们从霍尔规则得到的前条件和后条件并不完全是我们在特定情况下
    想要的——它们可能在逻辑上等价但具有不同的语法形式，无法与我们试图
    证明的目标统一，或者它们实际上在逻辑上可能比我们需要的更弱（对于
    前条件）或更强（对于后条件）。 *)

(** For instance,

      {{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

    follows directly from the assignment rule, but

      {{True}} X := 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.

    However, they are logically _equivalent_, so if one triple is
    valid, then the other must certainly be as well.  We can capture
    this observation with the following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)
(** 例如，

      {{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

    直接从赋值规则得出，但是

      {{True}} X := 3 {{X = 3}}

    却不行。这个三元组是有效的，但它不是 [hoare_asgn] 的实例，因为 [True] 
    和 [(X = 3) [X |-> 3]] 在语法上不是相等的断言。

    然而，它们在逻辑上是_等价的_，所以如果一个三元组是有效的，那么另一个
    肯定也是有效的。我们可以用下面的规则来捕获这个观察：

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)
(** 进一步发展这种思路，我们可以看到加强有效三元组的前条件或削弱后条件
    总是产生另一个有效三元组。这个观察被两个_推理规则_所捕获。

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)
(** 这里是形式化版本： *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

(** For example, we can use the first consequence rule like this:

    {{ True }} ->>
    {{ (X = 1) [X |-> 1] }}
      X := 1
    {{ X = 1 }}

    Or, formally... *)
(** 例如，我们可以像这样使用第一个推理规则：

    {{ True }} ->>
    {{ (X = 1) [X |-> 1] }}
      X := 1
    {{ X = 1 }}

    或者，形式化地... *)

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  (* WORKED IN CLASS *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update; simpl.
    intros st _. reflexivity.
Qed.

(** We can also use it to prove the example mentioned earlier.

    {{ X < 4 }} ->>
    {{ (X < 5)[X |-> X + 1] }}
      X := X + 1
    {{ X < 5 }}

   Or, formally ... *)
(** 我们也可以用它来证明前面提到的例子。

    {{ X < 4 }} ->>
    {{ (X < 5)[X |-> X + 1] }}
      X := X + 1
    {{ X < 5 }}

   或者，形式化地... *)

Example assertion_sub_example2 :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  (* WORKED IN CLASS *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** Finally, here is a combined rule of consequence that allows us to
    vary both the precondition and the postcondition.

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)
(** 最后，这里是一个组合的推理规则，允许我们同时改变前条件和后条件。

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q'); assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Automation *)
(** ** 自动化 *)

(** Many of the proofs we have done so far with Hoare triples can be
    streamlined using the automation techniques that we introduced in
    the [Auto] chapter of _Logical Foundations_.

    Recall that the [auto] tactic can be told to [unfold] definitions
    as part of its proof search.  Let's give it that hint for the
    definitions and coercions we're using: *)
(** 到目前为止我们用霍尔三元组做的许多证明都可以使用我们在《逻辑基础》
    的 [Auto] 章节中介绍的自动化技术来简化。

    回想一下，[auto] 策略可以被告知将 [unfold] 定义作为其证明搜索的一部分。
    让我们为我们正在使用的定义和强制转换给它这个提示： *)

Hint Unfold assert_implies assertion_sub t_update : core.
Hint Unfold valid_hoare_triple : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(** Also recall that [auto] will search for a proof involving [intros]
    and [apply].  By default, the theorems that it will apply include
    any of the local hypotheses, as well as theorems in a core
    database. *)
(** 还要记住，[auto] 将搜索涉及 [intros] 和 [apply] 的证明。默认情况下，
    它将应用的定理包括任何局部假设，以及核心数据库中的定理。 *)

(** The proof of [hoare_consequence_pre], repeated below, looks
    like an opportune place for such automation, because all it does
    is [unfold], [intros], and [apply].  (It uses [assumption], too,
    but that's just application of a hypothesis.) *)
(** 下面重复的 [hoare_consequence_pre] 的证明看起来是这种自动化的好地方，
    因为它所做的就是 [unfold]、[intros] 和 [apply]。（它也使用 [assumption]，
    但那只是假设的应用。） *)

Theorem hoare_consequence_pre' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

(** Merely using [auto], though, doesn't complete the proof. *)
(** 然而，仅仅使用 [auto] 并不能完成证明。 *)

Theorem hoare_consequence_pre'' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  auto. (* no progress *)
Abort.

(** The problem is the [apply Hhoare with...] part of the proof.  Coq
    isn't able to figure out how to instantiate [st] without some help
    from us.  Recall, though, that there are versions of many tactics
    that will use _existential variables_ to make progress even when
    the regular versions of those tactics would get stuck.

    Here, the [eapply] tactic will introduce an existential variable
    [?st] as a placeholder for [st], and [eassumption] will
    instantiate [?st] with [st] when it discovers [st] in assumption
    [Heval].  By using [eapply] we are essentially telling Coq, "Be
    patient: The missing part is going to be filled in later in the
    proof." *)
(** 问题在于证明的 [apply Hhoare with...] 部分。Coq 无法在没有我们帮助的
    情况下弄清楚如何实例化 [st]。但是回想一下，许多策略都有使用_存在变量_
    的版本，即使这些策略的常规版本会卡住，它们也能取得进展。

    这里，[eapply] 策略将引入一个存在变量 [?st] 作为 [st] 的占位符，
    而 [eassumption] 会在假设 [Heval] 中发现 [st] 时用 [st] 实例化 [?st]。
    通过使用 [eapply]，我们本质上是在告诉 Coq："耐心点：缺失的部分将在
    证明的后面填入。" *)

Theorem hoare_consequence_pre''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold valid_hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  eapply Hhoare.
  - eassumption.
  - apply Himp. assumption.
Qed.

(** The [eauto] tactic will use [eapply] as part of its proof search.
    So, the entire proof can actually be done in just one line. *)
(** [eauto] 策略将使用 [eapply] 作为其证明搜索的一部分。
    所以，整个证明实际上可以在一行中完成。 *)

Theorem hoare_consequence_pre'''' : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** Of course, it's hard to predict that [eauto] suffices here
    without having gone through the original proof of
    [hoare_consequence_pre] to see the tactics it used. But now that
    we know [eauto] worked there, it's a good bet that it will also
    work for [hoare_consequence_post]. *)
(** 当然，如果没有经历 [hoare_consequence_pre] 的原始证明来查看它使用的
    策略，很难预测 [eauto] 在这里就足够了。但现在我们知道 [eauto] 在那里
    起作用了，很有可能它也会对 [hoare_consequence_post] 起作用。 *)

Theorem hoare_consequence_post' : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

(** We can also use [eapply] to streamline a
    proof ([hoare_asgn_example1]), that we did earlier as an example
    of using the consequence rule: *)
(** 我们也可以使用 [eapply] 来简化一个证明（[hoare_asgn_example1]），
    我们之前将其作为使用推理规则的例子： *)

Example hoare_asgn_example1' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre. (* no need to state an assertion *)
  - apply hoare_asgn.
  - unfold "->>", assertion_sub, t_update.
    intros st _. simpl. reflexivity.
Qed.

(** The final bullet of that proof also looks like a candidate for
    automation. *)
(** 该证明的最后一个项目符号看起来也是自动化的候选。 *)

Example hoare_asgn_example1'' :
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto.
Qed.

(** Now we have quite a nice proof script: it simply identifies the
    Hoare rules that need to be used and leaves the remaining
    low-level details up to Coq to figure out. *)
(** 现在我们有了一个相当不错的证明脚本：它只是识别需要使用的霍尔规则，
    并将剩余的低级细节留给 Coq 来解决。 *)

(** By now it might be apparent that the _entire_ proof could be
    automated if we added [hoare_consequence_pre] and [hoare_asgn] to
    the hint database.  We won't do that in this chapter, so that we
    can get a better understanding of when and how the Hoare rules are
    used.  In the next chapter, [Hoare2], we'll dive deeper into
    automating entire proofs of Hoare triples. *)
(** 到现在为止，如果我们将 [hoare_consequence_pre] 和 [hoare_asgn] 添加到
    提示数据库中，_整个_证明都可以自动化，这一点可能已经很明显了。我们在
    本章中不会这样做，这样我们可以更好地理解何时以及如何使用霍尔规则。
    在下一章 [Hoare2] 中，我们将更深入地研究霍尔三元组整个证明的自动化。 *)

(** The other example of using consequence that we did earlier,
    [hoare_asgn_example2], requires a little more work to automate.
    We can streamline the first line with [eapply], but we can't just use
    [auto] for the final bullet, since it needs [lia]. *)
(** 我们之前做的使用推理的另一个例子 [hoare_asgn_example2] 需要更多的工作
    来自动化。我们可以用 [eapply] 简化第一行，但我们不能只对最后一个项目
    符号使用 [auto]，因为它需要 [lia]。 *)

Example assertion_sub_example2' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - auto. (* no progress *)
    unfold "->>", assertion_sub, t_update.
    intros st H. simpl in *. lia.
Qed.

(** Let's introduce our own tactic to handle both that bullet and the
    bullet from example 1: *)
(** 让我们引入我们自己的策略来处理那个项目符号和例子1中的项目符号： *)

Ltac assertion_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assertion_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assertion_sub_example2'' :
  {{X < 4}}
    X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assertion_auto.
Qed.

(** Again, we have quite a nice proof script.  All the low-level
    details of proofs about assertions have been taken care of
    automatically. Of course, [assertion_auto] isn't able to prove
    everything we could possibly want to know about assertions --
    there's no magic here! But it's good enough so far. *)
(** 再次，我们有了一个相当不错的证明脚本。关于断言证明的所有低级细节
    都已经自动处理了。当然，[assertion_auto] 无法证明我们可能想要了解
    的关于断言的所有内容——这里没有魔法！但到目前为止已经足够好了。 *)

(** **** Exercise: 2 stars, standard (hoare_asgn_examples_2)
(** **** 练习：2 星，标准 (hoare_asgn_examples_2)

    Prove these triples.  Try to make your proof scripts nicely
    automated by following the examples above. *)
    证明这些三元组。尝试通过遵循上面的例子使你的证明脚本很好地自动化。 *)

Example assertion_sub_ex1' :
  {{ X <= 5 }}
    X := 2 * X
  {{ X <= 10 }}.
Proof.
  (* 使用前置条件加强和赋值规则 *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - (* 证明 X <= 5 ->> (X <= 10)[X |-> 2 * X] *)
    (* 即证明 X <= 5 ->> 2 * X <= 10 *)
    unfold "->>", t_update.
    simpl.
    intros st H.
    unfold assertion_sub.
    simpl.
    rewrite t_update_eq.
    (* 现在目标是 2 * st X <= 10 *)
    lia.


Qed.

Example assertion_sub_ex2' :
  {{ 0 <= 3 /\ 3 <= 5 }}
    X := 3
  {{ 0 <= X /\ X <= 5 }}.
Proof.
  (* 使用前置条件加强和赋值规则 *)
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - (* 证明 0 <= 3 /\ 3 <= 5 ->> (0 <= X /\ X <= 5)[X |-> 3] *)
    (* 即证明 0 <= 3 /\ 3 <= 5 ->> 0 <= 3 /\ 3 <= 5 *)
    unfold "->>", t_update.
    simpl.
    intros st H.
    exact H. (* 前置条件和后置条件替换后完全相同 *)
Qed.

(** [] *)

(* ================================================================= *)
(** ** Sequencing + Assignment *)
(** ** 顺序执行 + 赋值 *)

(** Here's an example of a program involving both sequencing and
    assignment.  Note the use of [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic. *)
(** 这里是一个涉及顺序执行和赋值的程序例子。注意 [hoare_seq] 与 
    [hoare_consequence_pre] 和 [eapply] 策略的结合使用。 *)

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
  {{a = n}}
    X := a;
    skip
  {{X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

  {{ a = n }}
     X := a
              {{ X = n }};    <--- decoration for Q
     skip
  {{ X = n }}
*)
(** We'll come back to the idea of decorated programs in much more
    detail in the next chapter. *)
(** 非正式地，使用顺序执行规则显示证明的一个好方法是作为"修饰程序"，
    其中中间断言 [Q] 写在 [c1] 和 [c2] 之间：

  {{ a = n }}
     X := a
              {{ X = n }};    <--- Q 的修饰
     skip
  {{ X = n }}
*)
(** 我们将在下一章中更详细地回到修饰程序的想法。 *)

(** **** Exercise: 2 stars, standard, especially useful (hoare_asgn_example4)
(** **** 练习：2 星，标准，特别有用 (hoare_asgn_example4)

    Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X := 1
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }};
    Y := 2
                   {{ X = 1 /\ Y = 2 }}

   Note the use of "[->>]" decorations, each marking a use of
   [hoare_consequence_pre].

   We've started you off by providing a use of [hoare_seq] that
   explicitly identifies [X = 1] as the intermediate assertion. *)
    将这个"修饰程序"翻译成形式化证明：

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X := 1
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }};
    Y := 2
                   {{ X = 1 /\ Y = 2 }}

   注意 "[->>]" 修饰的使用，每个都标记了 [hoare_consequence_pre] 的使用。

   我们通过提供 [hoare_seq] 的使用来帮你开始，它明确地将 [X = 1] 
   标识为中间断言。 *)

Example hoare_asgn_example4 :
  {{ True }}
    X := 1;
    Y := 2
  {{ X = 1 /\ Y = 2 }}.
Proof.
  eapply hoare_seq with (Q := {{ X = 1 }}).
  
  - (* 证明第一个命令：{{ True }} X := 1 {{ X = 1 }} *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + (* 证明 True ->> (X = 1)[X |-> 1] *)
      (* 即证明 True ->> 1 = 1 *)
      unfold "->>", assertion_sub.
      simpl.
      intros st H.
      rewrite t_update_eq.
      split.
      -- (* 证明 (Y !-> 2; st) X = 1 *)
        rewrite t_update_neq.
        ++ exact H.
        ++ discriminate. (* "Y" <> "X" *)
      -- (* 证明 2 = 2 *)
        reflexivity.
  
  - (* 证明第二个命令：{{ X = 1 }} Y := 2 {{ X = 1 /\ Y = 2 }} *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + (* 证明 X = 1 ->> (X = 1 /\ Y = 2)[Y |-> 2] *)
      (* 即证明 X = 1 ->> X = 1 /\ 2 = 2 *)
      unfold "->>", assertion_sub.
      simpl.
      intros st H.
      auto.

Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_exercise)

    Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      {{X <= Y}} c {{Y <= X}}

    Your proof should not need to use [unfold valid_hoare_triple].

    Hints:
       - Remember that Imp commands need to be enclosed in <{...}>
         brackets.
       - Remember that the assignment rule works best when it's
         applied "back to front," from the postcondition to the
         precondition.  So your proof will want to start at the end
         and work back to the beginning of your program.
       - Remember that [eapply] is your friend.)  *)

Definition swap_program : com :=
  <{ Z := X;
     X := Y;
     Y := Z }>.

Theorem swap_exercise :
  {{X <= Y}}
    swap_program
  {{Y <= X}}.
Proof.
  unfold swap_program.
  
  (* 使用序列规则，从后往前分析 *)
  eapply hoare_seq with (Q := {{ X <= Z /\ Y = Z }}).
  (* eapply hoare_seq with (Q := {{ Y <= Z /\ X = Y }}). *)
  
  - (* 第一个命令：{{ X <= Y }} Z := X {{ Y <= Z /\ X = Y }} *)
    eapply hoare_seq with (Q := {{ Z <= Y }}).
    + (* 第一个子目标：{{ (Z <= X)[X |-> Y] }} X := Y {{ Z <= Y }} *)
      admit.
Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (invalid_triple)

    Show that

    {{ a = n }} X := 3; Y := a {{ Y = n }}

    is not a valid Hoare triple for some choices of [a] and [n].

    Conceptual hint: Invent a particular [a] and [n] for which the
    triple in invalid, then use those to complete the proof.

    Technical hint: Hypothesis [H] below begins [forall a n, ...].
    You'll want to instantiate that with the particular [a] and [n]
    you've invented.  You can do that with [assert] and [apply], but
    you may remember (from [Tactics.v] in Logical Foundations)
    that Coq offers an even easier tactic: [specialize].  If you write

       specialize H with (a := your_a) (n := your_n)

    the hypothesis will be instantiated on [your_a] and [your_n].

    Having chosen your [a] and [n], proceed as follows:
     - Use the (assumed) validity of the given hoare triple to derive
       a state [st'] in which [Y] has some value [y1]
     - Use the evaluation rules ([E_Seq] and [E_Asgn]) to show that
       [Y] has a _different_ value [y2] in the same final state [st']
     - Since [y1] and [y2] are both equal to [st' Y], they are equal
       to each other. But we chose them to be different, so this is a
       contradiction, which finishes the proof.
 *)

Theorem invalid_triple : ~ forall (a : aexp) (n : nat),
    {{ a = n }}
      X := 3; Y := a
    {{ Y = n }}.
Proof.
  unfold valid_hoare_triple.
  intros H.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} if b then c1 else c2 {{Q}}
*)

(** However, this is rather weak. For example, using this rule,
   we cannot show

     {{ True }}
       if X = 0
         then Y := 2
         else Y := X + 1
       end
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]).

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
*)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassertion b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Arguments bassertion /.

(** A useful fact about [bassertion]: *)

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

(** We mentioned the [congruence] tactic in passing in
    [Auto] when building the [find_rwd] tactic.  Like
    [find_rwd], [congruence] is able to automatically find that both
    [beval st b = false] and [beval st b = true] are being assumed,
    notice the contradiction, and [discriminate] to complete the
    proof. *)

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassertion b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassertion b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** Here is a formal proof that the program we used to motivate
    the rule satisfies the specification we gave. *)

Example if_example :
  {{True}}
    if (X = 0)
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto. (* no progress *)
      unfold "->>", assertion_sub, t_update, bassertion.
      simpl. intros st [_ H]. apply eqb_eq in H.
      rewrite H. lia.
  - (* Else *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto.
Qed.

(** As we did earlier, it would be nice to eliminate all the low-level
    proof script that isn't about the Hoare rules.  Unfortunately, the
    [assertion_auto] tactic we wrote wasn't quite up to the job.  Looking
    at the proof of [if_example], we can see why.  We had to unfold a
    definition ([bassertion]) and use a theorem ([eqb_eq]) that we didn't
    need in earlier proofs.  So, let's add those into our tactic, and
    clean it up a little in the process. *)

Ltac assertion_auto' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *; (* for equalities *)
  auto; try lia.

(** Now the proof is quite streamlined. *)

Example if_example'' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
  - eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto'.
Qed.

(** We can even shorten it a little bit more. *)

Example if_example''' :
  {{True}}
    if X = 0
      then Y := 2
      else Y := X + 1
    end
  {{X <= Y}}.
Proof.
  apply hoare_if; eapply hoare_consequence_pre;
    try apply hoare_asgn; try assertion_auto'.
Qed.

(** For later proofs, it will help to extend [assertion_auto'] to handle
    inequalities, too. *)

Ltac assertion_auto'' :=
  unfold "->>", assertion_sub, t_update, bassertion;
  intros; simpl in *;
  try rewrite -> eqb_eq in *;
  try rewrite -> leb_le in *;  (* for inequalities *)
  auto; try lia.

(** **** Exercise: 2 stars, standard (if_minus_plus)

    Prove the theorem below using [hoare_if].  Do not use [unfold
    valid_hoare_triple].  The [assertion_auto''] tactic we just
    defined may be useful. *)

Theorem if_minus_plus :
  {{True}}
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  {{Y = X + Z}}.
Proof.
  apply hoare_if.
  
  - (* then分支：{{ True /\ X <= Y }} Z := Y - X {{ Y = X + Z }} *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + (* 证明 True /\ X <= Y ->> (Y = X + Z)[Z |-> Y - X] *)
      (* 即 True /\ X <= Y ->> Y = X + (Y - X) *)
      unfold "->>", assertion_sub.
      simpl.
      intros st [_ H].
      rewrite t_update_neq by discriminate.
      rewrite t_update_eq.
      rewrite t_update_neq.
      -- apply Nat.leb_le in H.
        f_equal.
        rewrite Nat.add_comm.
        rewrite Nat.sub_add.
        ++ reflexivity.
        ++ exact H.
      
      -- discriminate. (* "Z" <> "X" *)
      
  - (* else分支：{{ True /\ ~ (X <= Y) }} Y := X + Z {{ Y = X + Z }} *)
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + (* 证明 True /\ ~ (X <= Y) ->> (Y = X + Z)[Y |-> X + Z] *)
      (* 即 True /\ ~ (X <= Y) ->> X + Z = X + Z *)
      unfold "->>", assertion_sub.
      simpl.
      intros st [_ H].
      rewrite t_update_eq.
      reflexivity.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: One-sided conditionals *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [if1 b then c end]. Here [b] is a boolean
    expression, and [c] is a command. If [b] evaluates to [true], then
    command [c] is evaluated. If [b] evaluates to [false], then [if1 b
    then c end] does nothing.

    We recommend that you complete this exercise before attempting the
    ones that follow, as it should help solidify your understanding of
    the material. *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'if1' x 'then' y 'end'" :=
         (CIf1 x y)
             (in custom com at level 0, x custom com at level 99).
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

(** **** Exercise: 2 stars, standard, especially useful (if1_ceval) *)

(** Add two new evaluation rules to relation [ceval], below, for
    [if1]. Let the rules for [if] guide you.*)

Reserved Notation "st '=[' c ']=>'' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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
  | E_If1True : forall st st' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st =[ if1 b then c end ]=> st'
  | E_If1False : forall st b c,
      beval st b = false ->
      st =[ if1 b then c end ]=> st

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The following unit tests should be provable simply by [eauto] if
    you have defined the rules for [if1] correctly. *)

Example if1true_test :
  empty_st =[ if1 X = 0 then X := 1 end ]=> (X !-> 1).
Proof. eauto. Qed.

Example if1false_test :
  (X !-> 2) =[ if1 X = 0 then X := 1 end ]=> (X !-> 2).
Proof. eauto. Qed.

(** [] *)

(** Now we have to repeat the definition and notation of Hoare triples,
    so that they will use the updated [com] type. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
       st =[ c ]=> st' ->
       P st  ->
       Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** **** Exercise: 2 stars, standard (hoare_if1) *)

(** Invent a Hoare logic proof rule for [if1].  State and prove a
    theorem named [hoare_if1] that shows the validity of your rule.
    Use [hoare_if] as a guide. Try to invent a rule that is
    _complete_, meaning it can be used to prove the correctness of as
    many one-sided conditionals as possible.  Also try to keep your
    rule _compositional_, meaning that any Imp command that appears
    in a premise should syntactically be a part of the command
    in the conclusion.

    Hint: if you encounter difficulty getting Coq to parse part of
    your rule as an assertion, try manually indicating that it should
    be in the assertion scope.  For example, if you want [e] to be
    parsed as an assertion, write it as [(e)%assertion]. *)

(* FILL IN HERE *)

(** For full credit, prove formally ([hoare_if1_good]) that your rule is
    precise enough to show the following Hoare triple is valid:

  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}
*)
(* Do not modify the following line: *)
Definition manual_grade_for_hoare_if1 : option (nat*string) := None.
(** [] *)

(** Before the next exercise, we need to restate the Hoare rules of
    consequence (for preconditions) and assignment for the new [com]
    type. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  eauto.
Qed.

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X := a) {{Q}}.
Proof.
  intros Q X a st st' Heval HQ.
  inversion Heval; subst.
  auto.
Qed.

(** **** Exercise: 2 stars, standard (hoare_if1_good) *)

(** Use your [if1] rule to prove the following (valid) Hoare triple.

    Hint: [assertion_auto''] will once again get you most but not all
    the way to a completely automated proof.  You can finish manually,
    or tweak the tactic further.

    Hint: If you see a message like [Unable to unify "Imp.ceval
    Imp.CSkip st st'" with...], it probably means you are using a
    definition or theorem [e.g., hoare_skip] from above this exercise
    without re-proving it for the new version of Imp with if1. *)

Lemma hoare_if1_good :
  {{ X + Y = Z }}
    if1 Y <> 0 then
      X := X + Y
    end
  {{ X = Z }}.
Proof.
  (* 首先我们需要 if1 的 Hoare 规则 *)
  (* if1 的规则应该是：
     {{P /\ b}} c {{Q}}    {{P /\ ~b}} skip {{Q}}
     ----------------------------------------
            {{P}} if1 b then c end {{Q}}
     
     更简化的形式：
     {{P /\ b}} c {{Q}}    P /\ ~b ->> Q
     --------------------------------
           {{P}} if1 b then c end {{Q}}
  *)
  
  eapply hoare_consequence_pre.
  
  (* 我们需要分情况讨论：Y <> 0 和 Y = 0 *)
  - (* 应用类似 if 的规则结构 *)
    intros st st' Heval HP.
    inversion Heval; subst.
    
    + (* E_If1True: Y <> 0 为真，执行 X := X + Y *)
      (* 需要证明执行后 X = Z *)
      inversion H4; subst. (* 分析赋值执行 *)
      simpl.
      rewrite t_update_eq.
      (* 目标：st X + st Y = st Z *)
      (* 从前置条件 HP: st X + st Y = st Z *)
      exact HP.
      
    + (* E_If1False: Y <> 0 为假，即 Y = 0 *)
      (* 状态不变，需要证明 X = Z *)
      (* 从前置条件和 Y = 0 可以推出 X = Z *)
      (* 因为 X + Y = Z 且 Y = 0，所以 X = Z *)
      assert (st' Y = 0).
      { (* 从 beval st (Y <> 0) = false 推出 st Y = 0 *)
        simpl in H3.
        apply negb_false_iff in H3.
        apply eqb_eq in H3.
        exact H3.
      }
      (* 首先简化前置条件中的状态更新 *)
      assert (H_Z: (X !-> st' X + st' Y; st') Z = st' Z).
      { rewrite t_update_neq by discriminate. reflexivity. }
      simpl in HP.

      (* 重写前置条件 *)
      rewrite H_Z in HP.

      (* 现在 HP: st' X + st' Y = st' Z *)
      (* 由于 H: st' Y = 0 *)
      rewrite H in HP.

      (* 现在 HP: st' X + 0 = st' Z *)
      rewrite Nat.add_0_r in HP.

      (* 所以 HP: st' X = st' Z *)
      exact HP.
      
  - (* 证明前置条件蕴含 *)
    unfold "->>".
    intros st H.
    exact H.
Qed.
(** [] *)

End If1.

(* ================================================================= *)
(** ** While Loops *)

(** The Hoare rule for [while] loops is based on the idea of a
    _command invariant_ (or just _invariant_): an assertion whose
    truth is guaranteed after executing a command, assuming it is true
    before.

    That is, an assertion [P] is a command invariant of [c] if

      {{P}} c {{P}}

    holds.  Note that the command invariant might temporarily become
    false in the middle of executing [c], but by the end of [c] it
    must be restored. *)

(**  As a first attempt at a [while] rule, we could try:

             {{P}} c {{P}}
      ---------------------------
      {{P} while b do c end {{P}}

    That rule is valid: if [P] is a command invariant of [c], as the premise
    requires, then no matter how many times the loop body executes,
    [P] is going to be true when the loop finally finishes.

    But the rule also omits two crucial pieces of information.  First,
    the loop terminates when [b] becomes false.  So we can strengthen
    the postcondition in the conclusion:

              {{P}} c {{P}}
      ---------------------------------
      {{P} while b do c end {{P /\ ~b}}

    Second, the loop body will be executed only if [b] is true.  So we
    can also strengthen the precondition in the premise:

            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}
*)

(** That is the Hoare [while] rule.  Note how it combines
    aspects of [skip] and conditionals:

    - If the loop body executes zero times, the rule is like [skip] in
      that the precondition survives to become (part of) the
      postcondition.

    - Like a conditional, we can assume guard [b] holds on entry to
      the subcommand. *)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  (* We proceed by induction on [Heval], because, in the "keep looping" case,
     its hypotheses talk about the whole loop instead of just [c]. The
     [remember] is used to keep the original command in the hypotheses;
     otherwise, it would be lost in the [induction]. By using [inversion]
     we clear away all the cases except those involving [while]. *)
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.

(** We call [P] a _loop invariant_ of [while b do c end] if

      {{P /\ b}} c {{P}}

    is a valid Hoare triple.

    This means that [P] will be true at the end of the loop body
    whenever the loop body executes. If [P] contradicts [b], this
    holds trivially since the precondition is false.

    For instance, [X = 0] is a loop invariant of

      while X = 2 do X := 1 end

    since the program will never enter the loop. *)

(** The program

    while Y > 10 do Y := Y - 1; Z := Z + 1 end

    admits an interesting loop invariant:

    X = Y + Z

    Note that this doesn't contradict the loop guard but neither
    is it a command invariant of

    Y := Y - 1; Z := Z + 1

    since, if X = 5,
    Y = 0 and Z = 5, running the command will set Y + Z to 6. The
    loop guard [Y > 10] guarantees that this will not be the case.
    We will see many such loop invariants in the following chapter.
*)

Example while_example :
  {{X <= 3}}
    while (X <= 2) do
      X := X + 1
    end
  {{X = 3}}.
 Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + assertion_auto''.
  - assertion_auto''.
Qed.

(** If the loop never terminates, any postcondition will work. *)

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.

(** Of course, this result is not surprising if we remember that
    the definition of [valid_hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition.

    Hoare rules that specify what happens _if_ commands terminate,
    without proving that they do, are said to describe a logic of
    _partial_ correctness.  It is also possible to give Hoare rules
    for _total_ correctness, which additionally specifies that
    commands must terminate. Total correctness is out of the scope of
    this textbook. *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: [REPEAT] *)

(** **** Exercise: 4 stars, advanced, optional (hoare_repeat)

    In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [until] b [end]. You will write the
    evaluation rule for [REPEAT] and add a new Hoare rule to the
    language for programs involving it.  (You may recall that the
    evaluation rule is given in an example in the [Auto] chapter.
    Try to figure it out yourself here rather than peeking.) *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [while], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'repeat' e1 'until' b2 'end'" :=
          (CRepeat e1 b2)
              (in custom com at level 0,
               e1 custom com at level 99, b2 custom com at level 99).
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

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [while] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true. *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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
(* FILL IN HERE *)

where "st '=[' c ']=>' st'" := (ceval st c st').

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Definition valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion)
                        : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** To make sure you've got the evaluation rules for [repeat] right,
    prove that [ex1_repeat] evaluates correctly. *)

Definition ex1_repeat :=
  <{ repeat
       X := 1;
       Y := Y + 1
     until (X = 1) end }>.

Theorem ex1_repeat_works :
  empty_st =[ ex1_repeat ]=> (Y !-> 1 ; X !-> 1).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:

  {{ X > 0 }}
    repeat
      Y := X;
      X := X - 1
    until X = 0 end
  {{ X = 0 /\ Y > 0 }}
*)

End RepeatExercise.

(* Do not modify the following line: *)
Definition manual_grade_for_hoare_repeat : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs.

    The rules of Hoare Logic are:

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X:=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} skip {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} while b do c end {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

(** Our task in this chapter has been to _define_ the rules of Hoare
    logic, and prove that the definitions are sound.  Having done so,
    we can now work _within_ Hoare logic to prove that particular
    programs satisfy particular Hoare triples.  In the next chapter,
    we'll see how Hoare logic is can be used to prove that more
    interesting programs satisfy interesting specifications of their
    behavior.

    Crucially, we will do so without ever again [unfold]ing the
    definition of Hoare triples -- i.e., we will take the rules of
    Hoare logic as a closed world for reasoning about programs. *)

(* ################################################################# *)
(** * Additional Exercises *)

(* ================================================================= *)
(** ** Havoc *)

(** In this exercise, we will derive proof rules for a [HAVOC]
    command, which is similar to the nondeterministic [any] expression
    from the the [Imp] chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

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

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> (x !-> n ; st)
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

where "st '=[' c ']=>' st'" := (ceval c st st').

Hint Constructors ceval : core.

(** The definition of Hoare triples is exactly as before. *)

Definition valid_hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', st =[ c ]=> st' -> P st -> Q st'.

Hint Unfold valid_hoare_triple : core.

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** And the precondition consequence rule is exactly as before. *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

(** **** Exercise: 3 stars, advanced (hoare_havoc) *)

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre], and prove that the resulting rule is correct. *)

Definition havoc_pre (X : string) (Q : Assertion) (st : total_map nat) : Prop :=
  forall n, Q (X !-> n; st).

Theorem hoare_havoc : forall (Q : Assertion) (X : string),
  {{ $(havoc_pre X Q) }} havoc X {{ Q }}.
Proof.
  intros Q X st st' Heval HQ.
  unfold havoc_pre in HQ.
  inversion Heval; subst.
  (* 由于 havoc X 可以将 X 设为任意值 n，
     而前置条件保证对于所有 n，Q (X !-> n; st) 都成立，
     所以后置条件 Q st' 成立 *)
  apply HQ.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (havoc_post)

    Complete the following proof without changing any of the provided
    commands. If you find that it can't be completed, your definition of
    [havoc_pre] is probably too strong. Find a way to relax it so that
    [havoc_post] can be proved.

    Hint: the [assertion_auto] tactics we've built won't help you here.
    You need to proceed manually. *)

Theorem havoc_post : forall (P : Assertion) (X : string),
  {{ P }} havoc X {{ $(fun st => exists (n:nat), ({{P [X |-> n] }}) st) }}.
Proof.
  intros P X. eapply hoare_consequence_pre.
  - apply hoare_havoc.
  - (* 需要证明 P ->> havoc_pre X (fun st => exists n, P [X |-> n] st) *)
    unfold "->>", havoc_pre.
    intros st HP.
    intros m.
    (* 目标：exists n, P [X |-> n] (X !-> m; st) *)
    (* 我们选择 n = st X，即原始状态中 X 的值 *)
    exists (st X).
    (* 现在需要证明：P [X |-> st X] (X !-> m; st) *)
    unfold assertion_sub.
    simpl.
    (* 目标：P (X !-> st X; X !-> m; st) *)
    (* 由于连续更新，这简化为 P (X !-> st X; st) *)
    assert (H_eq: (X !-> st X; X !-> m; st) = (X !-> st X; st)).
    {
      unfold t_update.
      apply functional_extensionality.
      intros y.
      destruct (String.eqb X y) eqn:Heq.
      - reflexivity.
      - reflexivity.
    }
    rewrite H_eq.
    (* 现在需要证明：P (X !-> st X; st) *)
    (* 这等价于 P st，因为用原值更新不改变状态 *)
    assert (H_st_eq: (X !-> st X; st) = st).
    {
      unfold t_update.
      apply functional_extensionality.
      intros y.
      destruct (String.eqb X y) eqn:Heq.
      - apply String.eqb_eq in Heq.
        subst.
        reflexivity.
      - reflexivity.
    }
    rewrite H_st_eq.
    exact HP.
Qed.

(** [] *)

End Himp.

(* ================================================================= *)
(** ** Assert and Assume *)

(** **** Exercise: 4 stars, standard (assert_vs_assume)

    In this exercise, we will extend IMP with two commands, [assert]
    and [assume]. Both commands are ways to indicate that a certain
    assertion should hold any time this part of the program is
    reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [assume] statement fails, the program fails to evaluate at
      all. In other words, the program gets stuck and has no final
      state.

    The new set of commands is: *)

Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
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

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }} c {{ Q }}" :=
  (valid_hoare_triple P c Q)
    (at level 2, P custom assn at level 99, c custom com at level 99, Q custom assn at level 99)
    : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [assume]
    statement but not by the [assert] statement. *)

Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}})
  /\ ~ ({{P}} assert b {{Q}}).
Proof.
  (* 我们选择：
     P := True (任何状态都满足)
     b := false (总是假)
     Q := False (没有状态满足)
  *)
  exists (fun _ => True), <{false}>, (fun _ => False).
  split.
  
  - (* 证明 {{True}} assume false {{False}} *)
    unfold valid_hoare_triple.
    intros st r Heval HP.
    (* assume false 只有在 false = true 时才能执行，这不可能 *)
    (* 所以 assume false 永远不会产生正常结果 *)
    inversion Heval; subst.
    (* E_Assume 要求 beval st false = true，但这是矛盾的 *)
    simpl in H0.
    discriminate H0.
    
  - (* 证明 ~ {{True}} assert false {{False}} *)
    unfold not, valid_hoare_triple.
    intro H.
    (* assert false 会产生 RError *)
    assert (Hexec: empty_st =[ assert false ]=> RError).
    { apply E_AssertFalse. reflexivity. }
    
    (* 应用 H *)
    specialize (H empty_st RError Hexec I).
    (* H 声称存在 st' 使得 RError = RNormal st'，这是矛盾的 *)
    destruct H as [st' [Heq _]].
    discriminate Heq.
Qed.

(** Then prove that any triple for an [assert] also works when
    [assert] is replaced by [assume]. *)

Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
  intros P b Q H.
  unfold valid_hoare_triple in *.
  intros st r Heval HP.
  
  (* assume b 的执行 *)
  inversion Heval; subst.
  (* E_Assume: beval st b = true *)
  
  (* 如果 assume b 成功执行，那么 b 在 st 中为真 *)
  (* 现在我们可以模拟 assert b 的执行 *)
  assert (Hassert: st =[ assert b ]=> RNormal st).
  { apply E_AssertTrue. exact H1. }
  
  (* 应用原来的三元组 *)
  specialize (H st (RNormal st) Hassert HP).
  destruct H as [st' [Heq HQ]].
  
  (* RNormal st = RNormal st' 意味着 st = st' *)
  injection Heq as Heq_st.
  subst st'.
  
  (* 结论 *)
  exists st.
  split.
  - reflexivity.
  - exact HQ.
Qed.

(** Next, here are proofs for the old hoare rules adapted to the new
    semantics.  You don't need to do anything with these. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold valid_hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  - assumption.
  - apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold valid_hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ'] ].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ] ].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _] ].
     inversion C.
Qed.

(** Here are the other proof rules (sanity check) *)
Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split.
  - reflexivity.
  - assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
    + assumption.
    + split; assumption.
  - (* b is false *)
    apply (HFalse st st').
    + assumption.
    + split.
      * assumption.
      * apply bexp_eval_false. assumption.
Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{ P /\ ~b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember <{while b do c end}> as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split.
    + reflexivity.
    + split; try assumption.
      apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2.
    + reflexivity.
    + clear IHHe2 He2 r.
      unfold valid_hoare_triple in Hhoare.
      apply Hhoare in He1.
      * destruct He1 as [st1 [Heq Hst1] ].
        inversion Heq; subst.
        assumption.
      * split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold valid_hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _] ]. inversion C.
     + split; assumption.
Qed.

(** Finally, state Hoare rules for [assert] and [assume] and use them
    to prove a simple program correct.  Name your rules [hoare_assert]
    and [hoare_assume]. *)


Theorem hoare_assert : forall P (b:bexp),
  {{P /\ b}} assert b {{P /\ b}}.
Proof.
  intros P b st st' Heval H.
  destruct H as [HP Hb].
  inversion Heval; subst.
  - (* E_AssertTrue *)
    exists st.
    split.
    + reflexivity.
    + split; assumption.
  - (* E_AssertFalse *)
    (* 矛盾：我们有 Hb 说 b 成立，但  beval st b = false *)
    assert (Contra: beval st b = true).
    { exact Hb. }
    rewrite H0 in Contra.
    discriminate Contra.
Qed.

Theorem hoare_assume : forall P (b:bexp),
  {{P}} assume b {{P /\ b}}.
Proof.
  intros P b st st' Heval HP.
  inversion Heval; subst.
  (* E_Assume: beval st b = true *)
  exists st.
  split.
  - reflexivity.
  - split.
    + assumption.
    + exact H0.
Qed.

(** Use your rules to prove the following triple. *)

Example assert_assume_example:
  {{True}}
    assume (X = 1);
    X := X + 1;
    assert (X = 2)
  {{True}}.
Proof.
  (* 使用序列规则分解 *)
  eapply hoare_seq.

  
  - (* 最后部分：assert (X = 2) *)
    eapply hoare_consequence_pre.
    + admit.

Admitted.

End HoareAssertAssume.
(** [] *)



(* 2025-08-24 13:47 *)
