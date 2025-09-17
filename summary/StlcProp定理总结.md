# StlcProp.v 定理总结

## 概述

`StlcProp.v` 文件包含了简单类型 λ 演算（STLC）的基本理论，特别是**类型安全性定理**。这是类型理论中最重要的结果之一，证明了类型系统的健全性。

## 主要定理分类

### 1. 规范形式引理（Canonical Forms Lemmas）

#### `canonical_forms_bool`
```coq
Lemma canonical_forms_bool : forall t,
  <{ empty |-- t \in Bool }> ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
```
**含义**：如果一个项在空上下文中具有布尔类型且是值，那么它要么是 `true` 要么是 `false`。

#### `canonical_forms_fun`
```coq
Lemma canonical_forms_fun : forall t T1 T2,
  <{ empty |-- t \in T1 -> T2 }> ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
```
**含义**：如果一个项在空上下文中具有函数类型且是值，那么它必定是 lambda 抽象。

### 2. 进展性定理（Progress Theorems）

#### `progress`
```coq
Theorem progress : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
```
**含义**：**进展性定理** - 任何闭合的、良类型的项要么是值，要么可以进行归约步骤。这确保了程序不会"卡住"。

#### `progress'`
```coq
Theorem progress' : forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
```
**含义**：进展性定理的另一种证明方法（通过对项的结构归纳）。

### 3. 保型性定理（Preservation Theorems）

#### `preservation`
```coq
Theorem preservation : forall t t' T,
  <{ empty |-- t \in T }> ->
  t --> t' ->
  <{ empty |-- t' \in T }>.
```
**含义**：**保型性定理** - 如果一个良类型的项进行一步归约，那么归约后的项仍然具有相同的类型。

### 4. 类型安全性（Type Safety）

#### `type_soundness`
```coq
Corollary type_soundness : forall t t' T,
  <{ empty |-- t \in T }> ->
  t -->* t' ->
  ~(stuck t').
```
**含义**：**类型安全性定理** - 良类型的项永远不会到达"卡住"状态。这是进展性和保型性的直接推论。

### 5. 替换相关定理

#### `substitution_preserves_typing`
```coq
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }> ->
  <{ Gamma |-- [x:=v]t \in T }>.
```
**含义**：**替换保型引理** - 用良类型的项替换变量后，原项仍然保持良类型。

#### `substitution_preserves_typing_from_typing_ind`
```coq
Lemma substitution_preserves_typing_from_typing_ind : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>   ->
  <{ Gamma |-- [x:=v]t \in T }>.
```
**含义**：替换保型引理的另一种证明（通过对类型推导归纳）。

### 6. 弱化引理（Weakening Lemmas）

#### `weakening`
```coq
Lemma weakening : forall Gamma Gamma' t T,
  included Gamma Gamma' ->
  <{ Gamma |-- t \in T }> ->
  <{ Gamma' |-- t \in T }>.
```
**含义**：**弱化引理** - 向上下文添加更多变量不会影响项的类型。

#### `weakening_empty`
```coq
Lemma weakening_empty : forall Gamma t T,
  <{ empty |-- t \in T }> ->
  <{ Gamma |-- t \in T }>.
```
**含义**：在空上下文中良类型的项在任何上下文中都良类型。

### 7. 类型唯一性

#### `unique_types`
```coq
Theorem unique_types : forall Gamma e T T',
  <{ Gamma |-- e \in T }> ->
  <{ Gamma |-- e \in T' }> ->
  T = T'.
```
**含义**：**类型唯一性定理** - 在给定上下文中，每个项最多有一个类型。

### 8. 反向主题展开

#### `not_subject_expansion`
```coq
Theorem not_subject_expansion:
  exists t t' T, t --> t' /\ <{ empty |-- t' \in T }> /\ ~ <{ empty |-- t \in T }>.
```
**含义**：**主题展开不成立** - 与保型性相反，如果 `t --> t'` 且 `t'` 良类型，`t` 不一定良类型。

### 9. 自由变量相关

#### `free_in_context`
```coq
Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   <{ Gamma |-- t \in T }> ->
   exists T', Gamma x = Some T'.
```
**含义**：如果变量在项中自由出现且项良类型，那么该变量必须在上下文中有类型。

#### `typable_empty__closed`
```coq
Corollary typable_empty__closed : forall t T,
    <{ empty |-- t \in T }> ->
    closed t.
```
**含义**：在空上下文中良类型的项必须是闭合的（没有自由变量）。

### 10. 上下文不变性

#### `context_invariance`
```coq
Lemma context_invariance : forall Gamma Gamma' t T,
     <{ Gamma |-- t \in T }> ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     <{ Gamma' |-- t \in T }>.
```
**含义**：**上下文不变性** - 如果两个上下文在项的自由变量上一致，那么项在两个上下文中具有相同的类型。

## 核心理论意义

### 类型安全性的完整证明

这些定理共同构成了 STLC 的**类型安全性**证明：

1. **进展性（Progress）**：良类型的程序不会卡住
2. **保型性（Preservation）**：程序执行过程中类型保持不变
3. **类型安全性（Type Safety）**：两者的结合，确保良类型程序的安全执行

### 实际意义

- **编程语言设计**：为类型系统的设计提供理论基础
- **编译器正确性**：确保类型检查器的可靠性
- **程序验证**：为静态分析和形式验证奠定基础
- **函数式编程**：证明了 λ 演算作为计算模型的健全性

## 证明技术

文件中使用的主要证明技术包括：
- **结构归纳**：对项和类型的归纳
- **规则归纳**：对类型推导和归约关系的归纳
- **案例分析**：对不同的语法形式分类讨论
- **反演**：从结论推导前提的技术
- **替换引理**：处理变量绑定的核心技术

这些定理构成了现代类型理论的基础，是理解编程语言语义的重要里程碑。
