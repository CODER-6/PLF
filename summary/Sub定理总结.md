# Sub.v 定理总结

## 概述

`Sub.v` 文件引入了**子类型系统（Subtyping）**到简单类型 λ 演算（STLC）中。这是面向对象编程语言的核心特性，允许一个类型的值安全地用在期望其父类型值的上下文中。该文件证明了带子类型的STLC仍然满足类型安全性。

## 子类型系统核心概念

### 安全替换原则（Safe Substitution Principle）
**定义**：如果 `S <: T`（S是T的子类型），那么类型为S的值可以安全地用在任何期望类型T值的上下文中。

### 子类型关系规则

#### 结构规则
- **反射性（S_Refl）**：`T <: T`
- **传递性（S_Trans）**：`S <: U` 且 `U <: T` → `S <: T`
- **Top规则（S_Top）**：`S <: Top`（Top是所有类型的父类型）

#### 类型构造器规则
- **积类型（S_Prod）**：`S1 <: T1` 且 `S2 <: T2` → `S1*S2 <: T1*T2`
- **箭头类型（S_Arrow）**：`T1 <: S1` 且 `S2 <: T2` → `S1->S2 <: T1->T2`
  - 注意：参数类型是**逆变的**，返回类型是**协变的**

#### 包容规则（Subsumption Rule）
```coq
Gamma |-- t1 \in T1     T1 <: T2
--------------------------------  (T_Sub)
      Gamma |-- t1 \in T2
```

## 主要定理分类

### 1. 子类型反演引理（Subtype Inversion Lemmas）

#### `sub_inversion_Bool`
```coq
Lemma sub_inversion_Bool : forall U,
     U <: Bool ->
     U = Bool.
```
**含义**：`Bool` 类型的唯一子类型是它自己。

#### `sub_inversion_arrow`
```coq
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: (V1->V2) ->
     exists U1 U2,
     U = (U1->U2) /\ V1 <: U1 /\ U2 <: V2.
```
**含义**：箭头类型的子类型必须也是箭头类型，且参数和返回类型满足相应的子类型关系。

#### `sub_inversion_Unit`
```coq
Lemma sub_inversion_Unit : forall U,
     U <: Unit ->
     U = Unit.
```
**含义**：`Unit` 类型的唯一子类型是它自己。

#### `sub_inversion_Base`
```coq
Lemma sub_inversion_Base : forall U s,
     U <: (Base s) ->
     U = (Base s).
```
**含义**：基础类型的唯一子类型是它自己。

#### `sub_inversion_Top`
```coq
Lemma sub_inversion_Top : forall U,
     Top <: U ->
     U = Top.
```
**含义**：`Top` 类型的唯一父类型是它自己。

### 2. 规范形式引理（Canonical Forms Lemmas）

#### `canonical_forms_of_arrow_types`
```coq
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  <{ Gamma |-- s \in T1->T2 }> ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
```
**含义**：具有箭头类型的值必须是lambda抽象。

#### `canonical_forms_of_Bool`
```coq
Lemma canonical_forms_of_Bool : forall Gamma s,
  <{ Gamma |-- s \in Bool }> ->
  value s ->
  s = tm_true \/ s = tm_false.
```
**含义**：具有布尔类型的值必须是 `true` 或 `false`。

### 3. 进展性定理（Progress Theorem）

```coq
Theorem progress : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
```

**含义**：**带子类型的进展性定理** - 在空上下文中良类型的项要么是值，要么可以进行归约步骤。

**重要性**：
- 证明了子类型的引入不会导致程序卡住
- 确保类型安全性的一半：程序不会进入无法继续的状态
- 需要使用规范形式引理来处理子类型情况

### 4. 类型反演引理（Typing Inversion Lemmas）

#### `typing_inversion_abs`
```coq
Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     <{ Gamma |-- \x:S1,t2 \in T }> ->
     exists S2,
       <{{ S1->S2 }}> <: T
       /\ <{ x |-> S1 ; Gamma |-- t2 \in S2 }>.
```
**含义**：如果lambda抽象具有类型T，那么存在类型S2使得S1->S2是T的子类型。

#### `typing_inversion_var`
```coq
Lemma typing_inversion_var : forall Gamma (x:string) T,
  <{ Gamma |-- x \in T }> ->
  exists S,
    Gamma x = Some S /\ S <: T.
```
**含义**：如果变量x具有类型T，那么上下文中x的类型是T的某个子类型。

#### `typing_inversion_app`
```coq
Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  <{ Gamma |-- t1 t2 \in T2 }> ->
  exists T1,
    <{ Gamma |-- t1 \in T1->T2 }> /\
    <{ Gamma |-- t2 \in T1 }>.
```
**含义**：如果函数应用具有类型T2，那么函数具有某个箭头类型，参数具有相应的参数类型。

#### `typing_inversion_unit`
```coq
Lemma typing_inversion_unit : forall Gamma T,
  <{ Gamma |-- unit \in T }> ->
  Unit <: T.
```
**含义**：如果unit具有类型T，那么Unit是T的子类型。

#### `abs_arrow`
```coq
Lemma abs_arrow : forall x S1 s2 T1 T2,
  <{ empty |-- \x:S1,s2 \in T1->T2 }> ->
  T1 <: S1
  /\ <{ x |-> S1 |-- s2 \in T2 }>.
```
**含义**：组合引理，说明lambda抽象与箭头类型的关系。

### 5. 弱化引理（Weakening Lemmas）

#### `weakening`
```coq
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
```
**含义**：扩展上下文不影响类型判断。

#### `weakening_empty`
```coq
Corollary weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
```
**含义**：在空上下文中良类型的项在任何上下文中都良类型。

### 6. 替换保型引理（Substitution Preserves Typing）

```coq
Lemma substitution_preserves_typing : forall Gamma x U t v T,
   <{ x |-> U ; Gamma |-- t \in T }> ->
   <{ empty |-- v \in U }>  ->
   <{ Gamma |-- [x:=v]t \in T }>.
```

**含义**：**带子类型的替换保型引理** - 用良类型的项替换变量后，原项仍然保持良类型。

### 7. 保型性定理（Preservation Theorem）

```coq
Theorem preservation : forall t t' T,
     <{ empty |-- t \in T }> ->
     t --> t'  ->
     <{ empty |-- t' \in T }>.
```

**含义**：**带子类型的保型性定理** - 如果一个良类型的项进行一步归约，那么归约后的项仍然具有相同的类型。

**重要性**：
- 证明了子类型系统中类型在计算过程中保持不变
- 与进展性定理共同构成类型安全性
- 需要使用类型反演引理和替换保型引理

### 8. 形式化练习定理

文件包含了大量形式化的"思考练习"定理，分为几类：

#### 子类型实例判断（Subtype Instance Judgments）
- `formal_subtype_instances_tf_1a` 到 `formal_subtype_instances_tf_1g`：检验具体子类型关系的真假
- `formal_subtype_instances_tf_2a` 到 `formal_subtype_instances_tf_2e`：更复杂的子类型模式

#### 子类型概念（Subtype Concepts）
- `formal_subtype_concepts_tfa` 到 `formal_subtype_concepts_tfh`：关于子类型系统基本性质的判断
- 涉及最大/最小类型、无穷链等概念

#### 真子类型（Proper Subtypes）
- `formal_proper_subtypes`：关于非平凡子类型存在性的判断

## 子类型系统的实际应用

### 1. 记录类型子类型
虽然文件中没有直接实现记录类型，但讨论了三种子类型规则：
- **宽度子类型（Width Subtyping）**：添加字段得到子类型
- **深度子类型（Depth Subtyping）**：字段类型的子类型关系
- **排列子类型（Permutation Subtyping）**：字段顺序无关

### 2. 面向对象编程
子类型是面向对象语言的核心：
- **类和接口**：子类提供父类的所有方法和字段
- **多态性**：子类对象可以用在期望父类对象的地方
- **代码重用**：通过继承和子类型实现

### 3. 类型安全的灵活性
子类型提供了类型安全与编程灵活性的平衡：
- 保持静态类型检查的安全性
- 允许更灵活的代码组织和重用
- 支持渐进式的接口设计

## 理论意义

### 1. 类型系统扩展的典型模式
展示了如何系统性地为类型系统添加新特性：
- 定义新的判断关系（子类型关系）
- 添加新的类型规则（包容规则）
- 证明基本性质的保持（进展性、保型性）

### 2. 协变性和逆变性
箭头类型的子类型规则展示了重要概念：
- **逆变性**：函数参数类型的子类型关系是"反向"的
- **协变性**：函数返回类型的子类型关系是"正向"的
- 这些概念在现代类型系统设计中至关重要

### 3. 类型安全性的维护
证明了复杂的类型系统特性可以在保持类型安全的前提下添加：
- 进展性：程序不会卡住
- 保型性：类型在计算中保持一致
- 两者结合保证类型安全性

## 实际价值

1. **编程语言设计**：为现代面向对象语言提供理论基础
2. **类型检查器实现**：为编译器的类型检查算法提供规范
3. **程序验证**：为静态分析工具提供理论支撑
4. **接口设计**：指导API和库的设计原则

这些定理构成了现代面向对象编程语言类型系统的理论基础，证明了子类型可以在保持类型安全的前提下提供编程的灵活性。
