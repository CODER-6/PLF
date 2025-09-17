# MoreStlc.v 定理总结

## 概述

`MoreStlc.v` 文件扩展了简单类型 λ 演算（STLC），添加了多种实用的编程语言特性。这个文件主要关注**语言扩展的形式化**和**类型安全性的保持**，展示了如何在保持核心理论性质的同时丰富语言的表达能力。

## 语言扩展特性

### 1. 数字类型（Numbers）
- **自然数常量**：`0, 1, 2, ...`
- **算术操作**：`succ`（后继）、`pred`（前驱）、`*`（乘法）
- **条件判断**：`if0 t then t1 else t2`（零测试）

### 2. Let 绑定（Let Bindings）
- **语法**：`let x = t1 in t2`
- **语义**：调用值（call-by-value）求值策略
- **作用**：避免重复计算，提高可读性

### 3. 积类型（Product Types/Pairs）
- **构造**：`(t1, t2)` - 创建对
- **投影**：`t.fst`（第一投影）、`t.snd`（第二投影）
- **类型**：`T1 * T2`

### 4. 单元类型（Unit Type）
- **值**：`unit` - 唯一的单元值
- **类型**：`Unit`
- **用途**：表示副作用操作的返回值

### 5. 和类型（Sum Types）
- **构造**：`inl T t`（左注入）、`inr T t`（右注入）
- **模式匹配**：`case t of | inl x => t1 | inr x => t2`
- **类型**：`T1 + T2`
- **用途**：表示"或"关系的数据

### 6. 列表类型（List Types）
- **构造**：`nil T`（空列表）、`cons t1 t2`（列表构造）
- **模式匹配**：`case t of | nil => t1 | x::xs => t2`
- **类型**：`List T`

### 7. 一般递归（General Recursion）
- **不动点算子**：`fix t`
- **用途**：定义递归函数
- **语义**：`fix (\f:T->T, t) --> [f := fix (\f:T->T, t)] t`

## 主要定理

### 1. 进展性定理（Progress Theorem）

```coq
Theorem progress : forall t T,
     <{ empty |-- t \in T }> ->
     value t \/ exists t', t --> t'.
```

**含义**：**扩展的进展性定理** - 对于所有扩展特性，任何在空上下文中良类型的项要么是值，要么可以进行归约步骤。

**重要性**：
- 证明了语言扩展不会引入"卡住"状态
- 确保所有新增特性都遵循进展性原则
- 是类型安全性的核心组成部分

### 2. 弱化引理（Weakening Lemmas）

#### `weakening`
```coq
Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }> ->
     <{ Gamma' |-- t \in T }>.
```

**含义**：如果上下文 `Gamma'` 包含 `Gamma` 的所有绑定，那么在 `Gamma` 中良类型的项在 `Gamma'` 中也良类型。

#### `weakening_empty`
```coq
Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
```

**含义**：在空上下文中良类型的项在任何上下文中都良类型。

### 3. 替换保型引理（Substitution Preserves Typing）

```coq
Lemma substitution_preserves_typing : forall Gamma x U t v T,
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ empty |-- v \in U }>  ->
  <{ Gamma |-- [x:=v]t \in T }>.
```

**含义**：**扩展的替换保型引理** - 对于所有新增的语言特性，用良类型的项替换变量后，原项仍然保持良类型。

**重要性**：
- 处理所有新增语法结构的替换操作
- 特别处理绑定结构（let、case、列表模式匹配等）
- 确保变量绑定的正确性

### 4. 保型性定理（Preservation Theorem）

```coq
Theorem preservation : forall t t' T,
     <{ empty |-- t \in T }> ->
     t --> t'  ->
     <{ empty |-- t' \in T }>.
```

**含义**：**扩展的保型性定理** - 对于所有语言扩展，如果一个良类型的项进行一步归约，那么归约后的项仍然具有相同的类型。

**重要性**：
- 证明了所有新增归约规则的类型安全性
- 涵盖数字运算、对操作、列表操作、递归展开等
- 与进展性定理共同保证类型安全性

## 测试示例分析

### 数字运算示例
```coq
Definition tm_test :=
  <{if0
    (pred
      (succ
        (pred
          (2 * 0))))
    then 5
    else 6}>.
```
- **类型检查**：`<{ empty |-- tm_test \in Nat }>`
- **归约结果**：`tm_test -->* 5`

### 积类型示例
```coq
Definition tm_test := <{((5,6),7).fst.snd}>.
```
- **类型检查**：`<{ empty |-- tm_test \in Nat }>`
- **归约结果**：`tm_test -->* 6`

### Let 绑定示例
```coq
Definition tm_test := <{let x = (pred 6) in (succ x)}>.
```
- **类型检查**：`<{ empty |-- tm_test \in Nat }>`
- **归约结果**：`tm_test -->* 6`

### 和类型示例
```coq
Definition tm_test :=
  <{ case (inl Nat 5) of
     | inl x => x
     | inr y => y }>.
```
- **类型检查**：`<{ empty |-- tm_test \in Nat }>`
- **归约结果**：`tm_test -->* 5`

### 列表操作示例
```coq
Definition tm_test :=
  <{ let l = (5 :: 6 :: (nil Nat)) in
     case l of
     | nil => 0
     | x :: y => (x * x) }>.
```
- **类型检查**：`<{ empty |-- tm_test \in Nat }>`
- **归约结果**：`tm_test -->* 25`

### 递归函数示例

#### 阶乘函数
```coq
Definition fact :=
  <{ fix
      (\f:Nat->Nat,
        \a:Nat,
         if0 a then 1 else (a * (f (pred a)))) }>.
```
- **类型检查**：`<{ empty |-- fact \in Nat -> Nat }>`
- **归约结果**：`<{ fact 4 }> -->* 24`

#### 映射函数
```coq
Definition map :=
  <{ \g:Nat->Nat,
       fix
         (\f:(List Nat)->(List Nat),
            \l:List Nat,
               case l of
               | nil => nil Nat
               | x::l => ((g x)::(f l))) }>.
```
- **类型检查**：`<{ empty |-- map \in (Nat -> Nat) -> (List Nat) -> (List Nat) }>`

#### 相等判断函数
```coq
Definition equal :=
  <{ fix
        (\eq:Nat->Nat->Nat,
           \m:Nat, \n:Nat,
             if0 m then (if0 n then 1 else 0)
             else (if0 n
                   then 0
                   else (eq (pred m) (pred n)))) }>.
```
- **类型检查**：`<{ empty |-- equal \in Nat -> Nat -> Nat }>`
- **归约结果**：`<{ equal 4 4 }> -->* 1`，`<{ equal 4 5 }> -->* 0`

## 理论意义

### 1. 模块化扩展
- 展示了如何系统性地扩展类型系统
- 每个新特性都有完整的语法、语义和类型规则
- 证明了扩展不会破坏原有的类型安全性

### 2. 类型安全性的保持
- **进展性**：所有新特性都不会导致程序卡住
- **保型性**：所有新的归约规则都保持类型不变
- **替换保型**：所有新的绑定结构都正确处理变量替换

### 3. 实用编程特性
- **数据结构**：积类型、和类型、列表提供了基本的数据组织方式
- **控制结构**：let绑定、模式匹配提供了程序结构化的方式
- **计算能力**：递归使语言具备了图灵完备性

### 4. 形式化方法论
- 演示了如何系统性地形式化编程语言特性
- 提供了扩展类型系统的标准模板
- 展现了定理证明在编程语言理论中的应用

## 实际应用价值

1. **编程语言设计**：为设计新的函数式编程语言提供理论基础
2. **编译器验证**：为编译器正确性提供形式化规范
3. **类型系统研究**：为更复杂的类型系统（如子类型、多态等）奠定基础
4. **程序验证**：为静态分析和程序验证工具提供理论支撑

这些定理构成了现代函数式编程语言的理论基础，证明了丰富的语言特性可以在保持类型安全的前提下有机结合。
