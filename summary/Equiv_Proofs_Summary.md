# Equiv.v 文件中的证明统计

本文档统计了 `Equiv.v` 文件中所有使用 `Proof.` 关键字的定理、引理和例子，总计 **54** 个证明。

## 证明分类统计

- **定理 (Theorem)**: 32 个
- **引理 (Lemma)**: 14 个  
- **例子 (Example)**: 8 个

## 详细证明列表

### 1. 基本等价性例子

#### 1.1 aequiv_example
**类型**: Theorem  
**内容**: 证明 `X - X` 与 `0` 在算术表达式上等价
```coq
aequiv <{ X - X }> <{ 0 }>
```

#### 1.2 bequiv_example  
**类型**: Theorem  
**内容**: 证明 `X - X = 0` 与 `true` 在布尔表达式上等价
```coq
bequiv <{ X - X = 0 }> <{ true }>
```

### 2. 简单命令等价性

#### 2.1 skip_left
**类型**: Theorem  
**内容**: 证明在命令前添加 skip 不改变程序行为
```coq
cequiv <{ skip; c }> c
```

#### 2.2 skip_right
**类型**: Theorem  
**内容**: 证明在命令后添加 skip 不改变程序行为
```coq
cequiv <{ c ; skip }> c
```

### 3. 条件语句等价性

#### 3.1 if_true_simple
**类型**: Theorem  
**内容**: 证明条件为 true 的 if 语句等价于其 then 分支
```coq
cequiv <{ if true then c1 else c2 end }> c1
```

#### 3.2 if_true
**类型**: Theorem  
**内容**: 证明如果条件等价于 true，则 if 语句等价于其 then 分支
```coq
bequiv b <{true}> -> cequiv <{ if b then c1 else c2 end }> c1
```

#### 3.3 if_false
**类型**: Theorem  
**内容**: 证明如果条件等价于 false，则 if 语句等价于其 else 分支
```coq
bequiv b <{false}> -> cequiv <{ if b then c1 else c2 end }> c2
```

#### 3.4 swap_if_branches
**类型**: Theorem  
**内容**: 证明可以通过否定条件来交换 if 语句的分支
```coq
cequiv <{ if b then c1 else c2 end }> <{ if ~ b then c2 else c1 end }>
```

### 4. 循环等价性

#### 4.1 while_false
**类型**: Theorem  
**内容**: 证明条件等价于 false 的 while 循环等价于 skip
```coq
bequiv b <{false}> -> cequiv <{ while b do c end }> <{ skip }>
```

#### 4.2 while_true_nonterm
**类型**: Lemma  
**内容**: 证明条件等价于 true 的 while 循环不会终止
```coq
bequiv b <{true}> -> ~( st =[ while b do c end ]=> st' )
```

#### 4.3 while_true
**类型**: Theorem  
**内容**: 证明条件等价于 true 的 while 循环等价于无限循环
```coq
bequiv b <{true}> -> cequiv <{ while b do c end }> <{ while true do skip end }>
```

#### 4.4 loop_unrolling
**类型**: Theorem  
**内容**: 证明循环展开的正确性
```coq
cequiv <{ while b do c end }> <{ if b then c ; while b do c end else skip end }>
```

### 5. 序列组合性质

#### 5.1 seq_assoc
**类型**: Theorem  
**内容**: 证明序列组合的结合律
```coq
cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>
```

### 6. 赋值语句性质

#### 6.1 identity_assignment
**类型**: Theorem  
**内容**: 证明自赋值等价于 skip
```coq
cequiv <{ x := x }> <{ skip }>
```

#### 6.2 assign_aequiv
**类型**: Theorem  
**内容**: 证明如果变量与表达式等价，则 skip 与赋值等价
```coq
aequiv <{ X }> a -> cequiv <{ skip }> <{ X := a }>
```

### 7. 等价关系性质

#### 7.1-7.3 算术表达式等价性质
- **refl_aequiv**: 自反性 `aequiv a a`
- **sym_aequiv**: 对称性 `aequiv a1 a2 -> aequiv a2 a1`  
- **trans_aequiv**: 传递性 `aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3`

#### 7.4-7.6 布尔表达式等价性质
- **refl_bequiv**: 自反性 `bequiv b b`
- **sym_bequiv**: 对称性 `bequiv b1 b2 -> bequiv b2 b1`
- **trans_bequiv**: 传递性 `bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3`

#### 7.7-7.9 命令等价性质
- **refl_cequiv**: 自反性 `cequiv c c`
- **sym_cequiv**: 对称性 `cequiv c1 c2 -> cequiv c2 c1`
- **trans_cequiv**: 传递性 `cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3`

### 8. 同余性质

#### 8.1 CAsgn_congruence
**类型**: Theorem  
**内容**: 证明赋值的同余性
```coq
aequiv a a' -> cequiv <{x := a}> <{x := a'}>
```

#### 8.2 CWhile_congruence
**类型**: Theorem  
**内容**: 证明 while 循环的同余性
```coq
bequiv b b' -> cequiv c c' -> cequiv <{ while b do c end }> <{ while b' do c' end }>
```

#### 8.3 CSeq_congruence
**类型**: Theorem  
**内容**: 证明序列组合的同余性
```coq
cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>
```

#### 8.4 CIf_congruence
**类型**: Theorem  
**内容**: 证明条件语句的同余性
```coq
bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' -> 
cequiv <{ if b then c1 else c2 end }> <{ if b' then c1' else c2' end }>
```

### 9. 常量折叠优化

#### 9.1-9.3 常量折叠例子
- **fold_aexp_ex1**: `fold_constants_aexp <{ (1 + 2) * X }> = <{ 3 * X }>`
- **fold_aexp_ex2**: `fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>`
- **fold_bexp_ex1**: `fold_constants_bexp <{ true && ~(false && true) }> = <{ true }>`
- **fold_bexp_ex2**: `fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }> = <{ (X = Y) && true }>`
- **fold_com_ex1**: 命令常量折叠的复杂例子

#### 9.4-9.6 常量折叠正确性
- **fold_constants_aexp_sound**: 算术表达式常量折叠的正确性
- **fold_constants_bexp_sound**: 布尔表达式常量折叠的正确性  
- **fold_constants_com_sound**: 命令常量折叠的正确性

### 10. 0+n 消除优化

#### 10.1 test_optimize_0plus
**类型**: Example  
**内容**: 展示 0+n 优化的例子

#### 10.2-10.4 0+n 优化正确性
- **optimize_0plus_aexp_sound**: 算术表达式 0+n 优化的正确性
- **optimize_0plus_bexp_sound**: 布尔表达式 0+n 优化的正确性
- **optimize_0plus_com_sound**: 命令 0+n 优化的正确性

#### 10.5 optimizer_sound
**类型**: Theorem  
**内容**: 证明复合优化器的正确性

### 11. 程序不等价性

#### 11.1 subst_aexp_ex
**类型**: Example  
**内容**: 表达式替换的例子

#### 11.2 subst_inequiv
**类型**: Theorem  
**内容**: 证明某个替换性质不成立

#### 11.3 aeval_weakening
**类型**: Lemma  
**内容**: 证明变量不使用时的求值弱化性质

#### 11.4 inequiv_exercise
**类型**: Theorem  
**内容**: 证明无限循环与 skip 不等价

### 12. 非确定性扩展

#### 12.1-12.2 HAVOC 例子
- **havoc_example1**: `empty_st =[ havoc X ]=> (X !-> 0)`
- **havoc_example2**: `empty_st =[ skip; havoc Z ]=> (Z !-> 42)`

#### 12.3 pXY_cequiv_pYX (重复定义)
**类型**: Theorem  
**内容**: 证明两个 HAVOC 序列的等价性或不等价性

#### 12.4 ptwice_cequiv_pcopy
**类型**: Theorem  
**内容**: 证明两种不同的随机赋值模式不等价

#### 12.5-12.6 循环发散性质
- **p1_may_diverge**: 证明程序 p1 在特定条件下发散
- **p2_may_diverge**: 证明程序 p2 在特定条件下发散

#### 12.7 p1_p2_equiv
**类型**: Theorem  
**内容**: 证明两个具有相同终止行为的程序等价

#### 12.8 p3_p4_inequiv
**类型**: Theorem  
**内容**: 证明两个程序不等价

#### 12.9 p5_p6_equiv
**类型**: Theorem  
**内容**: 证明另一对程序等价

### 13. 附加练习

#### 13.1 swap_noninterfering_assignments
**类型**: Theorem  
**内容**: 证明不相互干扰的赋值可以交换顺序

#### 13.2-13.4 程序近似
- **c3_c4_different**: 证明两个程序互不近似
- **cmin_minimal**: 证明最小程序近似所有程序
- **zprop_preserving**: 证明某个性质在程序近似下保持

## 总结

该文件系统地证明了程序等价性的各种性质，包括：

1. **基本等价关系**: 自反性、对称性、传递性
2. **同余性质**: 各种语言构造的同余性
3. **优化正确性**: 常量折叠、0+n消除等优化的正确性
4. **程序变换**: 循环展开、条件简化等变换的正确性
5. **不等价性**: 通过反例证明某些程序不等价
6. **非确定性**: 扩展语言的等价性性质

这些证明为程序优化和程序验证提供了理论基础，确保了编译器优化的正确性。
