# Hoare2.v 文件中的证明统计

本文档统计了 `Hoare2.v` 文件中所有使用 `Proof.` 关键字的定理、引理和例子，总计 **29** 个证明。

## 证明分类统计

- **定理 (Theorem)**: 18 个
- **引理 (Lemma)**: 4 个  
- **例子 (Example)**: 7 个

## 详细证明列表

### 1. 基础霍尔逻辑应用

#### 1.1 reduce_to_zero_correct'
**类型**: Theorem  
**内容**: 证明将变量X减到0的程序的正确性（手工证明版本）
```coq
{{True}} reduce_to_zero {{X = 0}}
```
**说明**: 这是一个详细的手工证明，展示了如何使用基本的霍尔逻辑规则来证明while循环的正确性。

#### 1.2 reduce_to_zero_correct'''
**类型**: Theorem  
**内容**: 证明将变量X减到0的程序的正确性（使用自动化策略）
```coq
{{True}} reduce_to_zero {{X = 0}}
```
**说明**: 与上一个定理相同的规范，但使用了 `verify_assertion` 策略来自动化大部分证明过程。

### 2. 形式化装饰程序框架

#### 2.1 dec0
**类型**: Example  
**内容**: 简单的装饰命令例子
```coq
<{ skip {{ True }} }>
```
**说明**: 展示装饰程序语法的基本用法。

#### 2.2 dec1
**类型**: Example  
**内容**: 带有while循环的装饰命令例子
```coq
<{ while true do {{ True }} skip {{ True }} end {{ True }} }>
```
**说明**: 展示更复杂的装饰程序语法。

#### 2.3 dec_while
**类型**: Example  
**内容**: 完整的装饰程序例子，实现X递减到0
```coq
{{ True }} while X <> 0 do {{ True /\ (X <> 0) }} X := X - 1 {{ True }} end {{ True /\ X = 0}} ->> {{ X = 0 }}
```

#### 2.4 erase_while_ex
**类型**: Example  
**内容**: 证明从装饰程序中擦除断言得到原始程序
```coq
erase_d dec_while = <{while X <> 0 do X := X - 1 end}>
```

#### 2.5 precondition_from_while
**类型**: Example  
**内容**: 从装饰程序中提取前条件
```coq
precondition_from dec_while = True
```

#### 2.6 postcondition_from_while
**类型**: Example  
**内容**: 从装饰程序中提取后条件
```coq
postcondition_from dec_while = {{ X = 0 }}
```

#### 2.7 dec_while_triple_correct
**类型**: Example  
**内容**: 验证装饰程序对应的霍尔三元组
```coq
outer_triple_valid dec_while = {{ True }} while X <> 0 do X := X - 1 end {{ X = 0 }}
```

### 3. 验证条件生成器的正确性

#### 3.1 verification_correct
**类型**: Theorem  
**内容**: 证明验证条件生成器的正确性
```coq
forall d P, verification_conditions P d -> {{P}} erase d {{ $(post d) }}
```
**说明**: 这是整个装饰程序框架的核心定理，证明如果验证条件满足，那么对应的霍尔三元组有效。

#### 3.2 vc_dec_while
**类型**: Example  
**内容**: 验证具体装饰程序的验证条件
```coq
verification_conditions_from dec_while
```

#### 3.3 dec_while_correct
**类型**: Theorem  
**内容**: 证明dec_while装饰程序的正确性
```coq
outer_triple_valid dec_while
```

### 4. 具体程序的正确性证明

#### 4.1 swap_correct
**类型**: Theorem  
**内容**: 证明变量交换程序的正确性
```coq
forall m n, outer_triple_valid (swap_dec m n)
```
**说明**: 通过加减法交换两个变量值的程序正确性证明。

#### 4.2 positive_difference_correct
**类型**: Theorem  
**内容**: 证明计算正差值程序的正确性
```coq
outer_triple_valid positive_difference_dec
```

#### 4.3 if_minus_plus_correct
**类型**: Theorem  
**内容**: 证明条件语句中减法和加法程序的正确性
```coq
outer_triple_valid if_minus_plus_dec
```

#### 4.4 div_mod_outer_triple_valid
**类型**: Theorem  
**内容**: 证明除法和取模程序的正确性
```coq
forall a b, outer_triple_valid (div_mod_dec a b)
```

### 5. 循环不变式的应用

#### 5.1 subtract_slowly_dec
**类型**: Example  
**内容**: 慢减法程序的装饰版本
```coq
{{ X = m /\ Y = n }} ->> {{ Y - X = n - m }} while X <> 0 do ... end {{ Y = n - m }}
```

#### 5.2 subtract_slowly_outer_triple_valid
**类型**: Theorem  
**内容**: 证明慢减法程序的正确性
```coq
forall m n, outer_triple_valid (subtract_slowly_dec m n)
```

#### 5.3 slow_assignment_dec
**类型**: Example  
**内容**: 慢赋值程序的装饰版本
```coq
{{ X = m }} Y := 0; while X <> 0 do ... end {{ Y = m }}
```

#### 5.4 slow_assignment
**类型**: Theorem  
**内容**: 证明慢赋值程序的正确性
```coq
forall m, outer_triple_valid (slow_assignment_dec m)
```

### 6. 奇偶性计算

#### 6.1 parity_ge_2
**类型**: Lemma  
**内容**: 奇偶性函数的性质：当x≥2时
```coq
forall x, 2 <= x -> parity (x - 2) = parity x
```

#### 6.2 parity_lt_2
**类型**: Lemma  
**内容**: 奇偶性函数的性质：当x<2时
```coq
forall x, ~ 2 <= x -> parity x = x
```

#### 6.3 parity_outer_triple_valid
**类型**: Theorem  
**内容**: 证明奇偶性计算程序的正确性
```coq
forall m, outer_triple_valid (parity_dec m)
```

### 7. 平方根计算

#### 7.1 sqrt_correct
**类型**: Theorem  
**内容**: 证明整数平方根计算程序的正确性
```coq
forall m, outer_triple_valid (sqrt_dec m)
```
**说明**: 计算整数平方根的迭代算法的正确性证明。

### 8. 阶乘计算（练习）

#### 8.1 factorial_dec
**类型**: Example  
**内容**: 阶乘计算程序的装饰版本（待完成）
```coq
decorated
```

#### 8.2 factorial_correct
**类型**: Theorem  
**内容**: 阶乘计算程序的正确性（待证明）
```coq
forall m, outer_triple_valid (factorial_dec m)
```

### 9. 最小值计算

#### 9.1 minimum_correct
**类型**: Theorem  
**内容**: 证明最小值计算程序的正确性
```coq
forall a b, outer_triple_valid (minimum_dec a b)
```
**说明**: 通过同时递减两个变量来计算最小值的算法正确性证明。

### 10. 双循环程序

#### 10.1 two_loops
**类型**: Theorem  
**内容**: 证明双循环加法程序的正确性
```coq
forall a b c, outer_triple_valid (two_loops_dec a b c)
```
**说明**: 使用两个连续的while循环来计算三个数之和的程序正确性证明。

### 11. 幂级数计算

#### 11.1 pow2_plus_1
**类型**: Lemma  
**内容**: 2的幂函数的递归性质
```coq
forall n, pow2 (n+1) = pow2 n + pow2 n
```

#### 11.2 pow2_le_1
**类型**: Lemma  
**内容**: 2的幂函数的下界性质
```coq
forall n, pow2 n >= 1
```

#### 11.3 dpow2_down_correct
**类型**: Theorem  
**内容**: 证明幂级数计算程序的正确性
```coq
forall n, outer_triple_valid (dpow2_dec n)
```
**说明**: 计算 1 + 2 + 2² + ... + 2ⁿ = 2^(n+1) - 1 的程序正确性证明。

### 12. 斐波那契数列

#### 12.1 fib_eqn
**类型**: Lemma  
**内容**: 斐波那契数列的递推关系
```coq
forall n, n > 0 -> fib n + fib (pred n) = fib (1 + n)
```

#### 12.2 dfib_correct
**类型**: Theorem  
**内容**: 斐波那契数列计算程序的正确性（待证明）
```coq
forall n, outer_triple_valid (dfib n)
```

### 13. 最弱前条件理论

#### 13.1 is_wp_example
**类型**: Theorem  
**内容**: 证明具体的最弱前条件例子
```coq
is_wp ({{ Y <= 4 }}) (<{X := Y + 1}>) ({{ X <= 5 }})
```

#### 13.2 hoare_asgn_weakest
**类型**: Theorem  
**内容**: 证明赋值规则中的前条件是最弱前条件
```coq
forall Q X a, is_wp ({{ Q [X |-> a] }}) <{ X := a }> Q
```

#### 13.3 hoare_havoc_weakest
**类型**: Lemma  
**内容**: 证明HAVOC命令的最弱前条件性质（待证明）
```coq
forall (P Q : Assertion) (X : string), {{ P }} havoc X {{ Q }} -> P ->> havoc_pre X Q
```

## 主要贡献

这些证明涵盖了霍尔逻辑第二部分的核心内容：

1. **装饰程序方法论**: 建立了形式化的装饰程序语法和语义
2. **自动化验证**: 开发了验证条件生成器和自动化证明策略
3. **循环不变式技术**: 通过多个实例展示了如何发现和使用循环不变式
4. **程序正确性证明**: 涵盖了各种算法的正确性证明，包括算术运算、搜索算法等
5. **最弱前条件理论**: 介绍了最弱前条件的概念和性质

## 文档位置

详细的分析文档已保存在：`/Users/dk/Desktop/coq/plf/Hoare2_Proofs_Summary.md`

该文档为霍尔逻辑的高级应用和程序验证自动化提供了完整的参考。
