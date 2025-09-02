# Hoare.v 文件中的证明统计

本文档统计了 `Hoare.v` 文件中所有使用 `Proof.` 关键字的定理、引理和例子，总计 **56** 个证明。

## 证明分类统计

- **定理 (Theorem)**: 31 个
- **引理 (Lemma)**: 2 个  
- **例子 (Example)**: 23 个

## 详细证明列表

### 1. 基础霍尔逻辑规则

#### 1.1 hoare_post_true
**类型**: Theorem  
**内容**: 如果后条件在所有状态都成立，则任何以它为后条件的三元组都有效
```coq
forall (P Q : Assertion) c, (forall st, Q st) -> {{P}} c {{Q}}
```

#### 1.2 hoare_pre_false
**类型**: Theorem  
**内容**: 如果前条件在任何状态都不成立，则任何以它为前条件的三元组都有效
```coq
forall (P Q : Assertion) c, (forall st, ~ (P st)) -> {{P}} c {{Q}}
```

#### 1.3 hoare_skip
**类型**: Theorem  
**内容**: skip 命令的霍尔规则 - skip 保持任何断言
```coq
forall P, {{P}} skip {{P}}
```

#### 1.4 hoare_seq
**类型**: Theorem  
**内容**: 序列组合的霍尔规则
```coq
forall P Q R c1 c2, {{Q}} c2 {{R}} -> {{P}} c1 {{Q}} -> {{P}} c1; c2 {{R}}
```

### 2. 赋值规则相关

#### 2.1 equivalent_assertion1, equivalent_assertion2
**类型**: Example  
**内容**: 展示断言替换的等价性例子

#### 2.2 hoare_asgn
**类型**: Theorem  
**内容**: 赋值的基本霍尔规则
```coq
forall Q X (a:aexp), {{Q [X |-> a]}} X := a {{Q}}
```

#### 2.3 assertion_sub_example
**类型**: Example  
**内容**: 使用赋值规则的简单例子

#### 2.4 hoare_asgn_examples1, hoare_asgn_examples2
**类型**: Example  
**内容**: 赋值规则的练习例子

#### 2.5 hoare_asgn_wrong
**类型**: Theorem  
**内容**: 证明一个看似自然但错误的赋值规则确实是错误的
```coq
exists a:aexp, ~ {{ True }} X := a {{ X = a }}
```

#### 2.6 hoare_asgn_fwd
**类型**: Theorem  
**内容**: 正向赋值规则（使用参数记住原值）
```coq
forall (m:nat) (a:aexp) (P : Assertion), {{P /\ X = m}} X := a {{...}}
```

#### 2.7 hoare_asgn_fwd_exists
**类型**: Theorem  
**内容**: 另一种正向赋值规则（使用存在量化）
```coq
forall a (P : Assertion), {{ P }} X := a {{ ... }}
```

### 3. 推理规则 (Consequence Rules)

#### 3.1 hoare_consequence_pre
**类型**: Theorem  
**内容**: 前条件加强规则
```coq
forall (P P' Q : Assertion) c, {{P'}} c {{Q}} -> P ->> P' -> {{P}} c {{Q}}
```

#### 3.2 hoare_consequence_post
**类型**: Theorem  
**内容**: 后条件削弱规则
```coq
forall (P Q Q' : Assertion) c, {{P}} c {{Q'}} -> Q' ->> Q -> {{P}} c {{Q}}
```

#### 3.3 hoare_consequence
**类型**: Theorem  
**内容**: 组合推理规则
```coq
forall (P P' Q Q' : Assertion) c, {{P'}} c {{Q'}} -> P ->> P' -> Q' ->> Q -> {{P}} c {{Q}}
```

#### 3.4 hoare_consequence_pre', hoare_consequence_pre'', hoare_consequence_pre''', hoare_consequence_pre''''
**类型**: Theorem  
**内容**: 前条件推理规则的不同自动化版本

#### 3.5 hoare_consequence_post'
**类型**: Theorem  
**内容**: 后条件推理规则的自动化版本

### 4. 赋值和序列组合的例子

#### 4.1 hoare_asgn_example1, hoare_asgn_example1', hoare_asgn_example1'', hoare_asgn_example1'''
**类型**: Example  
**内容**: 赋值规则应用的各种自动化程度的例子

#### 4.2 assertion_sub_example2, assertion_sub_example2', assertion_sub_example2''
**类型**: Example  
**内容**: 断言替换例子的不同版本

#### 4.3 assertion_sub_ex1', assertion_sub_ex2'
**类型**: Example  
**内容**: 断言替换的练习例子

#### 4.4 hoare_asgn_example3
**类型**: Example  
**内容**: 序列组合和赋值的综合例子

#### 4.5 hoare_asgn_example4
**类型**: Example  
**内容**: 复杂的序列组合例子，涉及多个推理步骤

#### 4.6 swap_exercise
**类型**: Theorem  
**内容**: 交换两个变量值的程序正确性证明
```coq
{{X <= Y}} swap_program {{Y <= X}}
```

#### 4.7 invalid_triple
**类型**: Theorem  
**内容**: 证明某个霍尔三元组不是对所有表达式都有效

### 5. 条件语句规则

#### 5.1 bexp_eval_false
**类型**: Lemma  
**内容**: 布尔表达式求值为假时的辅助引理

#### 5.2 hoare_if
**类型**: Theorem  
**内容**: 条件语句的霍尔规则
```coq
forall P Q (b:bexp) c1 c2, {{ P /\ b }} c1 {{Q}} -> {{ P /\ ~ b}} c2 {{Q}} -> {{P}} if b then c1 else c2 end {{Q}}
```

#### 5.3 if_example, if_example'', if_example'''
**类型**: Example  
**内容**: 条件语句规则的应用例子，展示不同的自动化程度

#### 5.4 if_minus_plus
**类型**: Theorem  
**内容**: 条件语句的练习例子

### 6. 单边条件语句扩展 (If1 Module)

#### 6.1 if1true_test, if1false_test
**类型**: Example  
**内容**: 单边条件语句的执行测试

#### 6.2 hoare_consequence_pre, hoare_asgn (在 If1 模块中)
**类型**: Theorem  
**内容**: 为新的命令类型重新证明的基本规则

#### 6.3 hoare_if1_good
**类型**: Lemma  
**内容**: 单边条件语句规则的应用例子

### 7. 循环规则

#### 7.1 hoare_while
**类型**: Theorem  
**内容**: while 循环的霍尔规则
```coq
forall P (b:bexp) c, {{P /\ b}} c {{P}} -> {{P}} while b do c end {{P /\ ~ b}}
```

#### 7.2 while_example
**类型**: Example  
**内容**: while 循环规则的应用例子

#### 7.3 always_loop_hoare
**类型**: Theorem  
**内容**: 证明无限循环可以满足任何后条件
```coq
forall Q, {{True}} while true do skip end {{Q}}
```

### 8. REPEAT 扩展 (RepeatExercise Module)

#### 8.1 ex1_repeat_works
**类型**: Theorem  
**内容**: REPEAT 命令的执行示例

### 9. HAVOC 扩展 (Himp Module)

#### 9.1 hoare_consequence_pre (在 Himp 模块中)
**类型**: Theorem  
**内容**: 为 HAVOC 扩展重新证明的推理规则

#### 9.2 hoare_havoc
**类型**: Theorem  
**内容**: HAVOC 命令的霍尔规则
```coq
forall (Q : Assertion) (X : string), {{ $(havoc_pre X Q) }} havoc X {{ Q }}
```

#### 9.3 havoc_post
**类型**: Theorem  
**内容**: HAVOC 命令的后条件性质

### 10. Assert/Assume 扩展 (HoareAssertAssume Module)

#### 10.1 assert_assume_differ
**类型**: Theorem  
**内容**: 证明 assert 和 assume 命令的行为差异
```coq
exists (P:Assertion) b (Q:Assertion), ({{P}} assume b {{Q}}) /\ ~ ({{P}} assert b {{Q}})
```

#### 10.2 assert_implies_assume
**类型**: Theorem  
**内容**: 证明 assert 的三元组蕴含对应的 assume 三元组
```coq
forall P b Q, ({{P}} assert b {{Q}}) -> ({{P}} assume b {{Q}})
```

#### 10.3 hoare_asgn, hoare_consequence_pre, hoare_consequence_post, hoare_seq (在 HoareAssertAssume 模块中)
**类型**: Theorem  
**内容**: 为新语义重新证明的基本霍尔规则

#### 10.4 hoare_skip, hoare_if, hoare_while (在 HoareAssertAssume 模块中)
**类型**: Theorem  
**内容**: 为新语义重新证明的其他霍尔规则

#### 10.5 hoare_assert
**类型**: Theorem  
**内容**: assert 命令的霍尔规则
```coq
forall P (b:bexp), {{P /\ b}} assert b {{P /\ b}}
```

#### 10.6 hoare_assume
**类型**: Theorem  
**内容**: assume 命令的霍尔规则
```coq
forall P (b:bexp), {{P}} assume b {{P /\ b}}
```

#### 10.7 assert_assume_example
**类型**: Example  
**内容**: 使用 assert 和 assume 规则的综合例子

## 总结

该文件系统地建立了霍尔逻辑的完整体系，包括：

1. **基础规则**: skip、赋值、序列组合的霍尔规则
2. **结构规则**: 前条件加强、后条件削弱等推理规则
3. **控制结构**: 条件语句、循环的霍尔规则
4. **语言扩展**: 
   - 单边条件语句 (if1)
   - 重复循环 (repeat-until)
   - 非确定性赋值 (havoc)
   - 断言和假设 (assert/assume)
5. **自动化**: 展示了如何使用 Coq 的自动化策略简化证明
6. **应用例子**: 大量的具体程序正确性证明例子

这些证明为程序验证提供了坚实的理论基础，展示了如何使用霍尔逻辑来推理程序的正确性。每个规则都有相应的正确性证明，确保了整个逻辑系统的可靠性。
