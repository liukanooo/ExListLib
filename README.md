# ExListLib - 扩展列表库

本库在`ListLib`基础上提供扩展功能，目前仅保留“自然数排列（Nperm）”与“区间列表（InvertalList）”两类模块，聚焦排列重排与有序区间约束。

## 文件结构

```
ExListLib/
├── Nperm.v         # 自然数排列
└── InvertalList.v  # 区间列表与整数排序
```

## 模块说明

### Nperm.v - 自然数排列

提供排列（permutation）的定义和操作，用于列表元素的重排。

#### 主要定义

**排列定义：**
- `nperm s`: `s`是`[0, 1, ..., length s - 1]`的一个排列
  - 定义：`Permutation (seq 0 (length s)) s`

**应用排列：**
- `apply_perm s l d`: 按排列`s`重排列表`l`
  - 定义：`map (fun n => nth n l d) s`

**恒等排列：**
- `identity_perm n`: 恒等排列`[0, 1, ..., n-1]`
  - 定义：`seq 0 n`

**逆排列：**
- `find_index l n`: 在列表`l`中查找`n`的位置
- `inverse_nperm s`: 排列`s`的逆排列

**特殊排列：**
- `swap_seq n1 n2`: 交换两段的排列
- `swap_seq2 n1 n2 n3`: 交换两个元素的排列

#### 核心引理

**基本性质：**
- `nperm_NoDup`: 排列无重复元素
- `nperm_range`: 排列中的元素都在有效范围内
- `identity_perm_is_is_nperm`: 恒等排列确实是排列
- `identity_perm_refl`: 恒等排列不改变列表

**查找与逆排列：**
- `find_index_nth`: 查找第n个元素的位置返回n
- `nth_find_index`: 查找元素在其位置处确实是该元素
- `inverse_nperm_nperm`: 逆排列也是排列

**应用排列性质：**
- `length_apply_perm`: 应用排列不改变长度
- `map_apply_perm`: map与apply_perm可交换
- `apply_perm_inverse_l`/`apply_perm_inverse_r`: 排列与逆排列互逆
- `apply_perm_is_permutation`: 应用排列得到原列表的排列

**Forall2保持：**
- `Forall2_nperm_congr`: `Forall2`在排列下保持
- `Forall2_nperm_congr_iff`: `Forall2`在排列下的等价性

**特殊排列：**
- `swap_seq2_is_nperm`: swap_seq2是有效排列
- `swap_nperm_apply_perm`: 交换两个元素的效果
- `swap_seq_is_nperm`: swap_seq是有效排列
- `swap_seq_apply_perm`: 交换两段的效果

### InvertalList.v - 区间列表

定义并研究元素间隔满足特定条件的列表，主要用于散列表分析。

#### 主要定义

**区间列表：**
- `interval_list pace lo hi l`: 列表`l`中元素取值范围`[lo, hi]`，相邻元素间隔至少为`pace`

**递增列表：**
- `Zincreasing l`: 列表`l`单调递增

**整数排序：**
- `Zinsert i l`: 将整数`i`插入有序整数列表
- `Zsort l`: 整数列表排序

#### 核心引理

**interval_list性质：**
- `interval_list_bounded_lt`: 区间列表元素有界
- `interval_list_NoDup`: 区间列表无重复
- `interval_perm_keep`: 排列保持区间列表性质
- `interval_list_compress`: 收缩区间保持性质
- `interval_list_range`: 区间列表的长度上界

**排序相关：**
- `Zinsert_In`: 插入后的成员关系
- `Zsort_Zincreasing`: 排序结果单调递增
- `Zinsert_perm`/`Zsort_perm`: 排序保持排列关系

**递增列表与区间列表：**
- `increasing_interval_list_range`: 递增区间列表的范围约束

## 使用示例

```coq
Require Import ExListLib.Nperm.
Require Import ExListLib.InvertalList.

(* 应用排列 *)
Example apply_perm_example:
  apply_perm [2; 0; 1] [10; 20; 30] 0 = [30; 10; 20].
Proof. reflexivity. Qed.

(* 区间列表示例 *)
Example interval_list_example:
  interval_list 1 0 5 [0;2;4].
Proof. repeat constructor; lia. Qed.
```

## 依赖关系

- **标准库**: `Coq.Lists.List`, `Coq.ZArith.ZArith`, `Coq.Sorting.Permutation`
- **项目依赖**: `ListLib` (Core, Positional, Basics)

## 常用引理索引

### 排列（Nperm）
- 定义：`nperm`, `identity_perm`
- 应用：`apply_perm`, `apply_perm_inverse_l`
- 逆排列：`inverse_nperm`, `find_index`
- 性质：`nperm_NoDup`, `apply_perm_is_permutation`

### 区间列表（InvertalList）
- 定义：`interval_list`, `Zincreasing`
- 性质：`interval_list_NoDup`, `interval_list_range`
- 排序：`Zsort`, `Zsort_perm`, `Zsort_Zincreasing`

---