import Mathlib.Data.Real.Basic

-- 定义一个分段函数
def piecewise_function (x : ℝ) : ℝ :=
  if x < 0 then -x
  else if x > 1 then x ^ 2
  else x

theorem piecewise_example (x : ℝ) : piecewise_function x ≥ 0 := by
  -- 展开函数定义
  unfold piecewise_function
  
  -- 使用 by_cases 进行情况分析
  by_cases h : x < 0
  · -- 情况1: x < 0
    rw [if_pos h]
    -- 使用 linarith 处理线性算术
    have : -x ≥ 0 := by linarith [show x < 0 from h]
    exact this
    
  · -- 情况2: x ≥ 0
    rw [if_neg h]
    
    -- 再次使用 by_cases 进行子情况分析
    by_cases h2 : x > 1
    · -- 子情况2.1: x > 1
      rw [if_pos h2]
      -- 使用 nlinarith 处理非线性算术
      nlinarith
      
    · -- 子情况2.2: 0 ≤ x ≤ 1
      rw [if_neg h2]
      -- 使用 linarith 证明 x ≥ 0
      linarith [show ¬(x > 1) from h2, show ¬(x < 0) from h]

-- 让我们再写一个更复杂的例子，展示更多 tactics
theorem piecewise_continuous (x : ℝ) : 
    piecewise_function (x + 1) - piecewise_function x ≤ 2 := by
  unfold piecewise_function
  
  -- 使用 by_cases 创建多个情况
  by_cases hx1 : x < 0
  · by_cases hx2 : x + 1 < 0
    · -- 情况1: x < 0 且 x+1 < 0
      rw [if_pos hx1, if_pos hx2]
      ring_nf
      linarith
      
    · -- 情况2: x < 0 但 x+1 ≥ 0
      rw [if_pos hx1, if_neg hx2]
      by_cases hx3 : x + 1 > 1
      · -- 子情况: x+1 > 1
        rw [if_pos hx3]
        have : x < 0 := hx1
        nlinarith
        
      · -- 子情况: 0 ≤ x+1 ≤ 1
        rw [if_neg hx3]
        linarith
        
  · -- 情况3: x ≥ 0
    rw [if_neg hx1]
    by_cases hx4 : x > 1
    · -- 子情况: x > 1
      rw [if_pos hx4]
      by_cases hx5 : x + 1 > 1
      · -- x+1 > 1
        rw [if_pos hx5]
        nlinarith
        
      · -- x+1 ≤ 1 (这实际上不可能，因为 x > 1)
        rw [if_neg hx5]
        exfalso  -- 产生矛盾
        linarith
        
    · -- 子情况: 0 ≤ x ≤ 1
      rw [if_neg hx4]
      by_cases hx6 : x + 1 > 1
      · -- x+1 > 1
        rw [if_pos hx6]
        nlinarith
        
      · -- x+1 ≤ 1
        rw [if_neg hx6]
        linarith

-- 展示更多 tactics 的例子
theorem piecewise_monotone (a b : ℝ) (h : a ≤ b) : 
    piecewise_function a ≤ piecewise_function b + 1 := by
  unfold piecewise_function
  
  -- 使用 cases' 进行情况分析（更强大的情况分析）
  by_cases ha : a < 0
  · rw [if_pos ha]
    by_cases hb : b < 0
    · rw [if_pos hb]
      linarith
      
    · rw [if_neg hb]
      by_cases hb2 : b > 1
      · rw [if_pos hb2]
        have : a ≤ b := h
        linarith
        
      · rw [if_neg hb2]
        linarith [show ¬(b < 0) from hb, show a < 0 from ha]
        
  · rw [if_neg ha]
    by_cases ha2 : a > 1
    · rw [if_pos ha2]
      by_cases hb : b < 0
      · -- 这种情况不可能，因为 a ≤ b 且 a > 1，但 b < 0
        exfalso
        linarith
        
      · rw [if_neg hb]
        by_cases hb2 : b > 1
        · rw [if_pos hb2]
          nlinarith
          
        · rw [if_neg hb2]
          nlinarith
          
    · rw [if_neg ha2]
      by_cases hb : b < 0
      · exfalso
        linarith
        
      · rw [if_neg hb]
        by_cases hb2 : b > 1
        · rw [if_pos hb2]
          nlinarith
          
        · rw [if_neg hb2]
          linarith

-- 使用 have 创建中间引理
theorem piecewise_special_values : 
    piecewise_function (-1) = 1 ∧ piecewise_function 0 = 0 ∧ piecewise_function 2 = 4 := by
  constructor
  · -- 证明 piecewise_function (-1) = 1
    unfold piecewise_function
    -- 使用 norm_num 处理具体数值计算
    norm_num
    
  constructor
  · -- 证明 piecewise_function 0 = 0
    unfold piecewise_function
    norm_num
    
  · -- 证明 piecewise_function 2 = 4
    unfold piecewise_function
    norm_num

-- 展示 field_simp 和 ring 的使用
theorem piecewise_ratio (x : ℝ) (hx : x ≠ 0) : 
    piecewise_function (2 * x) / piecewise_function x ≤ 2 := by
  unfold piecewise_function
  
  by_cases h1 : x < 0
  · by_cases h2 : 2 * x < 0
    · rw [if_pos h1, if_pos h2]
      field_simp
      linarith
      
    · rw [if_pos h1, if_neg h2]
      by_cases h3 : 2 * x > 1
      · rw [if_pos h3]
        field_simp
        nlinarith
        
      · rw [if_neg h3]
        field_simp
        linarith
        
  · rw [if_neg h1]
    by_cases h4 : x > 1
    · rw [if_pos h4]
      by_cases h5 : 2 * x > 1
      · rw [if_pos h5]
        field_simp
        ring_nf
        nlinarith
        
      · rw [if_neg h5]
        field_simp
        nlinarith
        
    · rw [if_neg h4]
      by_cases h6 : 2 * x > 1
      · rw [if_pos h6]
        field_simp
        nlinarith
        
      · rw [if_neg h6]
        field_simp
        linarith






import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 定义分段函数 f
def f (x : ℝ) : ℝ :=
  if x ≥ 0 then x + 1 else -x

-- 要证明的定理：对任意实数 x，f x ≥ 0
theorem f_nonneg : ∀ x : ℝ, f x ≥ 0 := by
  intro x
  -- 使用 `split_ifs` 拆分 if-then-else 的两种情况
  split_ifs with h
  · -- 情况1: x ≥ 0
    -- 目标是 x + 1 ≥ 0
    -- 因为 x ≥ 0 ⇒ x + 1 ≥ 1 > 0
    have h1 : x + 1 ≥ 1 := by linarith
    linarith
  · -- 情况2: ¬(x ≥ 0)，即 x < 0
    -- 目标是 -x ≥ 0，即 x ≤ 0
    -- 但我们有 x < 0，所以 -x > 0 ⇒ -x ≥ 0
    have h2 : x < 0 := by
      -- 从 ¬(x ≥ 0) 推出 x < 0
      exact lt_of_not_ge h
    have h3 : -x > 0 := by linarith
    linarith



import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Cast
import Mathlib.Tactic

open Set

-- 定义嵌套分段函数 g
def g (x : ℝ) : ℝ :=
  if hx : ∃ n : ℤ, x = n then
    if x ≥ 0 then x^2 + 1 else -x
  else
    if x > 0 then 1 / x else 0

-- 辅助引理：若 x 是整数且 x ≥ 0，则 x^2 + 1 ≥ 1 > 0
lemma int_nonneg_sq_plus_one (x : ℝ) (h_int : ∃ n : ℤ, x = n) (h_ge : x ≥ 0) : x^2 + 1 ≥ 1 := by
  rcases h_int with ⟨n, rfl⟩
  have h1 : (n : ℝ)^2 ≥ 0 := by apply sq_nonneg
  linarith

-- 辅助引理：若 x 是负整数，则 -x > 0
lemma neg_of_neg_int (x : ℝ) (h_int : ∃ n : ℤ, x = n) (h_lt : x < 0) : -x > 0 := by
  rcases h_int with ⟨n, rfl⟩
  have hn : (n : ℝ) < 0 := h_lt
  exact neg_pos.mpr hn

-- 主定理：g x ≥ 0 对所有实数 x 成立
theorem g_nonneg : ∀ x : ℝ, g x ≥ 0 := by
  intro x
  -- 第一层：是否为整数？
  by_cases h_int : ∃ n : ℤ, x = n
  · -- 情况1: x 是整数
    -- 第二层：x ≥ 0 ?
    split_ifs with h_ge
    · -- 子情况1a: x ≥ 0 → g x = x^2 + 1
      have h1 : x^2 + 1 ≥ 1 := int_nonneg_sq_plus_one x h_int h_ge
      linarith
    · -- 子情况1b: x < 0 → g x = -x
      have h_lt : x < 0 := lt_of_not_ge h_ge
      have h2 : -x > 0 := neg_of_neg_int x h_int h_lt
      linarith
  · -- 情况2: x 不是整数
    -- 第二层：x > 0 ?
    split_ifs with h_pos
    · -- 子情况2a: x > 0 且非整数 → g x = 1 / x
      have h3 : x > 0 := h_pos
      have h4 : 1 / x > 0 := one_div_pos.mpr h3
      linarith
    · -- 子情况2b: x ≤ 0 且非整数 → g x = 0
      rw [g]
      simp [h_int, h_pos]  -- 简化表达式，确认值为 0
      norm_num  -- 0 ≥ 0 得证
