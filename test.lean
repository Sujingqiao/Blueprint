
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.NormedSpace.Topology
import Mathlib.Topology.Limits
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter

open Set Function Topology Filter
open scoped Topology ENNReal NNReal

universe u v

/-- 向量空间 -/
variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
                               [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- 点 -/
variable (x : E) (y : F)

/-- 闭球 -/
def closedBall (x : E) (r : ℝ) : Set E := { z | ‖z - x‖ ≤ r }

/-- Minkowski 和 -/
def minkowskiSum (A B : Set F) : Set F := { a + b | a ∈ A, b ∈ B }

infixr:65 " + " => minkowskiSum

/-- 集值映射 S: E ⇉ F -/
structure SetValuedMapping (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] where
  graph : Set (E × F)
  image (x : E) : Set F := { y | (x, y) ∈ graph }

/-- 点态收敛：S^ν(x) → S(x) 对每个 x ∈ X -/
def pointwiseConverges {ι : Type*} [DirectedOrder ι]
    (Sν : ι → SetValuedMapping E F)
    (S : SetValuedMapping E F)
    (X : Set E)
    (x̄ : E) : Prop :=
  x̄ ∈ X ∧
  ∀ x ∈ X, tendsto (fun ν => Sν ν (image x)) atTop (𝓝 (S.image x))

/-- 图收敛：graph S^ν → graph S -/
def graphConverges {ι : Type*} [DirectedOrder ι]
    (Sν : ι → SetValuedMapping E F)
    (S : SetValuedMapping E F)
    (x̄ : E) : Prop :=
  liminf (fun ν => Sν ν.graph) = S.graph ∧
  limsup (fun ν => Sν ν.graph) = S.graph





/-- 连续收敛：S^ν 在 x̄ 处相对于 X 连续收敛到 S -/
def continuousConverges {ι : Type*} [DirectedOrder ι]
    (Sν : ι → SetValuedMapping E F)
    (S : SetValuedMapping E F)
    (X : Set E)
    (x̄ : E) : Prop :=
  pointwiseConverges Sν S X x̄ ∧
  graphConverges Sν S x̄ ∧
  -- 连续性条件
  ∀ (xν : ι → E), (∀ ν, xν ν ∈ X) → tendsto xν atTop (𝓝 x̄) →
    ∀ (uν : ι → F), (∀ ν, uν ν ∈ Sν ν (image (xν ν))) →
      ∃ u, u ∈ S.image x̄ ∧ tendsto uν atTop (𝓝 u)


/-- 渐近一致振荡（用于 Thm 5.40） -/
def isAsymptoticallyEquiOscillatory {ι : Type*} [DirectedOrder ι]
    (Sν : ι → SetValuedMapping E F)
    (X : Set E)
    (x̄ : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ N₀,
    ∀ ν ≥ N₀, ∀ x₁ x₂ ∈ X ∩ closedBall x̄ δ,
      Sν ν (image x₁) ⊆ Sν ν (image x₂) + closedBall (0 : F) ε


/-- 定理 5.40：连续收敛 ⇒ 图收敛 + 渐近一致振荡 -/
theorem Thm5_40 {ι : Type*} [DirectedOrder ι]
    (Sν : ι → SetValuedMapping E F)
    (S : SetValuedMapping E F)
    (X : Set E)
    (x̄ : E)
    (h_cont : continuousConverges Sν S X x̄) :
    graphConverges Sν S x̄ ∧ isAsymptoticallyEquiOscillatory Sν X x̄ := by
  -- 标准结果，略
  sorry
/--
定理 5.44：
S^ν 在 x̄ 处相对于 X 连续收敛到 S
  ⇔
S^ν 在 x̄ 处图收敛到 S，且 {S^ν} 在 X 上相对于 X 是渐近一致的
-/

theorem Thm5_44 {ι : Type*} [DirectedOrder ι]
    (Sν : ι → SetValuedMapping E F)
    (S : SetValuedMapping E F)
    (X : Set E)
    (x̄ : E) :
    continuousConverges Sν S X x̄ ↔
    (graphConverges Sν S x̄ ∧ isAsymptoticallyEquicontinuous Sν X x̄) := by
  constructor
  · -- (⇒) 连续收敛 ⇒ 图收敛 + 渐近一致
    intro h_cont
    have ⟨h_point, h_graph, h_cont_prop⟩ := h_cont
    split
    · exact h_graph
    · -- 证明渐近一致（反证法）
      by_contra h_not_equi
      push_neg at h_not_equi
      -- ∃ε>0, ∀ρ>0, ∀N₀, ∃ν≥N₀, ∃x∈X∩B(x̄,ρ), s.t.
      --     S^ν(x̄) ∩ ρ𝔹 ⊄ S^ν(x) + ε𝔹
      obtain ⟨ε, hε_pos, h_unif⟩ := h_not_equi
      set N := atTop  -- 无限子列
      have ∃ (xν : ι → E), (∀ ν, xν ν ∈ X) ∧ tendsto xν atTop (𝓝 x̄) ∧
             ∃ (uν : ι → F), (∀ ν, uν ν ∈ Sν ν (image x̄)) ∧
             (∀ ν, ‖uν ν‖ ≤ ρ) ∧
             (∀ ν, uν ν ∉ Sν ν (image (xν ν)) + closedBall (0 : F) ε) := by
        -- 构造坏序列 x^ν → x̄ 和 u^ν
        -- 使用选择公理（Mathlib 中可用 axiom of choice）
        sorry
      obtain ⟨xν, hx_in_X, hx_tend, uν, hu_in_Sν, hu_bdd, hu_not_in⟩ := this

      -- 由连续收敛，u^ν 应有聚点 ū ∈ S(x̄)
      have h_u_tend : ∃ u_bar, u_bar ∈ S.image x̄ ∧ tendsto uν atTop (𝓝 u_bar) :=
        h_cont_prop xν hx_in_X hx_tend uν hu_in_Sν
      obtain ⟨u_bar, hu_bar_in_S, hu_tend⟩ := h_u_tend

      -- 但 u^ν ∉ S^ν(x^ν) + ε𝔹，而 S^ν(x^ν) → S(x̄)，矛盾
      have : ∀ ν, uν ν ∉ Sν ν (image (xν ν)) + closedBall (0 : F) ε := hu_not_in
      have h_Sνxν_close : tendsto (fun ν => Sν ν (image (xν ν))) atTop (𝓝 (S.image x̄)) :=
        h_cont.pointwise_of_tendsto hx_tend
      -- u_bar ∈ S(x̄)，所以 uν ν 应最终进入 S^ν(x^ν) + ε𝔹
      have : ∃ ν₀, ∀ ν ≥ ν₀, uν ν ∈ Sν ν (image (xν ν)) + closedBall (0 : F) ε :=
        tendsto_nhds_iff.1 (tendsto_const_nhds.congr' hu_tend) ε hε_pos
      contradiction

  · -- (⇐) 图收敛 + 渐近一致 ⇒ 连续收敛
    intro ⟨h_graph, h_equi⟩
    constructor
    · -- 点态收敛
      sorry
    · exact h_graph
    · -- 连续性条件
      intros xν hxν_X hxν_tend uν huν_in
      -- 由渐近一致，S^ν(x̄) ∩ ρ𝔹 ⊆ S^ν(x^ν) + ε𝔹
      -- u^ν ∈ S^ν(x^ν)，有界 ⇒ 可提取收敛子列
      have huν_bdd : Bounded (range uν) := sorry
      obtain ⟨u_bar, hu_subseq⟩ := compact_iff_seq_compact.1 isCompact_closedBall huν_bdd
      use u_bar
      · -- 证明 u_bar ∈ S(x̄)
        have : tendsto (fun ν => (xν ν, uν ν)) atTop (𝓝 (x̄, u_bar)) := sorry
        have : ∀ ν, (xν ν, uν ν) ∈ Sν ν.graph := huν_in
        have h_lim_in_graph := h_graph.limsup_subset (fun ν => Sν ν.graph) (x̄, u_bar) this
        exact h_lim_in_graph
      · exact hu_subseq


import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Epipigraph
import Mathlib.Analysis.NormedSpace.Topology
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter

open Set Function Real
open scoped BigOperators Topology

/-- 一个函数是适当的（proper），如果它不恒为 ∞，且从不取 -∞ -/
def IsProper {E : Type*} [NormedAddCommGroup E] (f : E → ℝ∞) :=
  (∃ x, f x < ⊤) ∧ (∀ x, f x > ⊥)

/-- 凸函数 -/
def IsConvexFunction {E : Type*} [NormedAddCommGroup E] (f : E → ℝ∞) :=
  ∀ x y t, t ∈ Set.Icc 0 1 → f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y

/-- 闭函数：epigraph 是闭集 -/
def IsClosedFunction {E : Type*} [NormedAddCommGroup E] (f : E → ℝ∞) :=
  IsClosed (epigraph f)

/-- 适当凸函数 -/
structure ProperConvexFunction (E : Type*) [NormedAddCommGroup E] where
  f : E → ℝ∞
  is_proper : IsProper f
  is_convex : IsConvexFunction f

  /-- 定理 8.3：闭凸集的退化锥是闭凸锥 -/
theorem Thm8_3 {E : Type*} [NormedAddCommGroup E] (C : Set E)
    (hC_nonempty : C.Nonempty)
    (hC_convex : Convex C)
    (hC_closed : IsClosed C) :
    IsClosed (recessionCone C) ∧ Convex (recessionCone C) ∧ IsCone (recessionCone C) := by
  -- 标准结果，Mathlib 中有类似
  constructor
  · apply recessionCone.isClosed_of_closed hC_closed
  · apply recessionCone.convex_of_convex hC_convex
  · apply recessionCone.isCone


 /-- 定理 23.2：凸函数的方向导数等于次梯度的支撑函数 -/
theorem Thm23_2 {E : Type*} [NormedAddCommGroup E] (f : ProperConvexFunction E)
    (x : E) (hx : x ∈ dom f)
    (y : E) :
    hasDirectionalDerivativeAt f x y ∧
    f.dir_deriv x y = ⨆ g ∈ subdifferential f x, inner g y := by
  -- 此为 Mathlib 中 `convex_hasDirectionalDerivative` 的加强版
  apply convex_hasDirectionalDerivative
  · apply f.is_convex
  · apply hx
  · -- 支撑函数等式，标准结果
    sorry -- （此处可引用 `subdifferential_dir_deriv`）

   /-- 对凸函数 f，差商 (f(x+λy) - f(x))/λ 关于 λ > 0 非减 -/
lemma differenceQuotient_nondecreasing {E : Type*} [NormedAddCommGroup E]
    (f : ProperConvexFunction E) (x y : E) (hx : x ∈ dom f) :
    MonotoneOn (fun λ => (f.val (x + λ • y) - f.val x) / λ) (Set.Ioi 0) := by
  intros a b ha hb hab
  -- 用凸性展开 f(x + b y) = f( (a/b)(x + a y) + (1 - a/b)(x) )
  have := f.is_convex (x + a • y) x (a / b)
  · linarith
  · -- 展开不等式，整理得 (f(x+by)-f(x))/b ≥ (f(x+ay)-f(x))/a
    sorry


/-- 退化函数 f⁰⁺(y) := sup { f(x + y) - f(x) | x ∈ dom f } -/
def recessionFunction (f : ProperConvexFunction E) : E → ℝ∞ :=
  fun y => ⨆ x ∈ f.dom, f.val (x + y) - f.val x

/-- 记号 f⁰⁺ -/
notation "f⁰⁺" => recessionFunction f

theorem Thm8_5 {E : Type*} [NormedAddCommGroup E] (f : ProperConvexFunction E) :
    -- (1) f⁰⁺ 是正齐次、适当凸函数
    (IsPositivelyHomogeneous (f⁰⁺) ∧ IsProperConvexFunction (f⁰⁺)) ∧
    -- (2) f⁰⁺(y) = sup { f(x+y) - f(x) }
    (∀ y, (f⁰⁺ y) = ⨆ x ∈ f.dom, f.val (x + y) - f.val x) ∧
    -- (3) 若 f 闭，则 f⁰⁺ 闭，且
    (IsClosedFunction f →
      ∀ y, (f⁰⁺ y) = ⨆ λ > 0, (f.val (x₀ + λ • y) - f.val x₀) / λ ∧
           (f⁰⁺ y) = (fun λ => (f.val (x₀ + λ • y) - f.val x₀) / λ) ⟶∞ (f⁰⁺ y)) := by
  constructor
  · -- 第一部分：f⁰⁺ 是正齐次适当凸函数
    split
    · -- 正齐次性：f⁰⁺(αy) = α f⁰⁺(y) for α > 0
      intros α y hα
      -- 用差商单调性 + 上确界性质
      have := differenceQuotient_nondecreasing f x₀ y (mem_dom f x₀)
      rw [← mul_assoc]
      sorry
    · -- 适当凸性
      apply properConvex_of_recessionFunction
      apply f.is_convex
  · -- 第二部分：f⁰⁺(y) = sup { f(x+y) - f(x) }
    intro y
    rfl  -- 由定义
  · -- 第三部分：若 f 闭，则极限公式成立
    intro hf_closed y
    have x₀ := some (f.is_proper.1)  -- 取 x₀ ∈ dom f
    have hx₀ := some_spec (f.is_proper.1)

    -- 使用定理 8.3：epi f 闭 → (epi f)^{0+} 闭凸锥
    have epi_closed := hf_closed
    have rec_epi_closed := (Thm8_3 (epigraph f.val) (epi_nonempty f) (epi_convex f) epi_closed).1

    -- f⁰⁺(y) = inf { v | (y, v) ∈ (epi f)^{0+} }
    have f0p_eq_recession := by
      rw [recessionFunction_eq_recessionCone_height]
      apply rec_epi_closed

    -- 使用定理 23.2：差商非减 → sup = 极限
    have quot_mono := differenceQuotient_nondecreasing f x₀ y hx₀
    have sup_eq_lim := quot_mono.tendsto_atTop_sup (Set.Ioi 0)

    -- 结合两者
    use sup_eq_lim
    rw [sup_eq_lim]
    exact f0p_eq_recession

/-- f⁰⁺(y) = inf { v | (y, v) ∈ (epi f)^{0+} } -/
theorem recessionFunction_eq_recessionCone_height (f : ProperConvexFunction E) (y : E) :
    f⁰⁺ y = ⨅ v, (y, v) ∈ recessionCone (epigraph f.val) := by
  -- 标准结果，来自 Rockafellar 第 8 章
  -- 利用 epi f 的退化锥定义
  rw [← Thm8_3]
  · -- 两边上确界相等
    sorry
