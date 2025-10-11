import Mathlib


open Complex Matrix EuclideanSpace InnerProductSpace

variable {𝕂} [NormedField 𝕂] [CompleteSpace 𝕂]
variable {n} (ρ : Matrix (Fin n) (Fin n) ℂ)

-- Use the standard partial order on ℂ: z ≤ w iff z.re ≤ w.re ∧ z.im = w.im
attribute [local instance] Complex.partialOrder


noncomputable def Matrix.log
{n : ℕ}
[NormedField 𝕂]
[CompleteSpace 𝕂]
(A : Matrix (Fin n) (Fin n) 𝕂)
:
Matrix (Fin n) (Fin n) 𝕂 := ∑' i : ℕ, ((-1)^(i+1) : 𝕂) • (1 / (i+1 : 𝕂)) • ((1 - A) ^ (i+1))


-- The von Neumann entropy of a density matrix using the standard formula S = -tr(ρ ln ρ)
noncomputable def vonNeumannEntropy
{n : ℕ}
[NormedField 𝕂]
[CompleteSpace 𝕂]
(ρ : Matrix (Fin n) (Fin n) 𝕂)
:
𝕂 := -1 * Matrix.trace (ρ * Matrix.log ρ)


-- A function f: ℝⁿ → ℝ is Schur-convex if x ≺ y implies f(x) ≤ f(y) where ≺ denotes the majorization ordering
def SchurConvex {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (x y : Fin n → ℝ),
    (∀ i, 0 ≤ x i) →
    (∀ i, 0 ≤ y i) →
    (let x_dual : Fin n → OrderDual ℝ := fun i => OrderDual.toDual (x i)
     let y_dual : Fin n → OrderDual ℝ := fun i => OrderDual.toDual (y i)
     let σ := Tuple.sort x_dual
     let τ := Tuple.sort y_dual
    (∀ k : Fin n, ∑ i ∈ (Finset.univ.filter (· ≤ k)), x (σ i) ≤ ∑ i ∈ (Finset.univ.filter (· ≤ k)), y (τ i)) ∧ (∑ i, x i = ∑ i, y i)) →
    f x ≤ f y




theorem vonNeumannEntropy_hermitian
{n : ℕ}
(A : Matrix (Fin n) (Fin n) ℂ)
(hA : A.IsHermitian)
:
vonNeumannEntropy A = -1 * ∑ i, hA.eigenvalues i * Real.log (hA.eigenvalues i) := by
  sorry




-- Slope comparison lemma with strict inequalities (original hypothesis)
lemma slope_comparison_tlogt_strict_1
(a b c d : ℝ)
(ha : 0 ≤ a)
(hb : 0 ≤ b)
(hc : 0 ≤ c)
(hd : 0 ≤ d)
(hac : a ≥ c)
(hbd : b ≥ d)
(hab : a > b)
(hcd : c > d)
:
(c * Real.log c - d * Real.log d) / (c - d) ≤ (a * Real.log a - b * Real.log b) / (a - b) := by
  have f_convex : ConvexOn ℝ (Set.Ici 0) (fun t => t * Real.log t) := Real.convexOn_mul_log
  have hmem_a : a ∈ Set.Ici (0:ℝ) := ha
  have hmem_b : b ∈ Set.Ici (0:ℝ) := hb
  have hmem_c : c ∈ Set.Ici (0:ℝ) := hc
  have hmem_d : d ∈ Set.Ici (0:ℝ) := hd
  have hab_pos : 0 < a - b := sub_pos.mpr hab
  have hcd_pos : 0 < c - d := sub_pos.mpr hcd
  have had_pos : 0 < a - d := sub_pos.mpr (lt_of_lt_of_le hcd hac)
  have step1 :
    (c * Real.log c - d * Real.log d) / (c - d)
    ≤ (a * Real.log a - d * Real.log d) / (a - d) := by
    have hca_le : c ≤ a := hac
    have h_ne_cd : c ≠ d := ne_of_gt hcd
    have h_ne_ad : a ≠ d := ne_of_gt (lt_of_lt_of_le hcd hac)
    exact f_convex.secant_mono hmem_d hmem_c hmem_a h_ne_cd h_ne_ad hca_le
  have step2 :
    (a * Real.log a - d * Real.log d) / (a - d)
    ≤ (a * Real.log a - b * Real.log b) / (a - b) := by
    have hdb_le : d ≤ b := hbd
    have h_ne_da : d ≠ a := ne_of_lt (lt_of_lt_of_le hcd hac)
    have h_ne_ba : b ≠ a := ne_of_lt hab
    have secant_result := f_convex.secant_mono hmem_a hmem_d hmem_b h_ne_da h_ne_ba hdb_le
    have h_left : (d * Real.log d - a * Real.log a) / (d - a) =
                  (a * Real.log a - d * Real.log d) / (a - d) := by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]
    have h_right : (b * Real.log b - a * Real.log a) / (b - a) =
                   (a * Real.log a - b * Real.log b) / (a - b) := by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]
    rw [h_left, h_right] at secant_result
    exact secant_result
  exact le_trans step1 step2



lemma slope_comparison_tlogt_strict_2
(a b c d : ℝ)
(ha : 0 ≤ a)
(hb : 0 ≤ b)
(hc : 0 ≤ c)
(hd : 0 ≤ d)
(hac : a ≥ c)
(hbd : b ≥ d)
(hab : a < b)
(hcd : c < d)
:
(c * Real.log c - d * Real.log d) / (c - d) ≤ (a * Real.log a - b * Real.log b) / (a - b) := by
  have f_convex : ConvexOn ℝ (Set.Ici 0) (fun t => t * Real.log t) := Real.convexOn_mul_log
  have hmem_a : a ∈ Set.Ici (0:ℝ) := ha
  have hmem_b : b ∈ Set.Ici (0:ℝ) := hb
  have hmem_c : c ∈ Set.Ici (0:ℝ) := hc
  have hmem_d : d ∈ Set.Ici (0:ℝ) := hd
  have slope_equiv_c_d : (c * Real.log c - d * Real.log d) / (c - d) =
    (d * Real.log d - c * Real.log c) / (d - c) := by rw [← neg_div_neg_eq, neg_sub, neg_sub]
  have slope_equiv_a_b : (a * Real.log a - b * Real.log b) / (a - b) =
    (b * Real.log b - a * Real.log a) / (b - a) := by rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [slope_equiv_c_d, slope_equiv_a_b]
  by_cases h_order : d ≤ a

  case pos =>
    by_cases h_eq : d = a
    case pos =>
      subst h_eq
      exact f_convex.slope_mono_adjacent hmem_c hmem_b hcd hab
    case neg =>
      have hda : d < a := lt_of_le_of_ne h_order h_eq
      have step1 := f_convex.slope_mono_adjacent hmem_c hmem_a hcd hda
      have step2 := f_convex.slope_mono_adjacent hmem_d hmem_b hda hab
      exact le_trans step1 step2

  case neg =>
    push_neg at h_order
    have had : a < d := h_order

    by_cases h_eq : d = b
    case pos =>
      subst h_eq
      by_cases h_ca : c = a
      case pos => subst h_ca; simp
      case neg =>
        have hca : c < a := lt_of_le_of_ne hac h_ca
        exact f_convex.secant_mono_aux3 hmem_c hmem_b hca hab
    case neg =>
      have hdb : d < b := lt_of_le_of_ne hbd h_eq
      have step1 : (d * Real.log d - c * Real.log c) / (d - c) ≤
                   (d * Real.log d - a * Real.log a) / (d - a) := by
        by_cases h_ca : c = a
        case pos => subst h_ca; simp
        case neg =>
          have hca : c < a := lt_of_le_of_ne hac h_ca
          exact f_convex.secant_mono_aux3 hmem_c hmem_d hca had
      have step2 := f_convex.secant_mono_aux2 hmem_a hmem_b had hdb
      exact le_trans step1 step2




lemma slope_comparison_tlogt_strict_3
(a b c d : ℝ)
(ha : 0 ≤ a)
(hb : 0 ≤ b)
(hc : 0 ≤ c)
(hd : 0 ≤ d)
(hac : a ≥ c)
(hab : a < b)
(hcd : c > d)
:
(c * Real.log c - d * Real.log d) / (c - d) ≤ (a * Real.log a - b * Real.log b) / (a - b) := by
  have f_convex : ConvexOn ℝ (Set.Ici 0) (fun t => t * Real.log t) := Real.convexOn_mul_log
  have hmem_a : a ∈ Set.Ici (0:ℝ) := ha
  have hmem_b : b ∈ Set.Ici (0:ℝ) := hb
  have hmem_c : c ∈ Set.Ici (0:ℝ) := hc
  have hmem_d : d ∈ Set.Ici (0:ℝ) := hd
  have slope_equiv_a_b : (a * Real.log a - b * Real.log b) / (a - b) =
    (b * Real.log b - a * Real.log a) / (b - a) := by rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [slope_equiv_a_b]
  by_cases h_order : c ≤ a
  case pos =>
    by_cases h_eq : c = a
    case pos =>
      subst h_eq
      have hdc : d < c := hcd
      exact f_convex.slope_mono_adjacent hmem_d hmem_b hdc hab
    case neg =>
      have hca : c < a := lt_of_le_of_ne h_order h_eq
      have hdc : d < c := hcd
      have step1 := f_convex.slope_mono_adjacent hmem_d hmem_a hdc hca
      have step2 := f_convex.slope_mono_adjacent hmem_c hmem_b hca hab
      exact le_trans step1 step2
  case neg =>
    push_neg at h_order
    have hac_lt : a < c := h_order
    have : a ≥ c := hac
    linarith



lemma slope_comparison_tlogt_strict_4
(a b c d : ℝ)
(ha : 0 ≤ a)
(hb : 0 ≤ b)
(hc : 0 ≤ c)
(hd : 0 ≤ d)
(_hac : a ≥ c)
(hbd : b ≥ d)
(hab : a > b)
(hcd : c < d)
:
(c * Real.log c - d * Real.log d) / (c - d) ≤ (a * Real.log a - b * Real.log b) / (a - b) := by
  have f_convex : ConvexOn ℝ (Set.Ici 0) (fun t => t * Real.log t) := Real.convexOn_mul_log
  have hmem_a : a ∈ Set.Ici (0:ℝ) := ha
  have hmem_b : b ∈ Set.Ici (0:ℝ) := hb
  have hmem_c : c ∈ Set.Ici (0:ℝ) := hc
  have hmem_d : d ∈ Set.Ici (0:ℝ) := hd
  have slope_equiv_c_d : (c * Real.log c - d * Real.log d) / (c - d) =
    (d * Real.log d - c * Real.log c) / (d - c) := by rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [slope_equiv_c_d]
  have hba : b < a := hab
  have hdc : d > c := hcd
  have h_result := slope_comparison_tlogt_strict_3 b a d c hb ha hd hc hbd hba hdc
  have h_equiv : (a * Real.log a - b * Real.log b) / (a - b) =
                 (b * Real.log b - a * Real.log a) / (b - a) := by
    rw [← neg_div_neg_eq, neg_sub, neg_sub]
  rw [h_equiv]
  exact h_result


lemma slope_comparison_tlogt (a b c d : ℝ)
  (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
  (hac : a ≥ c) (hbd : b ≥ d) (hab : a ≠ b) (hcd : c ≠ d) :
  (c * Real.log c - d * Real.log d) / (c - d) ≤
  (a * Real.log a - b * Real.log b) / (a - b) := by
  cases' lt_or_gt_of_ne hab with hab_lt hab_gt
  case inl =>
    cases' lt_or_gt_of_ne hcd with hcd_lt hcd_gt
    case inl =>
      exact slope_comparison_tlogt_strict_2 a b c d ha hb hc hd hac hbd hab_lt hcd_lt
    case inr =>
      exact slope_comparison_tlogt_strict_3 a b c d ha hb hc hd hac hab_lt hcd_gt
  case inr =>
    cases' lt_or_gt_of_ne hcd with hcd_lt hcd_gt
    case inl =>
      exact slope_comparison_tlogt_strict_4 a b c d ha hb hc hd hac hbd hab_gt hcd_lt
    case inr =>
      exact slope_comparison_tlogt_strict_1 a b c d ha hb hc hd hac hbd hab_gt hcd_gt


lemma telescoping_identity (f : Fin n → ℝ) (i : Fin n) :
  f i = (∑ j ∈ Finset.univ with j ≤ i, f j) - (∑ j ∈ Finset.univ with j < i, f j) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [le_refl, if_true, lt_irrefl, if_false, sub_zero]
  · intro j _ hjne
    by_cases h : j ≤ i
    · have : j < i := lt_of_le_of_ne h hjne
      simp only [h, this, if_true, sub_self]
    · have : ¬(j < i) := by
        intro hlt
        exact h (le_of_lt hlt)
      simp only [h, this, if_false, sub_zero]
  · simp



lemma schur_convex_reduction_to_distinct {m : ℕ} (hm : 0 < m) (x y : Fin m → ℝ) :
  (∀ i : Fin m, 0 ≤ x i) →
  (∀ i : Fin m, 0 ≤ y i) →
  (∀ i j : Fin m, i ≤ j → x j ≤ x i) →
  (∀ i j : Fin m, i ≤ j → y j ≤ y i) →
  (∀ i : Fin m, x i ≠ y i) →
  (∀ k : Fin m, ∑ i ∈ (Finset.univ.filter (· ≤ k)), x i ≤ ∑ i ∈ (Finset.univ.filter (· ≤ k)), y i) →
  (∑ i, x i = ∑ i, y i) →
  ∑ i, x i * Real.log (x i) ≤ ∑ i, y i * Real.log (y i) := by
  intro hx_nonneg hy_nonneg hx_dec hy_dec hdist hmaj hsum

  let ci := fun i => (x i * Real.log (x i) - y i * Real.log (y i)) / (x i - y i)
  let c_i_plus_1 := fun i : Fin m => if h : i.val + 1 < m then
    let j : Fin m := ⟨i.val + 1, h⟩
    (x j * Real.log (x j) - y j * Real.log (y j)) / (x j - y j)
  else 0

  have ci_leq_ci_plus_1 : ∀ i : Fin m, ∀ h : i.val + 1 < m,
    x i ≠ y i →
    x ⟨i.val + 1, h⟩ ≠ y ⟨i.val + 1, h⟩ →
    c_i_plus_1 i ≤ ci i := by
    intro i hi_range hx_i_neq hx_j_neq
    have h1_sorted : let j_next : Fin m := ⟨i.val + 1, hi_range⟩
      x i ≥ x j_next ∧ y i ≥ y j_next := by
      let j_next : Fin m := ⟨i.val + 1, hi_range⟩
      constructor
      · apply hx_dec
        simp only [Fin.le_iff_val_le_val]
        exact Nat.le_succ _
      · apply hy_dec
        simp only [Fin.le_iff_val_le_val]
        exact Nat.le_succ _

    simp only [ci, c_i_plus_1, dif_pos hi_range]
    let j_next : Fin m := ⟨i.val + 1, hi_range⟩
    obtain ⟨hx_sorted, hy_sorted⟩ := h1_sorted
    have hx_j_neq_actual : x j_next ≠ y j_next := by convert hx_j_neq
    exact slope_comparison_tlogt (x i) (y i) (x j_next) (y j_next)
      (hx_nonneg i) (hy_nonneg i) (hx_nonneg j_next) (hy_nonneg j_next)
      hx_sorted hy_sorted hx_i_neq hx_j_neq_actual

  have term_rewrite : ∀ i : Fin m,
    x i * Real.log (x i) - y i * Real.log (y i) =
    ci i * (x i - y i) := by
    intro i
    simp only [ci]
    have h_neq : x i - y i ≠ 0 := by
      intro h_eq
      have : x i = y i := by linarith [h_eq]
      exact hdist i this
    field_simp [h_neq]

  suffices h : ∑ i, x i * Real.log (x i) - ∑ i, y i * Real.log (y i) ≤ 0 by linarith

  have sum_rewrite : ∑ i, x i * Real.log (x i) - ∑ i, y i * Real.log (y i) = ∑ i, ci i * (x i - y i) := by
    calc ∑ i, x i * Real.log (x i) - ∑ i, y i * Real.log (y i)
      = ∑ i, (x i * Real.log (x i) - y i * Real.log (y i)) := by rw [← Finset.sum_sub_distrib]
      _ = ∑ i, ci i * (x i - y i) := by simp only [term_rewrite]

  rw [sum_rewrite]

  have telescoping_diff : ∀ i : Fin m, (x i - y i) =
    ((∑ j with j ≤ i, x j) - (∑ j with j ≤ i, y j)) -
    ((∑ j with j < i, x j) - (∑ j with j < i, y j)) := by
    intro i
    rw [telescoping_identity x i, telescoping_identity y i]
    ring

  have sum_telescoping : ∑ i, ci i * (x i - y i) =
    ∑ i, ci i * ((∑ j with j ≤ i, x j) - (∑ j with j ≤ i, y j)) -
    ∑ i, ci i * ((∑ j with j < i, x j) - (∑ j with j < i, y j)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [telescoping_diff i]
    simp only [mul_sub]

  rw [sum_telescoping]

  have group_terms :
    ∑ i, ci i * ((∑ j with j ≤ i, x j) - (∑ j with j ≤ i, y j)) -
    ∑ i, ci i * ((∑ j with j < i, x j) - (∑ j with j < i, y j)) =
    ∑ i, ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) -
    ∑ i, ci i * (∑ j with j < i, x j - ∑ j with j < i, y j) := by
    simp only [← Finset.sum_sub_distrib]

  rw [group_terms]
  let i_max : Fin m := ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩

  have largest_index_zero :
    ∑ j with j ≤ i_max, x j - ∑ j with j ≤ i_max, y j = 0 := by
    have all_le : ∀ j : Fin m, j ≤ i_max := by
      intro j
      simp only [i_max, Fin.le_iff_val_le_val]
      exact Nat.le_pred_of_lt j.isLt
    have sum_x_total : ∑ j with j ≤ i_max, x j = ∑ j, x j := by
      rw [Finset.sum_filter]
      congr 1
      ext j
      simp [all_le j]
    have sum_y_total : ∑ j with j ≤ i_max, y j = ∑ j, y j := by
      rw [Finset.sum_filter]
      congr 1
      ext j
      simp [all_le j]
    calc ∑ j with j ≤ i_max, x j - ∑ j with j ≤ i_max, y j
      = ∑ j, x j - ∑ j, y j := by rw [sum_x_total, sum_y_total]
      _ = 0 := by rw [hsum, sub_self]

  have split_boundary : ∑ i, ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) =
    ci i_max * (∑ j with j ≤ i_max, x j - ∑ j with j ≤ i_max, y j) +
    ∑ i ∈ (Finset.univ.erase i_max), ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) := by
    have h_eq : ∑ i, ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) =
      ∑ i ∈ Finset.univ, ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) := by simp
    rw [h_eq]
    have h_mem : i_max ∈ Finset.univ := Finset.mem_univ i_max
    rw [(@Finset.sum_erase_add (Fin m) ℝ _ _ Finset.univ (fun i => ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j)) i_max h_mem).symm]
    ring

  rw [split_boundary]

  have boundary_zero : ci i_max * (∑ j with j ≤ i_max, x j - ∑ j with j ≤ i_max, y j) = 0 := by
    rw [largest_index_zero, mul_zero]

  rw [boundary_zero, zero_add]

  have telescoping_rewrite : ∑ i ∈ (Finset.univ.erase i_max), ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) -
    ∑ i, ci i * (∑ j with j < i, x j - ∑ j with j < i, y j) ≤ 0 := by

    have maj_bound : ∀ k : Fin m, ∑ j with j ≤ k, x j - ∑ j with j ≤ k, y j ≤ 0 := by
      intro k
      simp only [Finset.sum_filter] at hmaj ⊢
      linarith [hmaj k]

    have diff_terms_nonpos : ∀ i : Fin m, ∀ hi : i.val + 1 < m,
      (ci i - ci ⟨i.val + 1, hi⟩) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) ≤ 0 := by
      intro i hi
      have : c_i_plus_1 i = ci ⟨i.val + 1, hi⟩ := by simp only [c_i_plus_1, ci, dif_pos hi]
      have slope_diff_nonneg : ci ⟨i.val + 1, hi⟩ ≤ ci i := by
        rw [← this]; exact ci_leq_ci_plus_1 i hi (hdist i) (hdist ⟨i.val + 1, hi⟩)
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg_of_le slope_diff_nonneg) (maj_bound i)

    have i_succ_lt_m : ∀ i ∈ Finset.univ.erase i_max, i.val + 1 < m := by
      intro i hi
      simp only [Finset.mem_erase, Finset.mem_univ] at hi
      by_contra h_not_lt
      simp only [not_lt] at h_not_lt
      have : i.val = m - 1 := by omega
      have h_eq : i = i_max := by ext; simp [i_max]; exact this
      exact hi.1 h_eq

    have telescoping_split : ∑ i ∈ (Finset.univ.erase i_max), ci i * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) =
      ∑ i ∈ (Finset.univ.erase i_max), (ci i - if h : i.val + 1 < m then ci ⟨i.val + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) +
      ∑ i ∈ (Finset.univ.erase i_max), (if h : i.val + 1 < m then ci ⟨i.val + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp [i_succ_lt_m i hi]
      ring

    rw [telescoping_split]

    have first_sum_nonpos : ∑ i ∈ (Finset.univ.erase i_max), (ci i - if h : i.val + 1 < m then ci ⟨i.val + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      simp only [dif_pos (i_succ_lt_m i hi)]
      exact diff_terms_nonpos i (i_succ_lt_m i hi)

    have h_combine : ∑ i ∈ Finset.univ.erase i_max,
          (ci i - if h : ↑i + 1 < m then ci ⟨↑i + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) +
        ∑ i ∈ Finset.univ.erase i_max,
          (if h : ↑i + 1 < m then ci ⟨↑i + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) -
      ∑ i, ci i * (∑ j with j < i, x j - ∑ j with j < i, y j) ≤ 0 := by
      let i_zero : Fin m := ⟨0, hm⟩
      have h_zero_term : ci i_zero * (∑ j with j < i_zero, x j - ∑ j with j < i_zero, y j) = 0 := by
        have h_empty : ∑ j with j < i_zero, x j - ∑ j with j < i_zero, y j = 0 := by
          simp only [Finset.sum_filter]
          have h_empty_filter : (∑ a, if a < i_zero then x a else 0) = 0 ∧ (∑ a, if a < i_zero then y a else 0) = 0 := by
            constructor <;> {
              apply Finset.sum_eq_zero
              intro j _
              simp only [ite_eq_right_iff]
              intro h_lt
              exfalso
              simp only [i_zero, Fin.lt_def] at h_lt
              exact Nat.not_lt_zero j.val h_lt
            }
          rw [h_empty_filter.1, h_empty_filter.2, sub_zero]
        rw [h_empty, mul_zero]

      have h3 : ∑ i ∈ Finset.univ.erase i_max,
          (if h : ↑i + 1 < m then ci ⟨↑i + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) -
        ∑ i, ci i * (∑ j with j < i, x j - ∑ j with j < i, y j) = 0 := by

        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i_zero), h_zero_term, add_zero]

        have h_reindex : ∑ i ∈ Finset.univ.erase i_max,
            (if h : ↑i + 1 < m then ci ⟨↑i + 1, h⟩ else 0) * (∑ j with j ≤ i, x j - ∑ j with j ≤ i, y j) =
          ∑ i ∈ Finset.univ.erase i_zero, ci i * (∑ j with j < i, x j - ∑ j with j < i, y j) := by

          refine Finset.sum_bij (fun i hi => ⟨↑i + 1, i_succ_lt_m i hi⟩) ?_ ?_ ?_ ?_

          · intro i hi
            simp only [Finset.mem_erase, Finset.mem_univ]
            constructor
            · intro h_eq
              simp [i_zero] at h_eq
            · trivial

          · intro i₁ i₂ hi₁ hi₂ h_eq
            ext
            simp at h_eq
            omega

          · intro j hj
            simp only [Finset.mem_erase, Finset.mem_univ] at hj
            have hj_pos : 0 < j.val := by
              by_contra h_not
              simp only [not_lt, Nat.le_zero] at h_not
              have : j = i_zero := by ext; simp [i_zero]; exact h_not
              exact hj.1 this
            use ⟨j.val - 1, by omega⟩
            refine ⟨?_, ?_⟩
            · simp only [Finset.mem_erase, Finset.mem_univ]
              constructor
              · intro h_eq
                have : j.val - 1 = m - 1 := by simp [i_max] at h_eq; exact h_eq
                have : j.val = m := by omega
                omega
              · trivial
            · ext
              simp
              omega

          · intro i hi
            simp only [dif_pos (i_succ_lt_m i hi)]
            congr 1
            have h_sum_eq : (∑ j with j ≤ i, x j) = (∑ j with j < (⟨↑i + 1, i_succ_lt_m i hi⟩ : Fin m), x j) := by
              refine Finset.sum_congr ?_ (fun _ _ => rfl)
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Nat.le_iff_lt_add_one
            have h_sum_eq' : (∑ j with j ≤ i, y j) = (∑ j with j < (⟨↑i + 1, i_succ_lt_m i hi⟩ : Fin m), y j) := by
              refine Finset.sum_congr ?_ (fun _ _ => rfl)
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Nat.le_iff_lt_add_one
            rw [h_sum_eq, h_sum_eq']

        rw [h_reindex]
        simp

      linarith [first_sum_nonpos, h3]

    exact h_combine

  exact telescoping_rewrite




theorem schur_convex_xlogx {n : ℕ} :
  SchurConvex (fun x : Fin n → ℝ => ∑ i, x i * Real.log (x i)) := by
  unfold SchurConvex
  intro x y hx_nonneg hy_nonneg h
  obtain ⟨h_majorization, h_sum_eq⟩ := h

  let x_dual : Fin n → OrderDual ℝ := fun i => OrderDual.toDual (x i)
  let y_dual : Fin n → OrderDual ℝ := fun i => OrderDual.toDual (y i)
  let σ := Tuple.sort x_dual
  let τ := Tuple.sort y_dual
  let x_sorted := fun i => x (σ i)
  let y_sorted := fun i => y (τ i)

  have x_sorted_decreasing : ∀ i j : Fin n, i ≤ j → x_sorted j ≤ x_sorted i := by
    intros i j hij
    simp only [x_sorted, ← Function.comp_apply]
    exact Tuple.monotone_sort x_dual hij

  have y_sorted_decreasing : ∀ i j : Fin n, i ≤ j → y_sorted j ≤ y_sorted i := by
    intros i j hij
    simp only [y_sorted, ← Function.comp_apply]
    exact Tuple.monotone_sort y_dual hij

  have x_sum_eq : ∑ i, x i = ∑ i, x_sorted i := by
    simp only [x_sorted]
    rw [← Equiv.sum_comp σ x]

  have y_sum_eq : ∑ i, y i = ∑ i, y_sorted i := by
    simp only [y_sorted]
    rw [← Equiv.sum_comp τ y]

  have xlogx_sum_eq : ∑ i, x i * Real.log (x i) = ∑ i, x_sorted i * Real.log (x_sorted i) := by
    simp only [x_sorted]
    rw [← Equiv.sum_comp σ (fun i => x i * Real.log (x i))]

  have ylogx_sum_eq : ∑ i, y i * Real.log (y i) = ∑ i, y_sorted i * Real.log (y_sorted i) := by
    simp only [y_sorted]
    rw [← Equiv.sum_comp τ (fun i => y i * Real.log (y i))]

  let equal_indices := Finset.univ.filter (fun i => x_sorted i = y_sorted i)
  let distinct_indices_set := Finset.univ.filter (fun i => x_sorted i ≠ y_sorted i)

  have disjoint_partition : equal_indices ∪ distinct_indices_set = Finset.univ ∧
                           Disjoint equal_indices distinct_indices_set := by
    constructor
    · ext i
      simp [equal_indices, distinct_indices_set]
      by_cases h : x_sorted i = y_sorted i <;> simp [h]
    ·       simp [equal_indices, distinct_indices_set, Finset.disjoint_filter]

  by_cases h_case : distinct_indices_set = ∅
  · have all_equal : ∀ i, x_sorted i = y_sorted i := by
      intro i
      by_contra h_neq
      have : i ∈ distinct_indices_set := by simp [distinct_indices_set, h_neq]
      rw [h_case] at this; exact Finset.notMem_empty i this
    have x_eq_y : x_sorted = y_sorted := by ext i; exact all_equal i
    change ∑ i, x i * Real.log (x i) ≤ ∑ i, y i * Real.log (y i)
    rw [xlogx_sum_eq, ylogx_sum_eq, x_eq_y]
  · have sum_split : ∀ f : Fin n → ℝ, ∑ i, f i =
      ∑ i ∈ equal_indices, f i + ∑ i ∈ distinct_indices_set, f i := by
      intro f
      rw [← Finset.sum_union disjoint_partition.2, disjoint_partition.1]

    change ∑ i, x i * Real.log (x i) ≤ ∑ i, y i * Real.log (y i)
    rw [xlogx_sum_eq, ylogx_sum_eq]
    rw [sum_split (fun i => x_sorted i * Real.log (x_sorted i)), sum_split (fun i => y_sorted i * Real.log (y_sorted i))]

    have equal_terms_cancel : ∑ i ∈ equal_indices, x_sorted i * Real.log (x_sorted i) =
                             ∑ i ∈ equal_indices, y_sorted i * Real.log (y_sorted i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [equal_indices] at hi
      rw [hi]

    rw [equal_terms_cancel]
    apply add_le_add_left

    have distinct_sums_eq : ∑ i ∈ distinct_indices_set, x_sorted i = ∑ i ∈ distinct_indices_set, y_sorted i := by
      have global_eq : ∑ i, x_sorted i = ∑ i, y_sorted i := by rw [← x_sum_eq, ← y_sum_eq, h_sum_eq]
      have : ∑ i, x_sorted i = ∑ i ∈ equal_indices, x_sorted i + ∑ i ∈ distinct_indices_set, x_sorted i := by
        rw [← Finset.sum_union disjoint_partition.2, disjoint_partition.1]
      rw [this] at global_eq; clear this
      have : ∑ i, y_sorted i = ∑ i ∈ equal_indices, y_sorted i + ∑ i ∈ distinct_indices_set, y_sorted i := by
        rw [← Finset.sum_union disjoint_partition.2, disjoint_partition.1]
      rw [this] at global_eq; clear this
      have equal_parts_eq : ∑ i ∈ equal_indices, x_sorted i = ∑ i ∈ equal_indices, y_sorted i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        simp [equal_indices] at hi; exact hi
      linarith

    let m := distinct_indices_set.card

    by_cases h_empty : m = 0
    · exfalso
      rw [Finset.card_eq_zero] at h_empty
      exact h_case h_empty

    · have hm_pos : 0 < m := Nat.pos_of_ne_zero h_empty
      have hdist_restricted : ∀ i : Fin n, i ∈ distinct_indices_set → x_sorted i ≠ y_sorted i := by
        intros i hi
        simp [distinct_indices_set] at hi
        exact hi

      let distinct_sorted := distinct_indices_set.sort (· ≤ ·)
      let x_restricted : Fin m → ℝ := fun i =>
        x_sorted (distinct_sorted.get ⟨i.val, by
          rw [Finset.length_sort]
          exact i.isLt⟩)
      let y_restricted : Fin m → ℝ := fun i =>
        y_sorted (distinct_sorted.get ⟨i.val, by
          rw [Finset.length_sort]
          exact i.isLt⟩)

      have hx_dec : ∀ i j : Fin m, i ≤ j → x_restricted j ≤ x_restricted i := by
        intros i j hij
        simp only [x_restricted]
        apply x_sorted_decreasing
        apply List.Sorted.rel_get_of_le (Finset.sort_sorted (· ≤ ·) distinct_indices_set) hij

      have hy_dec : ∀ i j : Fin m, i ≤ j → y_restricted j ≤ y_restricted i := by
        intros i j hij
        simp only [y_restricted]
        apply y_sorted_decreasing
        apply List.Sorted.rel_get_of_le (Finset.sort_sorted (· ≤ ·) distinct_indices_set) hij

      have hdist : ∀ i : Fin m, x_restricted i ≠ y_restricted i := by
        intro i
        simp only [x_restricted, y_restricted]
        apply hdist_restricted
        have h_mem := List.get_mem distinct_sorted ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩
        rwa [Finset.mem_sort] at h_mem

      have h_length : (Finset.sort (· ≤ ·) distinct_indices_set).length = m := by
        rw [Finset.length_sort]

      have h_bijection : ∀ f : Fin n → ℝ,
      ∑ i : Fin m, f (distinct_sorted.get ⟨i.val, by rw [Finset.length_sort]; exact i.isLt⟩) = ∑ j ∈ distinct_indices_set, f j := by
        intro f
        simp only [distinct_sorted]
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_bij (fun i _ => distinct_sorted.get ⟨i, by rw [h_length]; exact Finset.mem_range.mp (by assumption)⟩)
        · intro i hi
          have h_get_mem := List.get_mem distinct_sorted ⟨i, by rw [h_length]; exact Finset.mem_range.mp hi⟩
          rwa [Finset.mem_sort] at h_get_mem
        · intro i hi j hj h_eq
          have h_inj := List.nodup_iff_injective_get.mp (Finset.sort_nodup (· ≤ ·) distinct_indices_set)
          have h_i_bound : i < distinct_sorted.length := by rw [h_length]; exact Finset.mem_range.mp hi
          have h_j_bound : j < distinct_sorted.length := by rw [h_length]; exact Finset.mem_range.mp hj
          simp at h_eq ⊢
          exact congrArg Fin.val (h_inj h_eq)
        · intro j hj
          have h_in_list : j ∈ distinct_sorted := by rwa [Finset.mem_sort]
          obtain ⟨k, hk⟩ := List.mem_iff_get.mp h_in_list
          refine ⟨k.val, Finset.mem_range.mpr (h_length ▸ k.isLt), ?_⟩
          exact hk
        · intro a ha
          simp only [dif_pos (Finset.mem_range.mp ha)]
          congr


      have hmaj : ∀ k : Fin m, ∑ i with i ≤ k, x_restricted i ≤ ∑ i with i ≤ k, y_restricted i := by
        intro k
        simp only [x_restricted, y_restricted]
        let j := distinct_sorted.get ⟨k.val, by rw [Finset.length_sort]; exact k.isLt⟩
        have h_mem : j ∈ distinct_indices_set := by
          have h := List.get_mem distinct_sorted ⟨k.val, by rw [Finset.length_sort]; exact k.isLt⟩
          rwa [Finset.mem_sort] at h

        have h_j_def : j = distinct_sorted.get ⟨k.val, by rw [h_length]; exact k.isLt⟩ := rfl

        have h_sorted_prop : ∀ i : Fin m, i ≤ k → distinct_sorted.get ⟨i.val, by rw [h_length]; exact i.isLt⟩ ≤ j := by
          intro i hi
          rw [h_j_def]
          apply List.Sorted.rel_get_of_le (Finset.sort_sorted (· ≤ ·) distinct_indices_set)
          convert hi

        have h_partial_sum : ∀ f : Fin n → ℝ, ∑ x with x ≤ k, f (distinct_sorted.get ⟨↑x, by rw [h_length]; exact x.isLt⟩) =
          ∑ i ∈ distinct_indices_set.filter (· ≤ j), f i := by
          intro f
          apply Finset.sum_bij (fun a ha => distinct_sorted.get ⟨a.val, by rw [h_length]; exact a.isLt⟩)
          · intro a ha
            simp only [Finset.mem_filter]
            constructor
            · have h_get_mem := List.get_mem distinct_sorted ⟨a.val, by rw [h_length]; exact a.isLt⟩
              rwa [Finset.mem_sort] at h_get_mem
            · have h_a_le_k : a ≤ k := (Finset.mem_filter.mp ha).2
              exact h_sorted_prop a h_a_le_k
          · intro a₁ ha₁ a₂ ha₂ h_eq
            have h_inj := List.nodup_iff_injective_get.mp (Finset.sort_nodup (· ≤ ·) distinct_indices_set)
            have : (⟨a₁.val, by rw [h_length]; exact a₁.isLt⟩ : Fin distinct_sorted.length) =
                   ⟨a₂.val, by rw [h_length]; exact a₂.isLt⟩ := h_inj h_eq
            simp at this
            exact Fin.ext this
          · intro b hb
            have h_b_mem : b ∈ distinct_indices_set := (Finset.mem_filter.mp hb).1
            have h_in_list : b ∈ distinct_sorted := by
              rw [Finset.mem_sort]
              exact h_b_mem
            obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_in_list
            use ⟨i.val, by rw [← h_length]; exact i.isLt⟩
            constructor
            · simp; exact hi
            · have h_b_le_j : b ≤ j := (Finset.mem_filter.mp hb).2
              have h_sorted := Finset.sort_sorted (· ≤ ·) distinct_indices_set
              have h_k_bound : k.val < distinct_sorted.length := by
                rw [h_length]; exact k.isLt
              have h_get_le : distinct_sorted.get i ≤ distinct_sorted.get ⟨k.val, h_k_bound⟩ := by
                rw [hi]
                have h_eq_get : distinct_sorted.get ⟨k.val, h_k_bound⟩ = j := by
                  rw [← h_j_def]
                rw [h_eq_get]
                exact h_b_le_j
              have h_i_le_k : i.val ≤ k.val := by
                by_contra h_not_le
                push_neg at h_not_le
                have h_sorted_contra : distinct_sorted.get ⟨k.val, h_k_bound⟩ ≤ distinct_sorted.get i :=
                  List.Sorted.rel_get_of_le h_sorted (Nat.le_of_lt h_not_le)
                have h_eq := le_antisymm h_get_le h_sorted_contra
                have h_ne : i ≠ ⟨k.val, h_k_bound⟩ := fun h => Nat.lt_irrefl k.val (congrArg Fin.val h ▸ h_not_le)
                exact h_ne ((List.nodup_iff_injective_get.mp (Finset.sort_nodup _ _)) h_eq)
              simp
              exact Fin.mk_le_of_le_val h_i_le_k
          · intro a ha
            rfl

        rw [h_partial_sum x_sorted, h_partial_sum y_sorted]

        have h_full_sum : ∀ f : Fin n → ℝ, ∑ i with i ≤ j, f i =
          ∑ i ∈ distinct_indices_set.filter (· ≤ j), f i + ∑ i ∈ equal_indices.filter (· ≤ j), f i := by
          intro f
          simp only [Finset.sum_filter]
          rw [show (∑ a, if a ≤ j then f a else 0) = ∑ a ∈ (equal_indices ∪ distinct_indices_set), if a ≤ j then f a else 0 from by rw [disjoint_partition.1]]
          rw [Finset.sum_union disjoint_partition.2]
          ring

        have h_equal_terms : ∑ i ∈ equal_indices.filter (· ≤ j), x_sorted i = ∑ i ∈ equal_indices.filter (· ≤ j), y_sorted i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp [equal_indices] at hi; exact hi.1

        have h_maj : ∑ i with i ≤ j, x_sorted i ≤ ∑ i with i ≤ j, y_sorted i := h_majorization j

        rw [h_full_sum x_sorted, h_full_sum y_sorted, h_equal_terms] at h_maj
        exact le_of_add_le_add_right h_maj


      have hsum : ∑ i, x_restricted i = ∑ i, y_restricted i := by
        simp only [x_restricted, y_restricted]
        rw [h_bijection x_sorted, h_bijection y_sorted]
        exact distinct_sums_eq

      have hx_restricted_nonneg : ∀ i : Fin m, 0 ≤ x_restricted i := by
        intro i
        simp only [x_restricted, x_sorted]
        exact hx_nonneg (σ (distinct_sorted.get ⟨↑i, _⟩))

      have hy_restricted_nonneg : ∀ i : Fin m, 0 ≤ y_restricted i := by
        intro i
        simp only [y_restricted, y_sorted]
        exact hy_nonneg (τ (distinct_sorted.get ⟨↑i, _⟩))

      have main_ineq : ∑ i, x_restricted i * Real.log (x_restricted i) ≤ ∑ i, y_restricted i * Real.log (y_restricted i) :=
        schur_convex_reduction_to_distinct hm_pos x_restricted y_restricted
          hx_restricted_nonneg hy_restricted_nonneg hx_dec hy_dec hdist hmaj hsum

      have convert_x : ∑ i, x_restricted i * Real.log (x_restricted i) =
                       ∑ i ∈ distinct_indices_set, x_sorted i * Real.log (x_sorted i) := by
        simp only [x_restricted]
        exact h_bijection (fun j => x_sorted j * Real.log (x_sorted j))

      have convert_y : ∑ i, y_restricted i * Real.log (y_restricted i) =
                       ∑ i ∈ distinct_indices_set, y_sorted i * Real.log (y_sorted i) := by
        simp only [y_restricted]
        exact h_bijection (fun j => y_sorted j * Real.log (y_sorted j))

      rw [← convert_x, ← convert_y]
      exact main_ineq





lemma eigenvalue_bound_eigenbasis
{R : ℕ}
(C : ℝ)
(ρ : Matrix (Fin R) (Fin R) ℂ)
(hρ : ρ.IsHermitian)
(h : ∃ v : EuclideanSpace ℂ (Fin R), ‖v‖ = 1 ∧ (⟪v, ρ *ᵥ v⟫_ℂ).re > C)
:
∃ i : Fin R, hρ.eigenvalues i > C := by
  obtain ⟨v, hv_norm, hv_bound⟩ := h

  let α : Fin R → ℂ := hρ.eigenvectorBasis.repr v

  have v_eigenbasis : v = ∑ i : Fin R, α i • (hρ.eigenvectorBasis i) :=
    (OrthonormalBasis.sum_repr hρ.eigenvectorBasis v).symm

  have orthonormal_eq : ∀ i j : Fin R, ⟪hρ.eigenvectorBasis i, hρ.eigenvectorBasis j⟫_ℂ = if i = j then 1 else 0 := by
    have h_ortho : Orthonormal ℂ hρ.eigenvectorBasis := hρ.eigenvectorBasis.orthonormal
    rwa [orthonormal_iff_ite] at h_ortho

  have norm_constraint : ∑ i : Fin R, ‖α i‖^2 = 1 := by
    have h : ‖v‖^2 = ∑ i : Fin R, ‖α i‖^2 := by
      rw [pow_two, ← @inner_self_eq_norm_mul_norm ℂ, v_eigenbasis]
      simp_rw [inner_sum, sum_inner, inner_smul_left, inner_smul_right, orthonormal_eq]
      simp only [mul_ite, mul_one, mul_zero]
      have key : RCLike.re (∑ x, ∑ x_1, if x_1 = x then (starRingEnd ℂ) (α x_1) * α x else 0) = ∑ i, RCLike.re ((starRingEnd ℂ) (α i) * α i) := by
        simp only [map_sum]
        rw [← map_sum]
        simp only [map_sum]
        congr 1
        ext x
        simp only [apply_ite, map_zero]
        simp
      rw [key]
      congr 1
      ext i
      simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp
      norm_cast
    rw [← h, hv_norm]
    norm_num

  have linearity : ρ *ᵥ ∑ x, α x • hρ.eigenvectorBasis x = ∑ x, α x • (ρ *ᵥ hρ.eigenvectorBasis x) := by
    have h1 : ρ *ᵥ ∑ x, α x • hρ.eigenvectorBasis x = Matrix.mulVecLin ρ (∑ x, α x • hρ.eigenvectorBasis x) := rfl
    have h2 : Matrix.mulVecLin ρ (∑ x, α x • hρ.eigenvectorBasis x) = ∑ x, Matrix.mulVecLin ρ (α x • hρ.eigenvectorBasis x) :=
      map_sum (Matrix.mulVecLin ρ) _ _
    have h3 : ∑ x, Matrix.mulVecLin ρ (α x • hρ.eigenvectorBasis x) = ∑ x, α x • (ρ *ᵥ hρ.eigenvectorBasis x) := by
      simp only [LinearMap.map_smul, Matrix.mulVecLin_apply]
    rw [h1, h2, h3]


  have eigenvalue_equation : ∀ i : Fin R, ρ *ᵥ hρ.eigenvectorBasis i = hρ.eigenvalues i • hρ.eigenvectorBasis i := by
    intro i
    exact hρ.mulVec_eigenvectorBasis i

  have spectral : ⟪∑ i, α i • hρ.eigenvectorBasis i, ρ *ᵥ (∑ j, α j • hρ.eigenvectorBasis j)⟫_ℂ = ∑ i, hρ.eigenvalues i * ‖α i‖ ^ 2 := by
    rw [linearity]
    simp_rw [eigenvalue_equation]
    simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
    simp_rw [← Complex.coe_smul]
    simp only [inner_smul_right]
    simp_rw [orthonormal_eq]
    simp only [mul_ite, mul_one, mul_zero]
    simp
    congr
    ext i
    ring_nf
    rw [mul_comm (α i), ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
    ring

  have quadratic_form : (⟪v, ρ *ᵥ v⟫_ℂ).re = ∑ i : Fin R, hρ.eigenvalues i * ‖α i‖^2 := by
    have expand_both : ⟪v, ρ *ᵥ v⟫_ℂ = ⟪∑ i, α i • hρ.eigenvectorBasis i, ρ *ᵥ (∑ j, α j • hρ.eigenvectorBasis j)⟫_ℂ := by
      rw [v_eigenbasis]
    rw [expand_both, spectral]
    simp
    norm_cast

  rw [quadratic_form] at hv_bound
  by_contra h_all_small
  push_neg at h_all_small
  have bound_contradiction : ∑ i, hρ.eigenvalues i * ‖α i‖ ^ 2 ≤ C := by
    calc ∑ i, hρ.eigenvalues i * ‖α i‖ ^ 2
      _ ≤ ∑ i, C * ‖α i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_right (h_all_small i) (sq_nonneg _)
      _ = C * ∑ i, ‖α i‖ ^ 2 := by rw [← Finset.mul_sum]
      _ = C * 1 := by rw [norm_constraint]
      _ = C := by ring
  linarith [hv_bound, bound_contradiction]



/-- **High Fidelity Implies Low Entropy**

For a positive semidefinite density matrix ρ of order R > 1 with trace 1,
if there exists a unit vector achieving fidelity greater than 1 - δ,
then the von Neumann entropy is bounded above by the entropy of a specific
comparison distribution.

## Statement

Let ρ be an R×R positive semidefinite matrix (density matrix) with trace 1.
If there exists a unit vector v such that Re⟨v, ρv⟩ > 1 - δ, then:

  S(ρ) ≤ -(1-δ)log(1-δ) - δ log(δ/(R-1))

where S(ρ) = -tr(ρ log ρ) is the von Neumann entropy.

## Physical Interpretation

This result shows that high fidelity (low δ) with a pure state implies
low entropy, quantifying the "purity" of the quantum state.
-/
theorem high_fidelity_implies_low_entropy_equivalent
    (R : ℕ)
    (δ : ℝ)
    (ρ : Matrix (Fin R) (Fin R) ℂ)
    (hR : 1 < R)
    (hδ_pos : 0 ≤ δ)
    (hδ_lt_one : δ < 1)
    (hδ_small : δ ≤ (R - 1 : ℝ) / R)
    (hρ_pos : ρ.PosSemidef)
    (trace_one : ∑ i, hρ_pos.isHermitian.eigenvalues i = 1)
    (hv : ∃ v : EuclideanSpace ℂ (Fin R), norm v = 1 ∧ (⟪v, ρ *ᵥ v⟫_ℂ).re > 1 - δ)
    :
    (vonNeumannEntropy ρ).re ≤ -(1 - δ) * Real.log (1 - δ) - δ * Real.log (δ / (R - 1)) := by
  -- Extract Hermitian property from positive semidefiniteness
  have hρ : ρ.IsHermitian := hρ_pos.isHermitian

  -- Step 1: Existence of large eigenvalue
  -- High fidelity implies at least one eigenvalue exceeds 1 - δ
  have large_eigenvalue : ∃ i : Fin R, hρ.eigenvalues i > 1 - δ := by
    apply eigenvalue_bound_eigenbasis (1 - δ) ρ hρ
    exact hv
  obtain ⟨i₀, hi₀⟩ := large_eigenvalue

  -- Step 2: Non-negativity of eigenvalues
  -- Positive semidefinite matrices have non-negative eigenvalues
  have eigenvalues_nonneg : ∀ i : Fin R, 0 ≤ hρ.eigenvalues i := by
    intro i
    classical
    exact hρ_pos.eigenvalues_nonneg i

  -- Step 3: Construct comparison eigenvalue distribution
  -- Define eig_comp with one large eigenvalue (1-δ) and R-1 small equal eigenvalues
  have hR_pos : 0 < R := by omega
  let eig_comp : Fin R → ℝ := fun i => if i = ⟨0, hR_pos⟩ then (1 - δ) else (δ / (R - 1) : ℝ)

  -- Step 4: Verify comparison distribution is normalized
  -- Computation: (1 - δ) + (R-1) · δ/(R-1) = (1 - δ) + δ = 1
  have eig_comp_sum : ∑ i, eig_comp i = 1 := by
    simp only [eig_comp]
    let i₀ : Fin R := ⟨0, hR_pos⟩
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
    have h_if : (if i₀ = ⟨0, hR_pos⟩ then 1 - δ else δ / (R - 1)) = (1 - δ) := by rfl
    rw [h_if]
    have h_erase : ∑ x ∈ Finset.univ.erase i₀, (if x = ⟨0, hR_pos⟩ then 1 - δ else δ / (R - 1)) = (R - 1) * (δ / (R - 1)) := by
      trans ∑ x ∈ Finset.univ.erase i₀, δ / (R - 1)
      · apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_erase] at hx
        rw [if_neg hx.1]
      · rw [Finset.sum_const]
        simp [Finset.card_erase_of_mem, nsmul_eq_mul]
        left
        rw [Nat.cast_sub (by omega : 1 ≤ R)]
        norm_num
    rw [h_erase]
    have h_nz : (R - 1 : ℝ) ≠ 0 := by
      have : (1 : ℝ) < (R : ℝ) := by norm_cast;
      linarith
    field_simp [h_nz]
    ring

  -- Step 5: Establish majorization relation eig_comp ≺ hρ.eigenvalues
  -- This is the key step: we show the comparison distribution is majorized by
  -- the actual eigenvalue distribution, which allows us to apply Schur-convexity
  have majorization :
    (let eig_dual : Fin R → OrderDual ℝ := fun i => OrderDual.toDual (eig_comp i)
     let eigen_dual : Fin R → OrderDual ℝ := fun i => OrderDual.toDual (hρ.eigenvalues i)
     let σ := Tuple.sort eig_dual
     let τ := Tuple.sort eigen_dual
     (∀ k : Fin R, ∑ i ∈ (Finset.univ.filter (· ≤ k)), eig_comp (σ i) ≤
                   ∑ i ∈ (Finset.univ.filter (· ≤ k)), hρ.eigenvalues (τ i)) ∧
     (∑ i, eig_comp i = ∑ i, hρ.eigenvalues i)) := by
    constructor
    · intro k
      -- Part (a): Verify partial sum inequalities
      let eig_dual : Fin R → OrderDual ℝ := fun i => OrderDual.toDual (eig_comp i)
      let σ := Tuple.sort eig_dual

      -- The largest element of eig_comp is 1-δ
      have eig_comp_max : ∃ i, eig_comp i = 1 - δ := by
        use ⟨0, hR_pos⟩
        simp [eig_comp]

      -- After sorting, the first element is the largest
      have σ_0_is_max : eig_comp (σ ⟨0, hR_pos⟩) = 1 - δ := by
        -- First, show 1-δ is the maximum value in eig_comp
        have is_max : ∀ i, eig_comp i ≤ 1 - δ := by
          intro i
          simp only [eig_comp]
          split_ifs with h
          · exact le_refl _
          · -- Need to show: δ / (R - 1) ≤ 1 - δ
            have h1 : (1 : ℝ) < R := by norm_cast;
            have h2 : (0 : ℝ) < R - 1 := by linarith
            have h3 : δ * R ≤ R - 1 := by
              calc δ * R ≤ ((R - 1) / R) * R := by
                    apply mul_le_mul_of_nonneg_right hδ_small
                    linarith
                _ = R - 1 := by field_simp [ne_of_gt h1]
            have : δ ≤ (R - 1) * (1 - δ) := by
              rw [mul_sub, mul_one]
              linarith [h3]
            calc δ / (R - 1) = δ * (1 / (R - 1)) := by rw [div_eq_mul_inv, inv_eq_one_div]
              _ ≤ ((R - 1) * (1 - δ)) * (1 / (R - 1)) := by
                    apply mul_le_mul_of_nonneg_right this
                    exact div_nonneg (by linarith : (0 : ℝ) ≤ 1) (le_of_lt h2)
              _ = (R - 1) * (1 - δ) / (R - 1) := by ring
              _ = 1 - δ := by field_simp [ne_of_gt h2]

        -- Sorting by OrderDual puts maximum first
        have h_sorted : ∀ i : Fin R, OrderDual.toDual (eig_comp (σ ⟨0, hR_pos⟩)) ≤
                                       OrderDual.toDual (eig_comp (σ i)) := by
          intro i
          have : (⟨0, hR_pos⟩ : Fin R) ≤ i := Nat.zero_le i.val
          exact Tuple.monotone_sort eig_dual this
        -- This means eig_comp (σ i) ≤ eig_comp (σ ⟨0, hR_pos⟩) for all i
        have h_max_after_sort : ∀ i, eig_comp (σ i) ≤ eig_comp (σ ⟨0, hR_pos⟩) := by
          intro i
          have := h_sorted i
          simp only [OrderDual.toDual_le_toDual] at this
          exact this
        -- Since σ is a bijection, this means eig_comp (σ ⟨0, hR_pos⟩) is the maximum
        have h_is_max : ∀ j, eig_comp j ≤ eig_comp (σ ⟨0, hR_pos⟩) := by
          intro j
          have : ∃ i, σ i = j := Equiv.surjective σ j
          obtain ⟨i, hi⟩ := this
          rw [← hi]
          exact h_max_after_sort i
        -- But we know the maximum is 1 - δ
        obtain ⟨i₀, hi₀⟩ := eig_comp_max
        have h_upper : eig_comp (σ ⟨0, hR_pos⟩) ≤ 1 - δ := is_max (σ ⟨0, hR_pos⟩)
        have h_lower : 1 - δ ≤ eig_comp (σ ⟨0, hR_pos⟩) := by
          rw [← hi₀]
          exact h_is_max i₀
        exact le_antisymm h_upper h_lower

      -- Characterize sorted eigenvalues
      let eigen_dual : Fin R → OrderDual ℝ := fun i => OrderDual.toDual (hρ.eigenvalues i)
      let τ := Tuple.sort eigen_dual

      -- The largest eigenvalue is > 1-δ (from hi₀)
      have eigen_max_bound : hρ.eigenvalues (τ ⟨0, hR_pos⟩) ≥ 1 - δ := by
        have h_sorted : ∀ i : Fin R, OrderDual.toDual (hρ.eigenvalues (τ ⟨0, hR_pos⟩)) ≤
                                       OrderDual.toDual (hρ.eigenvalues (τ i)) := by
          intro i
          have : (⟨0, hR_pos⟩ : Fin R) ≤ i := Nat.zero_le i.val
          exact Tuple.monotone_sort eigen_dual this
        have h_max_after_sort : ∀ i, hρ.eigenvalues (τ i) ≤ hρ.eigenvalues (τ ⟨0, hR_pos⟩) := by
          intro i
          have := h_sorted i
          simp only [OrderDual.toDual_le_toDual] at this
          exact this
        have h_is_max : ∀ j, hρ.eigenvalues j ≤ hρ.eigenvalues (τ ⟨0, hR_pos⟩) := by
          intro j
          have : ∃ i, τ i = j := Equiv.surjective τ j
          obtain ⟨i, hi⟩ := this
          rw [← hi]
          exact h_max_after_sort i
        calc hρ.eigenvalues (τ ⟨0, hR_pos⟩) ≥ hρ.eigenvalues i₀ := h_is_max i₀
          _ ≥ 1 - δ := le_of_lt hi₀

      -- Case k=0
      by_cases h_k_zero : k = ⟨0, hR_pos⟩
      · rw [h_k_zero]
        have : Finset.univ.filter (· ≤ (⟨0, hR_pos⟩ : Fin R)) = {(⟨0, hR_pos⟩ : Fin R)} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro h
            have : i.val ≤ 0 := h
            have : i.val = 0 := Nat.eq_zero_of_le_zero this
            ext
            exact this
          · intro h
            rw [h]
        rw [this]
        simp only [Finset.sum_singleton]
        calc eig_comp (σ ⟨0, hR_pos⟩) = 1 - δ := σ_0_is_max
          _ ≤ hρ.eigenvalues (τ ⟨0, hR_pos⟩) := eigen_max_bound

      -- Case k>0
      · have h_k_pos : 0 < k.val := by
          by_contra h_not
          push_neg at h_not
          have : k.val = 0 := Nat.eq_zero_of_le_zero h_not
          have : k = ⟨0, hR_pos⟩ := by ext; exact this
          exact h_k_zero this

        -- Assume for contradiction that the inequality fails at k
        by_contra h_not
        push_neg at h_not

        -- Show eig_comp(σ k) > eigenvalues(τ k)
        have h_k_strict : eig_comp (σ k) > hρ.eigenvalues (τ k) := by
          by_contra h_not_strict
          push_neg at h_not_strict
          have h_eig_comp_tail : ∀ j : Fin R, 0 < j.val → eig_comp (σ j) = δ / (R - 1) := by
            intro j hj_pos
            by_cases h_distinct : 1 - δ > δ / (R - 1)
            · have h_sorted : eig_comp (σ j) ≤ eig_comp (σ ⟨0, hR_pos⟩) := by
                have : (⟨0, hR_pos⟩ : Fin R) ≤ j := Nat.zero_le j.val
                have h : OrderDual.toDual (eig_comp (σ ⟨0, hR_pos⟩)) ≤ OrderDual.toDual (eig_comp (σ j)) :=
                  Tuple.monotone_sort eig_dual this
                simp only [OrderDual.toDual_le_toDual] at h
                exact h
              rw [σ_0_is_max] at h_sorted
              simp only [eig_comp] at h_sorted ⊢
              split_ifs with h_if
              · exfalso
                have h_sigma_zero_eq : eig_comp (σ ⟨0, hR_pos⟩) = 1 - δ := σ_0_is_max
                simp only [eig_comp] at h_sigma_zero_eq
                split_ifs at h_sigma_zero_eq with h_sigma_zero
                · have : σ j = σ ⟨0, hR_pos⟩ := by rw [h_sigma_zero, h_if]
                  have : j = ⟨0, hR_pos⟩ := σ.injective this
                  have : j.val = 0 := by simp [this]
                  omega
                · linarith [h_distinct, h_sigma_zero_eq]
              · rfl
            · push_neg at h_distinct
              have h_equal : 1 - δ = δ / (R - 1) := by
                have h_upper : δ / (R - 1) ≤ 1 - δ := by
                  have h1 : (1 : ℝ) < R := by norm_cast
                  have h2 : (0 : ℝ) < R - 1 := by linarith
                  have h3 : δ * R ≤ R - 1 := by
                    calc δ * R ≤ ((R - 1) / R) * R := by
                          apply mul_le_mul_of_nonneg_right hδ_small
                          linarith
                      _ = R - 1 := by field_simp [ne_of_gt h1]
                  have : δ ≤ (R - 1) * (1 - δ) := by linarith
                  calc δ / (R - 1) ≤ (R - 1) * (1 - δ) / (R - 1) := by
                        apply div_le_div_of_nonneg_right this (le_of_lt h2)
                    _ = 1 - δ := by field_simp [ne_of_gt h2]
                exact le_antisymm h_distinct h_upper
              simp only [eig_comp]
              split_ifs
              · exact h_equal
              · rfl
          have h_eigen_sorted : ∀ j : Fin R, 0 < j.val → j ≤ k → hρ.eigenvalues (τ k) ≤ hρ.eigenvalues (τ j) := by
            intro j hj_pos hj_le
            have : j ≤ k := hj_le
            have h_sorted : OrderDual.toDual (hρ.eigenvalues (τ j)) ≤ OrderDual.toDual (hρ.eigenvalues (τ k)) :=
              Tuple.monotone_sort eigen_dual this
            simp only [OrderDual.toDual_le_toDual] at h_sorted
            exact h_sorted
          have h_term_by_term : ∀ i : Fin R, i ≤ k → eig_comp (σ i) ≤ hρ.eigenvalues (τ i) := by
            intro i hi_le
            by_cases h_i_zero : i.val = 0
            · have : i = ⟨0, hR_pos⟩ := by ext; exact h_i_zero
              rw [this]
              calc eig_comp (σ ⟨0, hR_pos⟩) = 1 - δ := σ_0_is_max
                _ ≤ hρ.eigenvalues (τ ⟨0, hR_pos⟩) := eigen_max_bound
            · have hi_pos : 0 < i.val := by omega
              have : eig_comp (σ i) = δ / (R - 1) := h_eig_comp_tail i hi_pos
              calc eig_comp (σ i) = δ / (R - 1) := this
                _ = eig_comp (σ k) := by rw [← h_eig_comp_tail k h_k_pos]
                _ ≤ hρ.eigenvalues (τ k) := h_not_strict
                _ ≤ hρ.eigenvalues (τ i) := h_eigen_sorted i hi_pos hi_le
          have h_sum : ∑ i ∈ Finset.univ.filter (· ≤ k), eig_comp (σ i) ≤
                       ∑ i ∈ Finset.univ.filter (· ≤ k), hρ.eigenvalues (τ i) := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact h_term_by_term i hi
          linarith [h_sum, h_not]

        have h_tail_ineq : ∑ i ∈ Finset.univ.filter (k < ·), eig_comp (σ i) <
                           ∑ i ∈ Finset.univ.filter (k < ·), hρ.eigenvalues (τ i) := by
          have h_partition_eig : ∑ i, eig_comp (σ i) =
                                 ∑ i ∈ Finset.univ.filter (· ≤ k), eig_comp (σ i) +
                                 ∑ i ∈ Finset.univ.filter (k < ·), eig_comp (σ i) := by
            rw [← Finset.sum_union]
            · congr; ext i; simp; omega
            · simp [Finset.disjoint_iff_ne]; intro x _ y _; omega
          have h_partition_eigen : ∑ i, hρ.eigenvalues (τ i) =
                                    ∑ i ∈ Finset.univ.filter (· ≤ k), hρ.eigenvalues (τ i) +
                                    ∑ i ∈ Finset.univ.filter (k < ·), hρ.eigenvalues (τ i) := by
            rw [← Finset.sum_union]
            · congr; ext i; simp; omega
            · simp [Finset.disjoint_iff_ne]; intro x _ y _; omega
          have h_total_eig : ∑ i, eig_comp (σ i) = 1 := by
            trans (∑ i, eig_comp i)
            · apply Equiv.sum_comp σ
            · exact eig_comp_sum
          have h_total_eigen : ∑ i, hρ.eigenvalues (τ i) = 1 := by
            trans (∑ i, hρ.eigenvalues i)
            · apply Equiv.sum_comp τ
            · exact trace_one
          rw [h_total_eig] at h_partition_eig
          rw [h_total_eigen] at h_partition_eigen
          have : (1 : ℝ) = 1 := rfl
          linarith

        have h_tail_geq : ∑ i ∈ Finset.univ.filter (k < ·), eig_comp (σ i) ≥
                          ∑ i ∈ Finset.univ.filter (k < ·), hρ.eigenvalues (τ i) := by
          apply Finset.sum_le_sum
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          have h_eig_comp_tail : ∀ j : Fin R, 0 < j.val → eig_comp (σ j) = δ / (R - 1) := by
            intro j hj_pos
            by_cases h_distinct : 1 - δ > δ / (R - 1)
            · have h_sorted : eig_comp (σ j) ≤ eig_comp (σ ⟨0, hR_pos⟩) := by
                have : (⟨0, hR_pos⟩ : Fin R) ≤ j := Nat.zero_le j.val
                have h : OrderDual.toDual (eig_comp (σ ⟨0, hR_pos⟩)) ≤ OrderDual.toDual (eig_comp (σ j)) :=
                  Tuple.monotone_sort eig_dual this
                simp only [OrderDual.toDual_le_toDual] at h
                exact h
              rw [σ_0_is_max] at h_sorted
              simp only [eig_comp] at h_sorted ⊢
              split_ifs with h_if
              · exfalso
                have h_sigma_zero_eq : eig_comp (σ ⟨0, hR_pos⟩) = 1 - δ := σ_0_is_max
                simp only [eig_comp] at h_sigma_zero_eq
                split_ifs at h_sigma_zero_eq with h_sigma_zero
                · have : σ j = σ ⟨0, hR_pos⟩ := by rw [h_sigma_zero, h_if]
                  have : j = ⟨0, hR_pos⟩ := σ.injective this
                  have : j.val = 0 := by simp [this]
                  omega
                · linarith [h_distinct, h_sigma_zero_eq]
              · rfl
            · push_neg at h_distinct
              have h_equal : 1 - δ = δ / (R - 1) := by
                have h_upper : δ / (R - 1) ≤ 1 - δ := by
                  have h1 : (1 : ℝ) < R := by norm_cast
                  have h2 : (0 : ℝ) < R - 1 := by linarith
                  have h3 : δ * R ≤ R - 1 := by
                    calc δ * R ≤ ((R - 1) / R) * R := by
                          apply mul_le_mul_of_nonneg_right hδ_small
                          linarith
                      _ = R - 1 := by field_simp [ne_of_gt h1]
                  have : δ ≤ (R - 1) * (1 - δ) := by linarith
                  calc δ / (R - 1) ≤ (R - 1) * (1 - δ) / (R - 1) := by
                        apply div_le_div_of_nonneg_right this (le_of_lt h2)
                    _ = 1 - δ := by field_simp [ne_of_gt h2]
                exact le_antisymm h_distinct h_upper
              simp only [eig_comp]
              split_ifs
              · exact h_equal
              · rfl
          have hj_pos : 0 < j.val := by omega
          have h_j_eq : eig_comp (σ j) = δ / (R - 1) := h_eig_comp_tail j hj_pos
          have h_eigen_decreasing : hρ.eigenvalues (τ j) ≤ hρ.eigenvalues (τ k) := by
            have : k < j := hj
            have h_sorted : OrderDual.toDual (hρ.eigenvalues (τ k)) ≤ OrderDual.toDual (hρ.eigenvalues (τ j)) :=
              Tuple.monotone_sort eigen_dual (le_of_lt this)
            simp only [OrderDual.toDual_le_toDual] at h_sorted
            exact h_sorted
          calc hρ.eigenvalues (τ j) ≤ hρ.eigenvalues (τ k) := h_eigen_decreasing
            _ ≤ eig_comp (σ k) := le_of_lt h_k_strict
            _ = δ / (R - 1) := h_eig_comp_tail k h_k_pos
            _ = eig_comp (σ j) := h_j_eq.symm

        linarith [h_tail_ineq, h_tail_geq]

    · -- Part (b): Verify total sums are equal (both equal 1)
      rw [eig_comp_sum, trace_one]

  -- Step 6: Apply Schur convexity theorem
  -- Key insight: The function f(x) = ∑ᵢ xᵢ log(xᵢ) is Schur-convex.
  -- Combined with majorization, this gives: f(eig_comp) ≤ f(eigenvalues)
  have entropy_bound : ∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) ≥
                       ∑ i, eig_comp i * Real.log (eig_comp i) := by
    have eig_comp_nonneg : ∀ i : Fin R, 0 ≤ eig_comp i := by
      intro i
      simp only [eig_comp]
      split_ifs
      · linarith [hδ_lt_one]
      · apply div_nonneg hδ_pos
        have : (1 : ℝ) < (R : ℝ) := by norm_cast
        linarith
    have schur_property : SchurConvex (fun x : Fin R → ℝ => ∑ i, x i * Real.log (x i)) := schur_convex_xlogx
    unfold SchurConvex at schur_property
    have majorization_condition : (let x_dual : Fin R → OrderDual ℝ := fun i => OrderDual.toDual (eig_comp i)
                                    let y_dual : Fin R → OrderDual ℝ := fun i => OrderDual.toDual (hρ.eigenvalues i)
                                    let σ := Tuple.sort x_dual
                                    let τ := Tuple.sort y_dual
                                    (∀ k : Fin R, ∑ i ∈ (Finset.univ.filter (· ≤ k)), eig_comp (σ i) ≤
                                                  ∑ i ∈ (Finset.univ.filter (· ≤ k)), hρ.eigenvalues (τ i)) ∧
                                    (∑ i, eig_comp i = ∑ i, hρ.eigenvalues i)) := by
      obtain ⟨hmaj, hsum⟩ := majorization
      exact ⟨hmaj, by rw [eig_comp_sum, trace_one]⟩
    have := schur_property eig_comp hρ.eigenvalues eig_comp_nonneg eigenvalues_nonneg majorization_condition
    simp only at this
    exact this

  -- Step 7: Rewrite von Neumann entropy in terms of eigenvalues
  rw [vonNeumannEntropy_hermitian ρ hρ]
  simp only [neg_mul]

  -- Step 8: Compute entropy of comparison distribution explicitly
  -- Result: H(eig_comp) = -(1-δ)log(1-δ) - δ log(δ/(R-1))
  have eig_comp_entropy : ∑ i, eig_comp i * Real.log (eig_comp i) =
                          (1 - δ) * Real.log (1 - δ) + δ * Real.log (δ / (R - 1)) := by
    let i₀ : Fin R := ⟨0, hR_pos⟩
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀)]
    have h_first : eig_comp i₀ * Real.log (eig_comp i₀) = (1 - δ) * Real.log (1 - δ) := by
      simp only [eig_comp, i₀, if_pos rfl]
    rw [h_first]
    have h_rest : ∑ i ∈ Finset.univ.erase i₀, eig_comp i * Real.log (eig_comp i) =
                  δ * Real.log (δ / (R - 1)) := by
      trans ∑ i ∈ Finset.univ.erase i₀, (δ / (R - 1)) * Real.log (δ / (R - 1))
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_erase] at hi
        simp only [eig_comp]
        rw [if_neg hi.1]
      · rw [Finset.sum_const]
        have h_card : (Finset.univ.erase i₀).card = R - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i₀)]
          simp [Fintype.card_fin]
        rw [h_card, nsmul_eq_mul]
        have h_nz : (↑R - 1 : ℝ) ≠ 0 := by
          have : (1 : ℝ) < R := by norm_cast
          linarith
        have h_cast : (↑(R - 1) : ℝ) = ↑R - 1 := by
          have : 1 ≤ R := by omega
          rw [Nat.cast_sub this]
          norm_num
        rw [h_cast]
        calc (↑R - 1) * ((δ / (↑R - 1)) * Real.log (δ / (↑R - 1)))
            = ((↑R - 1) * (δ / (↑R - 1))) * Real.log (δ / (↑R - 1)) := by ring
          _ = δ * Real.log (δ / (↑R - 1)) := by rw [mul_div_cancel₀ _ h_nz]
    rw [h_rest]
    ring

  simp only [Complex.ofReal_mul, Complex.ofReal_sum, neg_re, one_mul]

  -- Step 9: Simplify complex-to-real conversions
  -- Real eigenvalues remain real after casting to ℂ and taking real part
  have h_simplify : (∑ x, (hρ.eigenvalues x : ℂ) * (Real.log (hρ.eigenvalues x) : ℂ)).re =
                    ∑ x, hρ.eigenvalues x * Real.log (hρ.eigenvalues x) := by
    trans (∑ x, ((hρ.eigenvalues x : ℂ) * (Real.log (hρ.eigenvalues x) : ℂ)).re)
    · rw [Complex.re_sum]
    · congr 1; ext x
      have : (hρ.eigenvalues x : ℂ) * (Real.log (hρ.eigenvalues x) : ℂ) =
             ↑(hρ.eigenvalues x * Real.log (hρ.eigenvalues x)) := by
        rw [← Complex.ofReal_mul]
      rw [this, Complex.ofReal_re]

  -- Step 10: Final inequality via chain of equalities and Schur-convexity
  calc -((∑ x, (hρ.eigenvalues x : ℂ) * (Real.log (hρ.eigenvalues x) : ℂ)).re)
      = -(∑ x, hρ.eigenvalues x * Real.log (hρ.eigenvalues x)) := by
          rw [h_simplify]
    _ ≤ -(∑ i, eig_comp i * Real.log (eig_comp i)) := by
          apply neg_le_neg
          exact entropy_bound
    _ = -((1 - δ) * Real.log (1 - δ) + δ * Real.log (δ / (↑R - 1))) := by
          rw [eig_comp_entropy]
    _ = -((1 - δ) * Real.log (1 - δ)) - δ * Real.log (δ / (↑R - 1)) := by
          ring
