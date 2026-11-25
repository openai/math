import OAI.Computability.MultitapeWeakETH.Concentration

/-! # Normalizing the placement and its terminal and advice costs -/

namespace OAI.Computability.MultitapeWeakETH

open Finset VPVNP.SpectralGeometry
open scoped BigOperators

variable {V X : Type} [Fintype V] [Nonempty V] [MetricSpace X]

noncomputable def normalizedDist (a : ℝ) (p : V → X) (v w : V) := a * dist (p v) (p w)

theorem normalize_placement (p : V → X) (A : Matrix V V ℝ) {β : ℝ}
    (positive : 0 < β) (nonnegative : ∀ i j, 0 ≤ A i j)
    (gap : β*walkEnergy A p < (∑ i, ∑ j, dist (p i) (p j)^2)/Fintype.card V) :
    ∃ a : ℝ, 0 < a ∧ (𝔼 j, 𝔼 i, (normalizedDist a p i j)^2) = 1 ∧
      a^2*walkEnergy A p / Fintype.card V < 1/β := by
  let P := (Fintype.card V : ℝ)
  let moment := (𝔼 i, 𝔼 j, dist (p i) (p j)^2)
  have ppos : 0 < P := Nat.cast_pos.mpr Fintype.card_pos
  have scaled : P*moment = (∑ i, ∑ j, dist (p i) (p j)^2)/P := by
    simp only [moment,Fintype.expect_eq_sum_div_card,← sum_div]
    change P*((_ / P)/P) = _
    field_simp
  have enonneg : 0 ≤ walkEnergy A p := sum_nonneg fun i _ =>
    sum_nonneg fun j _ => mul_nonneg (nonnegative i j) (sq_nonneg _)
  rw [← scaled] at gap
  have pos : 0 < moment := pos_of_mul_pos_right
    ((mul_nonneg positive.le enonneg).trans_lt gap) ppos.le
  let a := (Real.sqrt moment)⁻¹
  have apos : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr pos)
  have unit : a^2 * moment = 1 := by
    rw [show a^2 = moment⁻¹ by rw [← Real.sq_sqrt pos.le]; simp [a,Real.sq_sqrt pos.le]]
    exact inv_mul_cancel₀ pos.ne'
  refine ⟨a,apos,?_,?_⟩
  · rw [expect_comm]
    simpa only [normalizedDist,mul_pow,← mul_expect] using unit
  · apply (div_lt_div_iff₀ ppos positive).mpr
    nlinarith only [mul_lt_mul_of_pos_left gap (sq_pos_of_pos apos),congrArg (P*·) unit]

/-- Uniform scalar variance of a scaled observable follows from the Poincaré
bound on the superimposed expander. -/
theorem normalized_variance [DecidableEq V] (A : Matrix V V ℝ) (nonnegative : ∀ i j, 0 ≤ A i j)
    {C : ℝ} (hC : 0 ≤ C) (scalar : HasPoincareBound ℝ A C)
    (p : V → X) (a : ℝ) (f : V → ℝ) (lip : ∀ i j, |f i-f j| ≤ dist (p i) (p j)) :
    (𝔼 i, (a*f i - 𝔼 j, a*f j)^2) ≤ C*(a^2*walkEnergy A p/Fintype.card V) := by
  have h := scalar_variance A nonnegative hC scalar p f lip
  have factor (i) : (a*f i - 𝔼 j, a*f j)^2 = a^2*(f i - 𝔼 j, f j)^2 := by
    rw [← mul_expect,← mul_sub,mul_pow]
  simp_rw [factor,← mul_expect]
  rw [Fintype.expect_eq_sum_div_card]
  have pc : (0:ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  field_simp
  nlinarith only [mul_le_mul_of_nonneg_left h (sq_nonneg a)]

/-- Both terminal draws can be restricted to lists of length N while paying
one factor of P/N in mean square. Starting positions and overlap are arbitrary. -/
theorem normalized_terminals (p : V → X) {a ε : ℝ} (apos : 0 < a) (he : 0 ≤ ε)
    (unit : (𝔼 j, 𝔼 i, (normalizedDist a p i j)^2) = 1)
    (variance : ∀ f : V → ℝ, (∀ i j, |f i-f j| ≤ dist (p i) (p j)) →
      (𝔼 i, (a*f i - 𝔼 j, a*f j)^2) ≤ ε)
    {N : ℕ} (left right : Fin N ↪ V) :
    (∑ j, ∑ i, (normalizedDist a p (left i) (right j)-1)^2) ≤
      12*(N:ℝ)*Fintype.card V*ε := by
  let d := normalizedDist a p
  let g (j : V) := 𝔼 i, d i j
  let μ := 𝔼 j, g j
  have cols (j : V) : (𝔼 i, (d i j-g j)^2) ≤ ε := variance
    (fun i => dist (p i) (p j)) (fun i k => abs_dist_sub_le _ _ _)
  have means : (𝔼 j, (g j-μ)^2) ≤ ε := by
    simpa only [g,μ,d,normalizedDist,← mul_expect] using
      variance (fun j => 𝔼 i, dist (p i) (p j)) (distance_mean_lipschitz p)
  have shift := mean_distance_deviation d (fun _ _ => mul_nonneg apos.le dist_nonneg) unit ε cols means
  have pc : (0:ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have unaverage (z : V → ℝ) (h : (𝔼 i, z i) ≤ ε) : ∑ i, z i ≤ Fintype.card V*ε := by
    rw [Fintype.expect_eq_sum_div_card] at h
    simpa only [mul_comm ε] using (div_le_iff₀ pc).mp h
  have pair := terminal_pair_deviation left right d g μ ((Fintype.card V : ℝ)*ε)
    (fun j => unaverage _ (cols j)) (unaverage _ means)
  have hn : (N:ℝ) ≤ Fintype.card V := by
    exact_mod_cast (show N ≤ Fintype.card V by simpa using Fintype.card_le_of_injective _ left.injective)
  change (μ-1)^2 ≤ 2*ε at shift
  nlinarith only [pair,mul_le_mul_of_nonneg_left shift (sq_nonneg (N:ℝ)),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg N)) he]

/-- One barycenter works simultaneously for every choice of nonnegative pin weights. -/
theorem normalized_center [CompleteSpace X] [Nonempty X] (segments : HasCATZeroSegments X)
    (p : V → X) {a ε : ℝ} (apos : 0 < a)
    (unit : (𝔼 j, 𝔼 i, (normalizedDist a p i j)^2) = 1)
    (variance : ∀ f : V → ℝ, (∀ i j, |f i-f j| ≤ dist (p i) (p j)) →
      (𝔼 i, (a*f i - 𝔼 j, a*f j)^2) ≤ ε) :
    ∃ o : X, ∀ h : V → ℝ, (∀ v, 0 ≤ h v) →
      ∑ v, h v*(a*dist (p v) o) ≤ (∑ v, h v)/Real.sqrt 2 +
        Real.sqrt (∑ v, (h v)^2)*Real.sqrt (Fintype.card V*ε) := by
  let P := (Fintype.card V : ℝ)
  have pc : 0 < P := Nat.cast_pos.mpr Fintype.card_pos
  have avg (f : V → ℝ) : (∑ i, P⁻¹*f i) = 𝔼 i, f i := by
    rw [← mul_sum,Fintype.expect_eq_sum_div_card]; dsimp [P]; ring
  obtain ⟨o,bound⟩ := exists_center_half_energy segments (fun _ : V => P⁻¹) p
    (fun _ => inv_nonneg.mpr pc.le) (by simp [P,pc.ne'])
  simp_rw [weightedSquaredDistance,avg] at bound
  have unit' : a^2*(𝔼 j, 𝔼 i, dist (p i) (p j)^2) = 1 := by
    simpa only [normalizedDist,mul_pow,← mul_expect] using unit
  let radius (v : V) := a*dist (p v) o
  let μ := 𝔼 v, radius v
  have small : μ^2 ≤ 1/2 := by
    have jensen := MetricKMedian.PCP.mean_sq_le_energy radius
    simp only [MetricKMedian.PCP.energy,radius,mul_pow,← mul_expect] at jensen
    change (𝔼 i, a*dist (p i) o)^2 ≤ _
    rw [← mul_expect,mul_pow]
    nlinarith only [jensen,mul_le_mul_of_nonneg_left bound (sq_nonneg a),unit']
  have mean : μ ≤ 1/Real.sqrt 2 := by
    have posμ : 0 ≤ μ := expect_nonneg fun _ _ => mul_nonneg apos.le dist_nonneg
    apply (sq_le_sq₀ posμ (by positivity : 0 ≤ 1/Real.sqrt 2)).mp
    rwa [div_pow,one_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have var := variance (fun i => dist (p i) o) (fun i j => abs_dist_sub_le _ _ _)
  change (𝔼 i, (radius i-μ)^2) ≤ ε at var
  rw [Fintype.expect_eq_sum_div_card] at var
  exact ⟨o,fun h hn => central_cost h radius μ (P*ε) hn mean
    (by simpa only [mul_comm ε] using (div_le_iff₀ pc).mp var)⟩

end OAI.Computability.MultitapeWeakETH
