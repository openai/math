import OAI.Computability.NearSquareRoot.PhysicalWalshGrouped
import OAI.Computability.NearSquareRoot.PhysicalWalshSparseSweep
import OAI.Computability.NearSquareRoot.Asymptotic

/-! # Sparse runtime of the grouped selected-Walsh pass

The input carries only the compact counters and its original ordered array.
The time bound covers padding, all rounded even pieces, truncation, and the
final parity-dependent butterfly. The tape bound includes the output copy.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space FixedPoint KernelPass PhysicalWalshNode Filter

theorem odd_volume_le (k : ℕ) : Odd.volume k ≤ 2*(sparseSpace k+1) := by
  cases k with
  | zero => decide
  | succ n =>
    have h : n+1+1 ≤ 2*(n+1) := by omega
    have bound := Nat.mul_le_mul_left (2^(n+1)) h
    unfold Odd.volume sparseSpace
    calc
      _ ≤ 2^(n+1)*(2*(n+1)) := bound
      _ ≤ _ := by ring_nf; omega

/-- The per-record ceiling binary logarithm is covered by the logarithmic
scan factor in the sparse time bound, including the singleton input. -/
theorem odd_time_le {ρ : ℝ} (hr : 0 ≤ ρ) : ∃ D : ℕ, ∀ k, Odd.time k ≤ D*(sparseTime ρ k+1) := by
  let d := 1 + (Real.log 2)⁻¹
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let D := ⌈2*(d+1)⌉₊+1
  have coef : 2*(d+1) ≤ (D:ℝ) := (Nat.le_ceil _).trans (by dsimp [D]; push_cast; linarith)
  refine ⟨D,fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl|hk
  · have pos : 0 < D*(sparseTime ρ 0+1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    change 1 ≤ _
    exact pos
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  let Z := 1+Real.log (2+(k:ℝ))
  have hz : 1 ≤ Z := by dsimp [Z]; linarith [Real.log_nonneg (show 1 ≤ 2+(k:ℝ) by linarith)]
  have l1 : (Nat.clog 2 (k+1):ℝ) ≤ d*logScale (k+1) := by
    exact (show (Nat.clog 2 (k+1):ℝ) ≤ (max 1 (Nat.clog 2 (k+1)):ℕ) by exact_mod_cast le_max_right ..).trans
      (clog_le_logScale (Nat.succ_pos _))
  have l2 : logScale (k+1) ≤ Z := by
    unfold logScale Z
    apply add_le_add_right
    apply Real.log_le_log (by positivity)
    push_cast; linarith
  have lg : (Nat.clog 2 (k+1):ℝ)+1 ≤ (d+1)*Z := by
    linarith only [l1,mul_le_mul_of_nonneg_left l2 hd,hz]
  have width : 1 ≤ (1+(k:ℝ))^ρ := Real.one_le_rpow (by linarith) hr
  let V := (2:ℝ)^k*k
  have vn : 0 ≤ V := by dsimp [V]; positivity
  have v : V ≤ V*(1+(k:ℝ))^ρ := le_mul_of_one_le_right vn width
  have cost : (Odd.time k:ℝ) ≤ 2*(d+1)*(V*Z) := by
    have base := mul_le_mul (show (k:ℝ)+1 ≤ 2*k by linarith) lg
      (show 0 ≤ (Nat.clog 2 (k+1):ℝ)+1 by positivity) (show 0 ≤ (2:ℝ)*k by positivity)
    have mult := mul_le_mul_of_nonneg_left base (show 0 ≤ (2:ℝ)^k by positivity)
    unfold Odd.time GridTask.recordCost
    push_cast
    dsimp only [V]
    linarith only [mult]
  have raw : V*Z ≤ (sparseTime ρ k:ℝ) :=
    (mul_le_mul_of_nonneg_right v (zero_le_one.trans hz)).trans (Nat.le_ceil _)
  have nat : Odd.time k ≤ D*sparseTime ρ k := by
    exact_mod_cast cost.trans (mul_le_mul coef raw (mul_nonneg vn (zero_le_one.trans hz)) (Nat.cast_nonneg D))
  exact nat.trans (Nat.mul_le_mul_left _ (Nat.le_succ _))

/-- Physical input and physical rounded output of the complete grouped pass. -/
def GroupedRun {a W : ℕ} (hw : 0<W) (p : Plan (a+1) W W) (ρ : ℝ) {I : Type} (k s : I → ℕ)
    (x : (i : I) → ℕ → Record (k i)) : Prop :=
  let q i := send ((tally (k i),tally (s i)),words (2^k i) (x i))
  let r i := send (Odd.words (result hw p (k i) (s i) (x i)))
  BoundedTask (sparseTime ρ ∘ k) (sparseSpace ∘ k) q r ∧
    ∃ C : ℕ, TapeRun (fun i => C*(sparseTime ρ (k i)+1)) (fun i => C*(sparseSpace (k i)+1)) q r

/-- One grouped command works for the entire specified family of roots at the
fixed grid precision. Its numerical guard concerns the records actually
reached by the rounded sweep. -/
theorem sparseGroupedPass {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    {ρ c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hc : 0 ≤ c) (hP : ∀ w, 0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) {I : Type} (k s : I → ℕ) (x : (i : I) → ℕ → Record (k i))
    (sel : ∀ i, s i ≤ k i) (occ : ∀ i, PaddingHeader.extra (a+1) W (k i) (s i) ≤ 2^k i)
    (fits : ∀ i, (root (k i) (s i) (x i)).Feasible hw p ha)
    {g H Q : ℝ} {q : ℕ} (hg : 0 < g) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (sparse : ∀ i, (s i:ℝ) ≤ g*k i/Real.log (2+k i))
    (overhead : ∀ i, 0 ≤ L (componentBits (k i)) ∧ L (componentBits (k i)) ≤ H*(1+Real.log (2+k i)))
    (setup : ∀ i, P (componentBits (k i)) ≤ Q*(k i+1:ℝ)^q) : GroupedRun hw p ρ k s x := by
  let b i := root (k i) (s i) (x i)
  have capacity (i) : (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1) := by
    change extent (a+1) W (k i) (s i) ≤ 2^(componentBits (k i)+1)
    unfold extent
    rw [←Padding.total (a+1) hw (sel i)]
    calc
      _ ≤ 2^k i + 2^k i := Nat.add_le_add_left (occ i) _
      _ = 2^(k i+1) := by rw [pow_succ]; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold componentBits; omega)
  have wbound (i) : ((b i).w:ℝ) ≤ 96*((b i).k+1) := by
    change ((96*k i+4:ℕ):ℝ) ≤ 96*((k i:ℝ)+1)
    push_cast; linarith
  have even := sparseRoundedSweep hw p ha hr hc hP release b capacity fits hg (by norm_num: (0:ℝ) ≤ 96)
    hH hQ sparse wbound overhead setup
  have whole := groupedPass hw p k s x sel occ (sparseTime ρ ∘ k) (sparseSpace ∘ k) even.1
  obtain ⟨D,tm⟩ := odd_time_le hr.le
  have task := whole.bound (D+1) 3 (time' := sparseTime ρ ∘ k) (space' := sparseSpace ∘ k)
    (fun i => by dsimp only [Function.comp_apply]; rw [Nat.succ_mul]; have := tm (k i); omega)
    (fun i => by dsimp only [Function.comp_apply]; have := odd_volume_le (k i); omega)
  exact ⟨task,task.releaseOfSpaceLeTime (fun i => space_le_clock hr.le (k i))⟩

/-- Beyond one fixed threshold, sparsity supplies both selector bounds and
padding occupancy for every grouped input in the family. -/
theorem sparseGroupedPass_above {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    {ρ c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hc : 0 ≤ c) (hP : ∀ w, 0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) {g H Q : ℝ} {q : ℕ} (hg : 0 < g) (hH : 0 ≤ H) (hQ : 0 ≤ Q) :
    ∃ K : ℕ, ∀ {I : Type} (k s : I → ℕ) (x : (i : I) → ℕ → Record (k i)),
      (∀ i, K ≤ k i) → (∀ i, (s i:ℝ) ≤ g*k i/Real.log (2+k i)) →
      (∀ i, (root (k i) (s i) (x i)).Feasible hw p ha) →
      (∀ i, 0 ≤ L (componentBits (k i)) ∧ L (componentBits (k i)) ≤ H*(1+Real.log (2+k i))) →
      (∀ i, P (componentBits (k i)) ≤ Q*(k i+1:ℝ)^q) → GroupedRun hw p ρ k s x := by
  have geometry : ∀ᶠ k : ℕ in atTop, ∀ s : ℕ, (s:ℝ) ≤ g*k/Real.log (2+k) →
      s ≤ k ∧ PaddingHeader.extra (a+1) W k s ≤ 2^k := by
    filter_upwards [WalshPadding.eventually_paddedRows_bound ha hw g hg,
      WalshPadding.eventually_twice_selected_le g hg] with k pad small
    intro s sparse
    have sel : s ≤ k := by have := small s sparse; omega
    have upper := (pad s sparse).2.2.2.2
    rw [←Padding.total (a+1) hw sel] at upper
    exact ⟨sel,by omega⟩
  obtain ⟨K,ok⟩ := eventually_atTop.mp geometry
  exact ⟨K,fun k s x cut sparse fits overhead setup =>
    sparseGroupedPass hw p ha hr hc hP release k s x (fun i => (ok _ (cut i) _ (sparse i)).1)
      (fun i => (ok _ (cut i) _ (sparse i)).2) fits hg hH hQ sparse overhead setup⟩

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
