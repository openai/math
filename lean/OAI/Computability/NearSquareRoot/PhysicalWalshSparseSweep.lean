import OAI.Computability.NearSquareRoot.PhysicalWalshPieceRate
import OAI.Computability.NearSquareRoot.PhysicalWalshPieceClock

/-! # Physical time and space for the complete sweep of even Walsh pieces

The record-width and selector bounds hold at each invocation. The machine
constant covers every exceptional finite width, and charges the final copy to
the physical output tape as part of the same asymptotic cost.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space PhysicalWalshNode KernelPass Filter

noncomputable def sparseTime (ρ : ℝ) (k : ℕ) :=
  ⌈(2:ℝ)^k*k*(1+(k:ℝ))^ρ*(1+Real.log (2+(k:ℝ)))⌉₊

def sparseSpace (k : ℕ) := 2^k*k

theorem space_le_clock {ρ : ℝ} (hr : 0 ≤ ρ) (k : ℕ) : sparseSpace k ≤ sparseTime ρ k := by
  have base : 1 ≤ (1+(k:ℝ))^ρ := Real.one_le_rpow (by linarith [Nat.cast_nonneg (α:=ℝ) k]) hr
  have log : 0 ≤ Real.log (2+(k:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  let V := (2:ℝ)^k*k
  have pos : 0 ≤ V := by dsimp [V]; positivity
  have raw : V ≤ V*(1+(k:ℝ))^ρ*(1+Real.log (2+(k:ℝ))) :=
    (le_mul_of_one_le_right pos base).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have bound := raw.trans (Nat.le_ceil _)
  unfold sparseSpace sparseTime
  dsimp only [V] at bound
  exact_mod_cast bound

/-- The composable command and its release with visited-cell and clock bounds. -/
def SparseRun {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ρ : ℝ) {I : Type} (b : I → Root) : Prop :=
    let T := fun i => sparseTime ρ (b i).k
    let S := fun i => sparseSpace (b i).k
    BoundedTask T S (fun i => input (a:=a) (W:=W) (b i)) (fun i => output hw p (b i)) ∧
      ∃ C : ℕ, TapeRun (fun i => C*(T i+1)) (fun i => C*(S i+1))
        (fun i => input (a:=a) (W:=W) (b i)) (fun i => output hw p (b i))

/-- The exact sweep counters fit the sparse rates on every width. The
constants include all finite exceptional input shapes and are independent
of the program realizing the measured stages. -/
theorem sparseClock_bounds {A W calls C d : ℕ} (ha : 1 < A) (hw : 0 < W)
    {ρ B c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hB : 0 ≤ B) (hc : 0 ≤ c) (hP : ∀ w, 0 ≤ P w)
    {I : Type} (b : I → Root) {g R H Q : ℝ} {q : ℕ} (hg : 0 < g) (hR : 0 ≤ R) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (sparse : ∀ i, ((b i).s:ℝ) ≤ g*(b i).k/Real.log (2+(b i).k))
    (width : ∀ i, ((b i).w:ℝ) ≤ R*((b i).k+1))
    (overhead : ∀ i, 0 ≤ L (b i).w ∧ L (b i).w ≤ H*(1+Real.log (2+(b i).k)))
    (setup : ∀ i, P (b i).w ≤ Q*((b i).k+1:ℝ)^q) :
    ∃ M N : ℕ,
      (∀ i, sweepTime A W calls ρ B c L P C d (b i).k (b i).s (b i).w+1 ≤ M*(sparseTime ρ (b i).k+1)) ∧
      (∀ i, sweepSpace A W c P C d (b i).k (b i).s (b i).w+1 ≤ N*(sparseSpace (b i).k+1)) := by
  have rate := eventually_sweepRate (calls:=calls) (C:=C) (d:=d) (q:=q) (L:=L) (P:=P) ha hw hr hB hc hH
    (R:=2*R) (by positivity) (Q:=Q*2^q) (by positivity) hg
  obtain ⟨T,S,_,_,large⟩ := rate
  have major : ∀ᶠ k : ℕ in atTop, ∀ i, (b i).k=k →
      (sweepTime A W calls ρ B c L P C d k (b i).s (b i).w : ℝ) ≤
        T*((2:ℝ)^k*k*(1+(k:ℝ))^ρ*(1+Real.log (2+k))) ∧
      (sweepSpace A W c P C d k (b i).s (b i).w : ℝ) ≤ S*((2:ℝ)^k*k) := by
    filter_upwards [large,eventually_ge_atTop 1] with k bound hk
    intro i eq
    have big : (1:ℝ) ≤ k := by exact_mod_cast hk
    have w := width i
    have s := sparse i
    have o := overhead i
    have q' := setup i
    rw [eq] at w s o q'
    have upper : ((b i).w:ℝ) ≤ (2*R)*k := w.trans (by nlinarith [mul_nonneg hR (sub_nonneg.mpr big)])
    have poly : Q*((k:ℝ)+1)^q ≤ (Q*2^q)*(k:ℝ)^q := by
      rw [mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) q) hQ
    obtain ⟨tm,sp⟩ := bound (b i).s (b i).w s upper o.1 o.2 (hP _) (q'.trans poly)
    exact ⟨by simpa [mul_assoc] using tm, by simpa [mul_assoc] using sp⟩
  have nonneg (k : ℕ) : 0 ≤ (2:ℝ)^k*k*(1+(k:ℝ))^ρ*(1+Real.log (2+k)) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) k] : (1:ℝ) ≤ 2+k)
    positivity
  obtain ⟨M,tm⟩ := absorb_small_widths b (sweepTime A W calls ρ B c L P C d) _ nonneg hg.le hR sparse width
    (major.mono (fun _ h i eq => (h i eq).1))
  obtain ⟨N,sp⟩ := absorb_small_widths b (sweepSpace A W c P C d) (fun k => (2:ℝ)^k*k) (fun _ => by positivity)
    hg.le hR sparse width (major.mono (fun _ h i eq => (h i eq).2))
  refine ⟨M,N,tm,fun i => ?_⟩
  simpa only [←Nat.cast_ofNat (R:=ℝ) (n:=2), ←Nat.cast_pow, ←Nat.cast_mul, Nat.ceil_natCast, sparseSpace] using sp i

/-- Every input in the sparse regime is processed by the same program.
Numerical feasibility refers to the actual, sequentially reached records.
The output contains the entire ordered stream after the last even piece. -/
theorem sparseRoundedSweep {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    {ρ c : ℝ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hc : 0 ≤ c) (hP : ∀ w, 0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) {I : Type} (b : I → Root)
    (capacity : ∀ i, (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1)) (fits : ∀ i, (b i).Feasible hw p ha)
    {g R H Q : ℝ} {q : ℕ} (hg : 0 < g) (hR : 0 ≤ R) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (sparse : ∀ i, ((b i).s:ℝ) ≤ g*(b i).k/Real.log (2+(b i).k))
    (width : ∀ i, ((b i).w:ℝ) ≤ R*((b i).k+1))
    (overhead : ∀ i, 0 ≤ L (b i).w ∧ L (b i).w ≤ H*(1+Real.log (2+(b i).k)))
    (setup : ∀ i, P (b i).w ≤ Q*((b i).k+1:ℝ)^q) :
    SparseRun hw p ρ b := by
  obtain ⟨B,hB,d,C,run⟩ := roundedSweepRate hw p hP release ha b capacity fits
  obtain ⟨M,N,tm,sp⟩ := sparseClock_bounds (calls:=p.calls) (C:=C) (d:=d) ha hw hr hB hc hP b
    hg hR hH hQ sparse width overhead setup
  have task := run.bound M N tm sp
  exact ⟨task,task.releaseOfSpaceLeTime (fun i => space_le_clock hr.le (b i).k)⟩

/-- The sparse physical sweep specialized to the compiled plan. All terms
other than the supplied XOR router are bounded by the concrete program's
arithmetic, frame, and compact descriptor estimates. -/
theorem sparseRoutedSweep {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (ha : 1 < a+1) (wide : 2 ≤ W) {ρ : ℝ} (hr : 0 < ρ) (saving : (p.calls:ℝ)/W < ((a+1:ℕ):ℝ)^ρ) :
    ∃ D : ℕ, ∀ d, D ≤ d → ∀ (extra : Shape → ℕ), XorRuns a W (nodeScan a W d extra) (nodeArena a W d) →
    ∀ (c : ℝ) (L P : ℕ → ℝ), 0 ≤ c → (∀ w, 1 ≤ L w) → (∀ w, 0 ≤ P w) →
    (∀ s, withinWidth (a+1) s → (extra s:ℝ) ≤ localTime (a+1) ρ c (L s.w) (P s.w) s.level (bitVolume (a+1) s)) →
    ∀ {I : Type} (b : I → Root), (∀ i, (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1)) →
    (∀ i, (b i).Feasible hw p ha) → ∀ {g R H Q : ℝ} {q : ℕ}, 0 < g → 0 ≤ R → 0 ≤ H → 0 ≤ Q →
    (∀ i, ((b i).s:ℝ) ≤ g*(b i).k/Real.log (2+(b i).k)) → (∀ i, ((b i).w:ℝ) ≤ R*((b i).k+1)) →
    (∀ i, L (b i).w ≤ H*(1+Real.log (2+(b i).k))) → (∀ i, P (b i).w ≤ Q*((b i).k+1:ℝ)^q) → SparseRun hw p ρ b := by
  obtain ⟨D,_,ready⟩ := routedPieceRelease hw p ha wide hr.le saving
  refine ⟨D,fun d hd extra route c L P hc hL hP router I b capacity fits g R H Q q hg hR hH hQ sparse width overhead setup => ?_⟩
  obtain ⟨K,_,exec⟩ := ready d hd
  have piece := exec extra route c L P hc hL hP router
  apply sparseRoundedSweep hw p ha hr (by positivity) (envelopeSetup_nonneg K d hP) piece b capacity fits
    hg hR hH (Q:=K*((34*(R+1))^d+1)+Q+1) (q:=max d q) (by positivity) sparse width
    (fun i => ⟨zero_le_one.trans (hL _),overhead i⟩)
  intro i
  apply envelopeSetup_le_power (R:=R+1) (by positivity) hQ (by linarith [Nat.cast_nonneg (α:=ℝ) (b i).k]) _ (setup i)
  have := width i
  nlinarith [Nat.cast_nonneg (α:=ℝ) (b i).k]

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
