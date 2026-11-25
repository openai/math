import OAI.Computability.NearSquareRoot.PhysicalWalshNodeFuel

/-! # Accounting for local scans and the compact header of a Walsh node

The record and descriptor costs are charged here. An address router can
supply its separate scan and workspace bounds on the same node geometry.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open PhysicalWalsh PhysicalWalshContext

/-- Number of record bits in the occupied parent bank. -/
def bitVolume (A : ℕ) (s : Shape) : ℝ := (count A s : ℝ)*(s.w+1)

theorem bitVolume_nonneg (A : ℕ) (s : Shape) : 0 ≤ bitVolume A s := by unfold bitVolume; positivity

/-- The fixed descriptor polynomial including any additive router setup. -/
def envelopeSetup (K d : ℕ) (P : ℕ → ℝ) (w : ℕ) : ℝ :=
  K*((24*((w:ℝ)+1)+10)^d+1)+P w+1

theorem envelopeSetup_nonneg (K d : ℕ) {P : ℕ → ℝ} (hP : ∀ w, 0 ≤ P w) (w : ℕ) :
    0 ≤ envelopeSetup K d P w := by
  have := hP w
  unfold envelopeSetup
  positivity

private theorem meter_le {A d K m extra : ℕ} {s : Shape} (hA : 2 ≤ A) (admit : withinWidth A s)
    (hm : m ≤ K*(allowance A d s+1)+extra) :
    (m:ℝ)+1 ≤ 4*K*bitVolume A s + K*((24*((s.w:ℝ)+1)+10)^d+1)+(extra:ℝ)+1 := by
  have hraw := allowance_le_of_withinWidth hA d s admit
  have room : (allowance A d s:ℝ) ≤ 4*bitVolume A s + (24*((s.w:ℝ)+1)+10)^d := by
    unfold bitVolume
    exact_mod_cast hraw
  have h : (m:ℝ) ≤ K*((allowance A d s:ℝ)+1)+(extra:ℝ) := by exact_mod_cast hm
  have hK := mul_le_mul_of_nonneg_left room (Nat.cast_nonneg (α := ℝ) K)
  linarith only [h,hK]

/-- The scan weight always dominates a plain linear scan, for every exponent. -/
theorem space_le_time (A : ℕ) (ρ : ℝ) {c L : ℝ} (hc : 0 ≤ c) (hL : 1 ≤ L) (P : ℝ) (j : ℕ)
    {V : ℝ} (hV : 0 ≤ V) : localSpace c P j V ≤ localTime A ρ c L P j V := by
  have hpow : 0 ≤ ((2:ℝ)*(A:ℝ)^j)^ρ := by positivity
  have hcl : c ≤ c*L := le_mul_of_one_le_right hc hL
  have hvol := mul_le_mul_of_nonneg_right hcl hV
  unfold localSpace localTime
  apply add_le_add_left
  exact hvol.trans (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hc (by linarith)) hV) (by linarith))

/-- Local time of the actual layout scan plus the extra address router. -/
theorem scan_envelope {A d K m extra : ℕ} {s : Shape} {c ρ : ℝ} {L P : ℕ → ℝ}
    (hA : 2 ≤ A) (admit : withinWidth A s) (hL : 1 ≤ L s.w)
    (hm : m ≤ K*(allowance A d s+1)+extra)
    (router : (extra:ℝ) ≤ localTime A ρ c (L s.w) (P s.w) s.level (bitVolume A s)) :
    (m:ℝ)+1 ≤ localTime A ρ (4*K+c) (L s.w) (envelopeSetup K d P s.w) s.level (bitVolume A s) := by
  have base := meter_le hA admit hm
  have linear := space_le_time A ρ (c := (4*K:ℝ)) (by positivity) hL 0 s.level (bitVolume_nonneg A s)
  unfold localTime localSpace at linear
  unfold localTime at router ⊢
  unfold envelopeSetup
  linarith only [base,linear,router]

/-- Local space accounts for the resident records, descriptor, and router. -/
theorem arena_envelope {A d K m extra : ℕ} {s : Shape} {c : ℝ} {P : ℕ → ℝ}
    (hA : 2 ≤ A) (admit : withinWidth A s) (hm : m ≤ K*(allowance A d s+1)+extra)
    (router : (extra:ℝ) ≤ localSpace c (P s.w) s.level (bitVolume A s)) :
    (m:ℝ)+1 ≤ localSpace (4*K+c) (envelopeSetup K d P s.w) s.level (bitVolume A s) := by
  have base := meter_le hA admit hm
  unfold localSpace at router ⊢
  unfold envelopeSetup
  linarith only [base,router]

/-- The initial read of the raw descriptor and bank fits the charged root
workspace as soon as its fixed meter covers one copy of the node allowance. -/
theorem entry_envelope {A d K : ℕ} {s : Shape} {c : ℝ} {P : ℕ → ℝ}
    (hA : 2 ≤ A) (admit : withinWidth A s) (hd : 1 ≤ d) (hK : 1 ≤ K) (hc : 0 ≤ c) (hP : 0 ≤ P s.w) :
    (allowance A 1 s:ℝ)+1 ≤ localSpace (4*K+c) (envelopeSetup K d P s.w) s.level (bitVolume A s) := by
  apply arena_envelope (extra := 0) hA admit
  · rw [Nat.add_zero]
    exact (allowance_mono hd s).trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hK))
  · unfold localSpace
    exact_mod_cast add_nonneg (mul_nonneg hc (bitVolume_nonneg A s)) hP

/-- The enriched work arena and the compact-layout allowance share a single
multiplicative constant at every possible node. -/
theorem max_arena_allowance_le (a W d : ℕ) (hd : 1 ≤ d) : ∃ K : ℕ, 1 ≤ K ∧ ∀ s : Shape,
    max (allowance (a+1) d s) (routeArena (coords a W) Shape.w (Header.wire (a+1)) s) ≤ K*(allowance (a+1) d s+1) := by
  obtain ⟨C,hC⟩ := routeArena_le_allowance a W d hd
  refine ⟨C+1,Nat.succ_pos _,fun s => max_le ?_ ?_⟩
  · exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  · exact (hC s).trans (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- At precision linear in the outer size parameter, the combined descriptor
and router setup is polynomial in that same parameter. -/
theorem envelopeSetup_le_power {K d q w : ℕ} {P : ℕ → ℝ} {R Q k : ℝ}
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hk : 1 ≤ k) (width : (w:ℝ)+1 ≤ R*k)
    (router : P w ≤ Q*k^q) :
    envelopeSetup K d P w ≤ (K*((34*R)^d+1)+Q+1)*k^(max d q) := by
  have hk' : 0 ≤ k := zero_le_one.trans hk
  have h1 := one_le_pow₀ hk (n := max d q)
  have hd : k^d ≤ k^(max d q) := pow_le_pow_right₀ hk (le_max_left ..)
  have hq : k^q ≤ k^(max d q) := pow_le_pow_right₀ hk (le_max_right ..)
  have hcoef : 24*((w:ℝ)+1)+10 ≤ (34*R)*k := by nlinarith [Nat.cast_nonneg (α := ℝ) w]
  have hp : (24*((w:ℝ)+1)+10)^d ≤ (34*R)^d*k^(max d q) := by
    calc
      _ ≤ ((34*R)*k)^d := pow_le_pow_left₀ (by positivity) hcoef d
      _ = _ := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
  have setup := mul_le_mul_of_nonneg_left (add_le_add hp h1) (Nat.cast_nonneg (α := ℝ) K)
  have hroute := router.trans (mul_le_mul_of_nonneg_left hq hQ)
  unfold envelopeSetup
  linarith only [setup,hroute,h1]

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
