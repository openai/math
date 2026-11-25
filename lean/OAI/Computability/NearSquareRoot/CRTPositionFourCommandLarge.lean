import OAI.Computability.NearSquareRoot.CRTPositionFourCommandRun
import OAI.Computability.NearSquareRoot.CRTPositionFourCommandWidths

/-! # Uniform large-width runs for explicit reserve parameters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
open IntegerMultiplication.Adic PositionProgram PositionRows EffectiveBoundedTask Filter
noncomputable section

private theorem overhead {ρ : ℝ} (hρ : 0 ≤ ρ) (a b k : ℕ) :
    payloadBits a k+payloadBits b k+1+(positionFactor ρ k+1) ≤ (a+b+5)*(positionFactor ρ k+1) := by
  have rate := positionFactor_pays (ρ := ρ) hρ (le_refl k)
  have e : positionRate ρ k ≤ positionFactor ρ k+1 := by have := one_le_positionRate hρ k; linarith
  exact_mod_cast (reserve_clock hρ a b k).trans (mul_le_mul_of_nonneg_left e (Nat.cast_nonneg (α := ℝ) (a+b+5)))

/-- An externally supplied degree pair is valid whenever it pays the universal
row overhead and the chosen address widths fit. -/
theorem runs_from_fits {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd) (hc : RowCommand.GroupedRuns core ρ) :
    ∃ D : ℕ, ∀ a b : ℕ, D ≤ a → D ≤ b → ⌈ρ⌉₊+2 ≤ b →
    ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (_pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead),
    (∀ i, 0 < k i) → (∀ i, payloadBits a (k i)+payloadBits b (k i) ≤ k i/2-2) →
    let V i := 2^(k i)*(u i).count
    Runs ((widthCmd a b).join (reserveCmd core)) (fun i => V i*(positionFactor ρ (k i)+1)) V
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  obtain ⟨D,inner⟩ := reserve_runs positive core hc
  refine ⟨D,?_⟩
  intro a b da db eb I k U u pos p f hk cap
  let V i := 2^(k i)*(u i).count
  let T i := V i*(positionFactor ρ (k i)+1)
  have work := inner k (fun i => payloadBits a (k i)) (fun i => payloadBits b (k i)) cap
    u pos p f (fun _ => Nat.mul_le_mul_right _ da) (fun _ => Nat.mul_le_mul_right _ db)
    (fun i => (positionFactor_high (hk i)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ eb)))
  have steps := work.bound (t' := T) (s' := V) (a+b+5) 1 (fun i => ?_) (fun i => by change V i+1 ≤ 1*(V i+1); simp)
  · have pre := width_runs a b k V p (fun i => Nat.le_mul_of_pos_right _ (pos i))
      (cloth (fun i => line 2 (k i)) u f) 5
      (ReserveSmall.beadClothCap k _ u f pos (fun _ => le_rfl))
    exact (pre.mono (fun i => Nat.le_mul_of_pos_right (V i) (Nat.succ_pos _)) (fun _ => le_rfl)).sequence steps
  · let Z := payloadBits a (k i)+payloadBits b (k i)+1
    let F := positionFactor ρ (k i)+1
    have eq := Nat.mul_le_mul_right (V i) (overhead positive a b (k i))
    change (Z+F)*V i ≤ (a+b+5)*F*V i at eq
    change Z*V i+V i*F+1 ≤ (a+b+5)*(V i*F+1)
    nlinarith only [eq,Nat.zero_le a,Nat.zero_le b]

/-- The cutoff and both loose metadata degrees are explicit numeric command
parameters. One large-width program works for every payload and image table. -/
theorem large_named_runs {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd) (hc : RowCommand.GroupedRuns core ρ) :
    ∃ a b K : ℕ, ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
    (_pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead),
    (∀ i, K < k i) →
    let V i := 2^(k i)*(u i).count
    Runs ((widthCmd a b).join (reserveCmd core)) (fun i => V i*(positionFactor ρ (k i)+1)) V
      (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
      (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))) := by
  obtain ⟨D,run⟩ := runs_from_fits positive core hc
  let b := max D (⌈ρ⌉₊+2)
  obtain ⟨K,hK⟩ := eventually_atTop.1 (ReserveShort.eventually_two_reserves D b)
  refine ⟨D,b,K,?_⟩
  intro I k U u pos p f hk
  exact run D b le_rfl (le_max_left ..) (le_max_right ..) k u pos p f
    (fun i => Nat.zero_lt_of_lt (hk i)) (fun i => hK _ (hk i).le)

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
