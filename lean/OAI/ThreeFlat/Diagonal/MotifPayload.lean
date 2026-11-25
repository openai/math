import OAI.ThreeFlat.Diagonal.MotifOuterTerms
import OAI.Computability.VPVNP.MotifWidths
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Aggregate payloads and the quadratic budget for one outer term

Mixed-radix words carry each surviving edge's base fields in selector
order. The finite set of profiles records only their total lengths.
-/

namespace ThreeFlat.Diagonal.MotifOuterTerms

open scoped BigOperators Classical
open Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths

variable {H E : Type*} [Fintype H] [Fintype E] {r : ℕ}

/-- Concatenate independently sized little-endian binary words. -/
def packDigits (w : Fin r → ℕ) : (∀ j, Fin (2 ^ w j)) ≃ Fin (2 ^ ∑ j, w j) :=
  finPiFinEquiv.trans (finCongr (Finset.prod_pow_eq_pow_sum Finset.univ w 2))

/-- The per-edge total width determines the outer term. -/
def totalWidth (w : H → E → ℕ) (s : Fin r → H) (e : E) : ℕ := ∑ j, w (s j) e

noncomputable def admitted (w : H → E → ℕ) (r : ℕ) : Finset (E → ℕ) :=
  Finset.univ.image (totalWidth (r := r) w)

def outerProfile (w : H → E → ℕ) (s : Fin r → H) : admitted w r :=
  ⟨totalWidth w s, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩

/-- Slice each edge's payload according to the actual selected tile widths.
This is a bijection, even when a selected width vanishes. -/
def packedPayload (w : H → E → ℕ) (s : Fin r → H) :
    (∀ j e, Fin (2 ^ w (s j) e)) ≃ (∀ e, Fin (2 ^ totalWidth w s e)) :=
  (Equiv.piComm (fun j e => Fin (2 ^ w (s j) e))).trans
    (Equiv.piCongrRight fun e => packDigits (fun j => w (s j) e))

/-- A sequence code has exactly the fixed base width at each tile position. -/
def sequenceCode {b : ℕ} (code : H ↪ Fin (2 ^ b)) (r : ℕ) : (Fin r → H) ↪ (Fin r → Fin (2 ^ b)) :=
  ⟨fun s j => code (s j), fun _ _ he => funext fun j => code.injective (congrFun he j)⟩

/-- Every admitted payload has norm no larger than the sum of its base
norms. The base width and radius are fixed before the demand arrives. -/
theorem payload_norm (w : H → E → ℕ) (q : E → ℝ) (hq : ∀ i, 0 < q i) {L : ℕ} {R : ℝ}
    (base : ∀ h, widthNorm q (fun e => (w h e : ℝ)) ≤ L * R) (v : admitted w r) :
    widthNorm q (fun e => (v.1 e : ℝ)) ≤ r * L * R := by
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp v.2
  rw [← hs]
  simp only [totalWidth, Nat.cast_sum]
  calc
    _ ≤ _ := widthNorm_sum_le q hq (fun j e => (w (s j) e : ℝ))
    _ ≤ ∑ _j : Fin r, (L * R) := Finset.sum_le_sum fun j _ => base (s j)
    _ = _ := by simp [mul_assoc]

/-- Uniform quadratic loss after placing `s` selector bits per tile on
each supply edge. The same additive constant works for all demands. -/
theorem outer_energy (w : H → E → ℕ) (q : E → ℝ) (hq : ∀ i, 0 < q i)
    {L s : ℕ} (hL : 0 < L) {R H' : ℝ} (hR : 0 ≤ R)
    (hgap : (R + s / (L : ℝ) * widthNorm q (fun _ => 1)) ^ 2 < H')
    (base : ∀ h, widthNorm q (fun e => (w h e : ℝ)) ≤ L * R) :
    ∃ C : ℝ, ∀ (N : ℝ), 0 ≤ N → ∀ v : admitted w (copies N L),
      widthNorm q (fun e => ((v.1 e + copies N L * s : ℕ) : ℝ)) ^ 2 ≤ H' * N^2 + C := by
  obtain ⟨C, hc⟩ := padded_energy_le q hq hL hR hgap
  exact ⟨C, fun N hN v => hc N v.1 hN (payload_norm w q hq base v)⟩

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
