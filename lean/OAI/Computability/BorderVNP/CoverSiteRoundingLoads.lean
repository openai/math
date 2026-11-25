import OAI.Computability.BorderVNP.CoverSiteMotionNeighbors
import OAI.Computability.BorderVNP.ShortenEpochConcentration
import OAI.Computability.BorderVNP.ShortenEpochLocality

/-!
# Concentration and retained records after rounding

Each input record has a center and a nonnegative mass. Its copies (the two
endpoints for a charged wire, or a single retained record) lie at bounded
distance from that center. Actual geometric tile neighborhoods bound both
the maximum final tile load and the normalized squared-load concentration.
Dropping the wires that round locally only decreases the endpoint counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Finset BorderVNP.Cover.Frame

/-- Sum of the masses of records with a given address. -/
noncomputable def tileMass {E T : Type*} [Fintype E] [DecidableEq T]
    (loc : E → T) (mass : E → ℝ) (t : T) : ℝ :=
  ∑ e, if loc e = t then mass e else 0

/-- Concentration norm in the paper, scaled by the square root of the number of tiles. -/
noncomputable def tileConcentration {T : Type*} [Fintype T] (mass : T → ℝ) : ℝ :=
  Real.sqrt (Fintype.card T) * Real.sqrt (Epoch.binEnergy mass)

private theorem tileMass_nonneg {E T : Type*} [Fintype E] [DecidableEq T]
    (loc : E → T) {m : E → ℝ} (hm : ∀ e, 0 ≤ m e) (t : T) : 0 ≤ tileMass loc m t := by
  apply sum_nonneg
  intro e _
  split_ifs <;> simp [hm]

private theorem tileMass_local {E S T : Type*} [Fintype E] [DecidableEq S] [DecidableEq T]
    (src : E → S) (dest : E → T) (m n : E → ℝ) (hm : ∀ e, 0 ≤ m e)
    (hn : ∀ e, n e ≤ m e) (near : T → Finset S) (h : ∀ e, src e ∈ near (dest e)) (t : T) :
    tileMass dest n t ≤ ∑ s ∈ near t, tileMass src m s := by
  simp only [tileMass]
  rw [sum_comm]
  apply sum_le_sum
  intro e _
  by_cases he : dest e = t
  · have hs := he ▸ h e
    simpa [he,hs] using hn e
  · simp [he]
    split_ifs <;> simp [hm]

private theorem duplicateMass {W J T : Type*} [Fintype W] [Fintype J] [DecidableEq T]
    (src : W → T) (width : W → ℝ) (s : T) :
    tileMass (fun p : W × J => src p.1) (fun p => width p.1) s =
      (Fintype.card J : ℝ) * tileMass src width s := by
  simp [tileMass, Fintype.sum_prod_type, mul_sum]

/-- Uniform estimates for moving a bounded number of copies of each record. The choice
`J = Bool` gives both ends of every wire. The choice `J = Unit` gives the per-tile
descriptor and expanded-weight bounds for all retained data. -/
theorem rounding_load_bounds (ρ : ℝ) (a q : ℕ) : ∃ N : ℕ,
    ∀ d (g : Fin q → SL) (hg : ∀ k, Clears (g k) a)
      {W J : Type*} [Fintype W] [Fintype J] (width : W → ℝ) (charge : W × J → ℝ),
      (∀ w, 0 ≤ width w) → (∀ p, 0 ≤ charge p ∧ charge p ≤ width p.1) →
      ∀ (center : W → Fin q → Surface (d+2+2*a))
        (point : W × J → Fin q → Surface (d+2+2*a)),
        (∀ p k, dist (center p.1 k) (point p k) ≤ ρ) →
        let src (w : W) (k : Fin q) := addressAt (d+2+2*a) (by omega) (center w k)
        let dest (p : W × J) (k : Fin q) := surfaceAddress (d+1) (surfaceMotion (hg k) (d+2) (point p k))
        (∀ M ≥ (0:ℝ), (∀ s, tileMass src width s ≤ M) →
          ∀ t, tileMass dest charge t ≤ (N:ℝ)*Fintype.card J*M) ∧
        tileConcentration (tileMass dest charge) ≤
          (N:ℝ)*Fintype.card J * tileConcentration (tileMass src width) := by
  classical
  obtain ⟨N,hN⟩ := product_motion_neighbors ρ a q
  refine ⟨N,?_⟩
  intro d g hg W J _ _ width charge hw hp center point hdist src dest
  obtain ⟨near,hin,hout,hrel⟩ := hN d g hg
  let old := tileMass src width
  let new := tileMass dest charge
  let c : ℝ := Fintype.card J
  have hl (t) : new t ≤ ∑ s ∈ near t, c * old s := by
    have h := tileMass_local (fun p : W × J => src p.1) dest (fun p => width p.1) charge
      (fun p => hw p.1) (fun p => (hp p).2) near
      (fun p => hrel (center p.1) (point p) (hdist p)) t
    simpa only [duplicateMass,old,c] using h
  have hc : 0 ≤ c := by positivity
  constructor
  · intro M hM hcap t
    calc
      _ ≤ ∑ s ∈ near t, c*old s := hl t
      _ ≤ ∑ _s ∈ near t, c*M := sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hcap s) hc
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hin t) (mul_nonneg hc hM)
  · have e := Epoch.sum_sq_locality near (fun s => c*old s) new N N
      (tileMass_nonneg dest (fun p => (hp p).1)) hl hin hout
    have he : Epoch.binEnergy new ≤ ((N:ℝ)*c)^2 * Epoch.binEnergy old := by
      simp only [mul_pow, ← mul_sum] at e
      simpa [Epoch.binEnergy, pow_two, mul_assoc, mul_left_comm, mul_comm] using e
    have hs := Real.sqrt_le_sqrt he
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hc)] at hs
    have hcard : Fintype.card (Fin q → Deck (d+2)) ≤ Fintype.card (Fin q → Deck (d+2+2*a)) :=
      Fintype.card_le_of_surjective _ (productReduction_surjective q (by omega))
    have hroot := Real.sqrt_le_sqrt (show (Fintype.card (Fin q → Deck (d+2)) : ℝ) ≤
      Fintype.card (Fin q → Deck (d+2+2*a)) by exact_mod_cast hcard)
    change Real.sqrt _ * Real.sqrt (Epoch.binEnergy new) ≤ (N:ℝ)*c * (Real.sqrt _ * Real.sqrt (Epoch.binEnergy old))
    calc
      _ ≤ Real.sqrt (Fintype.card (Fin q → Deck (d+2+2*a))) * ((N:ℝ)*c * Real.sqrt (Epoch.binEnergy old)) :=
        mul_le_mul hroot hs (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by ring

end Cover

end BorderVNP
end Computability
end OAI
