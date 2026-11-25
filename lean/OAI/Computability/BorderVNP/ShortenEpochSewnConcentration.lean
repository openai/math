import OAI.Computability.BorderVNP.ShortenEpochProfileWidth
import OAI.Computability.BorderVNP.ShortenEpochStep

/-!
# Concentration of the actual sewn profile

After normalizing by the input multiplicity, the count of every output
tile satisfies the bounded-neighbor estimate with one fixed expansion
constant. Equation (6.2) then gives the concentration part of (6.3)
for the joint histogram's real physical pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Epoch Crossing Finset
open scoped Classical

variable {D m : ℕ} {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable {T B : Type} [Fintype T] [Fintype B]

/-- The second estimate in (6.3) with the left-hand side computed from
the eligible physical edges of the concrete simultaneous profile replacement.
Eligibility can select precisely the positive-length charged segments whose
midpoint lies in the given output tile. -/
theorem sewnProfile_concentration (e : PaidIdentity K D m) (j : T × B → ℕ)
    {p : Pack D P bits K} (t : AddressPartition p.layout (T × B))
    (b : ∀ a, Bundle p.layout (t.part a) (j a*m)) (q : ProfileCounts e j)
    (active : p.layout.Edge → Prop) (addr : p.layout.Edge → T × B) (donor : Equiv.Perm (T × B))
    (near : T → Finset (T × B)) (post : T → (sewnProfile e j t b q).Edge → Prop)
    (hretain : ∀ o (x : {x : p.layout.Edge // x ∉ t.selected}), post o (.inr (.inl x)) →
      active x.val ∧ addr x.val ∈ near o)
    (hhook : ∀ o a k, post o (.inl (t.includePort a k)) → donor a ∈ near o)
    (hnew : ∀ o a x, post o (.inr (.inr ⟨a,x⟩)) → donor a ∈ near o)
    (hwidth : ∀ a, j a ≤ addressWidth p.layout.width active addr (donor a))
    (fanIn fanOut : ℕ) (hIn : ∀ o, (near o).card ≤ fanIn)
    (hOut : ∀ a, (univ.filter fun o => a ∈ near o).card ≤ fanOut)
    (g : T × B → ℝ) {k W err : ℝ} (hk : 0 < k)
    (hmean : Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy g) ≤ W)
    (hdev : Real.sqrt (Fintype.card T) * Real.sqrt
      (binEnergy fun a => addressWidth p.layout.width active addr a / k - g a) ≤ err) :
    Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy (fun o =>
      testedWidth (sewnProfile e j t b q).width (post o) / k)) ≤
      ((1 + profileWidthBound e : ℕ) : ℝ) * Real.sqrt ((fanIn : ℝ) * fanOut) * (W + err) := by
  let G : ℝ := (1 + profileWidthBound e : ℕ)
  let s (a : T × B) : ℝ := addressWidth p.layout.width active addr a / k
  let x (o : T) : ℝ := testedWidth (sewnProfile e j t b q).width (post o) / k
  have hG : 0 < G := by dsimp [G]; positivity
  have hx (o : T) : 0 ≤ x o / G := by dsimp [x]; positivity
  have hload (o : T) : x o / G ≤ ∑ a ∈ near o, s a := by
    have h := sewnProfile_width_le e j t b q active addr donor (near o) (post o)
      (hretain o) (hhook o) (hnew o) hwidth
    have hcast : (testedWidth (sewnProfile e j t b q).width (post o) : ℝ) ≤
        G * ∑ a ∈ near o, (addressWidth p.layout.width active addr a : ℝ) := by
      dsimp only [G]
      exact_mod_cast h
    rw [div_le_iff₀ hG]
    dsimp only [x,s]
    rw [← Finset.sum_div]
    calc
      _ ≤ (G * ∑ a ∈ near o, (addressWidth p.layout.width active addr a : ℝ)) / k :=
        div_le_div_of_nonneg_right hcast hk.le
      _ = _ := by ring
  have h := normalized_concentration near s g (fun o => x o / G) fanIn fanOut
    hx hload hIn hOut hmean hdev
  have henergy : binEnergy (fun o => x o / G) = binEnergy x / G^2 := by
    simp only [binEnergy, div_pow, Finset.sum_div]
  have hsqrt : Real.sqrt (binEnergy (fun o => x o / G)) = Real.sqrt (binEnergy x) / G := by
    rw [henergy,Real.sqrt_div (show 0 ≤ binEnergy x from sum_nonneg fun _ _ => sq_nonneg _), Real.sqrt_sq hG.le]
  rw [hsqrt, ← mul_div_assoc, div_le_iff₀ hG] at h
  change Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy x) ≤ G * _ * _
  calc
    _ ≤ (Real.sqrt ((fanIn : ℝ) * fanOut) * (W+err)) * G := h
    _ = _ := by ring

end Shortening

end BorderVNP
end Computability
end OAI
