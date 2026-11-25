import OAI.Computability.NearSquareRoot.KernelPassRectPencil

/-! # Bounding the child calls by incidences of the rectangle family -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect

open Finset
open scoped BigOperators

variable {A : ℕ} {L W J F C : Type} [Fintype L] [Fintype W] [Fintype J] [Fintype F] [Fintype C]
variable [DecidableEq L] [DecidableEq W]

omit [DecidableEq W] in
private theorem side_cost (side : F → Finset L) (work : F → L → ℕ) (d n : ℕ)
    (hd : ∀ f v, v ∈ side f → work f v ≤ d)
    (hn : ∀ v, (univ.filter fun f => v ∈ side f).card ≤ n) :
    (∑ f, ∑ v ∈ side f, work f v) ≤ d * (Fintype.card L * n) := by
  calc
    _ ≤ ∑ f, ∑ v ∈ side f, d := sum_le_sum fun f _ => sum_le_sum fun v hv => hd f v hv
    _ = ∑ v : L, ∑ f, if v ∈ side f then d else 0 := by
      rw [sum_comm]
      simp
    _ ≤ ∑ _ : L, d*n := sum_le_sum fun v _ => by
      simpa [Finset.sum_ite, Nat.mul_comm d] using Nat.mul_le_mul_right d (hn v)
    _ = _ := by simp [Nat.mul_left_comm]

/-- Per-label incidences and the total number of charged rectangles bound the
cost with no factor of the query count on the free-rectangle term. -/
theorem calls_pencil_le (Frees : F → FreeData A L J) (Charged : C → ChargedData A L J)
    (B₀ : W → W → Coefficient) (B : J → W → W → Coefficient) (d n t : ℕ)
    (hsrc : ∀ r v, v ∈ (Frees r).sources → ((Frees r).source v).calls ≤ d)
    (hdst : ∀ r w, w ∈ (Frees r).destinations → ((Frees r).target w).calls ≤ d)
    (hpaid : ∀ r j, ((Charged r).common j).calls ≤ d)
    (nsrc : ∀ v, (univ.filter (fun r => v ∈ (Frees r).sources)).card ≤ n)
    (ndst : ∀ w, (univ.filter (fun r => w ∈ (Frees r).destinations)).card ≤ n)
    (nt : Fintype.card C ≤ t) :
    (pencil Frees Charged B₀ B).calls ≤
      d * Fintype.card W * (2 * Fintype.card L * n + Fintype.card J * t) := by
  rw [calls_pencil]
  have hs := side_cost (fun r => (Frees r).sources) _ d n hsrc nsrc
  have ht := side_cost (fun r => (Frees r).destinations) _ d n hdst ndst
  rw [← mul_sum, sum_add_distrib]
  have hp : (∑ c, ∑ j, Fintype.card W * ((Charged c).common j).calls) ≤
      t * (Fintype.card J * (Fintype.card W * d)) := by
    calc
      _ ≤ ∑ _ : C, ∑ _ : J, Fintype.card W * d := sum_le_sum fun c _ =>
        sum_le_sum fun j _ => Nat.mul_le_mul_left _ (hpaid c j)
      _ = Fintype.card C * (Fintype.card J * (Fintype.card W * d)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ nt
  calc
    _ ≤ Fintype.card W * (d * (Fintype.card L * n) + d * (Fintype.card L * n)) +
        t * (Fintype.card J * (Fintype.card W * d)) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add ht hs)) hp
    _ = _ := by ring

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI
