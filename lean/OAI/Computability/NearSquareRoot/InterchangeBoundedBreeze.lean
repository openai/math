import OAI.Computability.IntegerMultiplication.Strip.Breeze
import OAI.Computability.NearSquareRoot.InterchangeBQuestLocal
import OAI.Computability.NearSquareRoot.BoundedProductRight
import OAI.Computability.NearSquareRoot.PhysicalWalshRelease

/-!
# Time and space for an interchange on packed records

The same stack program obeys two estimates. The runtime includes the
interchange rate, while its parked trees and working registers fit in the
per-record mass.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangePayload

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.Space NearSquareRoot.InterchangeSpace

variable {I : Type} {r : Regime I} {n l : I → ℕ} {f g : I → ℝ} {p q v : I → Tree}

/-- A P192 stack task with a rate-dependent time bound and a rate-independent space bound. -/
def BoundedBreeze (rate : I → ℝ) (r : Regime I) (n l : I → ℕ) (p q : I → Tree) : Prop :=
  (∀ i, 1 ≤ rate i) ∧ ∃ k, BoundedTask (fun i => ⌈runrate rate r n l k i⌉₊)
    (fun i => ⌈mass r n l k i⌉₊) p q

namespace BoundedBreeze

private theorem mass_le_rate (hr : ∀ i, 1 ≤ f i) (k : ℕ) (i : I) :
    ⌈mass r n l k i⌉₊ ≤ ⌈runrate f r n l k i⌉₊ :=
  Nat.ceil_mono (le_mul_of_one_le_right (by unfold mass; positivity) (hr i))

private theorem at_degree {k j : ℕ} (hr : ∀ i, 1 ≤ f i) (hj : k ≤ j)
    (h : BoundedTask (fun i => ⌈runrate f r n l k i⌉₊) (fun i => ⌈mass r n l k i⌉₊) p q) :
    BoundedTask (fun i => ⌈runrate f r n l j i⌉₊) (fun i => ⌈mass r n l j i⌉₊) p q :=
  h.mono (fun i => Nat.ceil_mono (rate_higher i (hr i) hj))
    (fun i => Nat.ceil_mono (mass_le hj i))

theorem ofRip (h : Rip r n l p q) (hr : ∀ i, 1 ≤ f i) : BoundedBreeze f r n l p q := by
  obtain ⟨k,h⟩ := h
  exact ⟨hr,k,(carries_bounded h).mono (mass_le_rate hr k) (fun _ => le_rfl)⟩

theorem chain (h : BoundedBreeze f r n l p q) (g : BoundedBreeze f r n l q v) :
    BoundedBreeze f r n l p v := by
  obtain ⟨hr,a,h⟩ := h
  obtain ⟨_,b,g⟩ := g
  let k := max a b
  have h' := at_degree hr (show a ≤ k from le_max_left ..) h
  have g' := at_degree hr (show b ≤ k from le_max_right ..) g
  refine ⟨hr,k,(h'.compose g').bound 2 1 (fun i => ?_) (fun i => ?_)⟩
  · omega
  · simp

/-- Apply the task to the right field. Relocating the parked left tree
takes time and space linear in its own size. -/
theorem right (h : BoundedBreeze f r n l p q) (spectator : I → Tree)
    (alive : Alive r n l spectator) :
    BoundedBreeze f r n l (together spectator p) (together spectator q) := by
  obtain ⟨hr,a,h⟩ := h
  obtain ⟨b,D,hs⟩ := rip_volumes alive
  let k := max a b
  have h' := at_degree hr (show a ≤ k from le_max_left ..) h
  have space (i : I) : (spectator i).count ≤ D * ⌈mass r n l k i⌉₊ := by
    rw [ceil_mass]
    exact (hs i).1.trans (Nat.mul_le_mul_left D (massNat_mono _ _ _ (le_max_right ..) i))
  refine ⟨hr,k,(h'.right spectator).bound (D+1) (D+1) (fun i => ?_) (fun i => ?_)⟩
  · have ht := (space i).trans (Nat.mul_le_mul_left D (mass_le_rate hr k i))
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · have hs' := space i
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

private theorem pair_task {t s : I → ℕ} (ht : ∀ i, s i ≤ t i)
    (h : BoundedTask t s p q) (g : BoundedTask t s p v) :
    BoundedTask t s p (together q v) := by
  obtain ⟨C,bounds⟩ := h.endpointSize
  have task := ((BoundedTask.of_time (Task.copy p)).compose (h.left p)).compose (g.right q)
  refine task.bound (2*C+3) (2*C+2) (fun i => ?_) (fun i => ?_)
  · have b := (bounds i).trans (Nat.mul_le_mul_left C (Nat.add_le_add_right (ht i) 1))
    have bp := (le_max_left _ _).trans b
    have bq := (le_max_right _ _).trans b
    rw [Nat.add_mul, Nat.mul_assoc, Nat.two_mul, Nat.succ_mul, Nat.succ_mul, Nat.one_mul]
    omega
  · have bp := (le_max_left _ _).trans (bounds i)
    have bq := (le_max_right _ _).trans (bounds i)
    rw [Nat.add_mul, Nat.mul_assoc, Nat.two_mul, Nat.two_mul]
    omega

/-- Compute both outputs from one input. The bounds on the serialized input
and the first output follow from their occurrence on the certified decks. -/
theorem pair (h : BoundedBreeze f r n l p q) (g : BoundedBreeze f r n l p v) :
    BoundedBreeze f r n l p (together q v) := by
  obtain ⟨hr,a,h⟩ := h
  obtain ⟨_,b,g⟩ := g
  exact ⟨hr,max a b,pair_task (mass_le_rate hr _) (at_degree hr (le_max_left a b) h)
    (at_degree hr (le_max_right a b) g)⟩

theorem raise (h : BoundedBreeze f r n l p q) (hg : ∀ i, f i ≤ g i) :
    BoundedBreeze g r n l p q := by
  obtain ⟨hr,k,h⟩ := h
  refine ⟨fun i => (hr i).trans (hg i),k,h.mono (fun i => Nat.ceil_mono ?_) (fun _ => le_rfl)⟩
  exact mul_le_mul_of_nonneg_left (hg i) (by unfold mass; positivity)

end BoundedBreeze
end InterchangePayload

end NearSquareRoot
end Computability
end OAI
