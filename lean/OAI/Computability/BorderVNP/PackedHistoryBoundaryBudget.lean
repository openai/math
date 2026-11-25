import OAI.Computability.BorderVNP.PackedHistoryRectangleRange
import OAI.Computability.BorderVNP.PackedHistorySubdivisionCost

/-! # Public costs at the actual input and output rectangles of a site epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.PublicCapacity Crossing Cover Packing TeamScales
open scoped Classical

/-- The logarithmic factors in both boundary compilers are bounded in the same
processor range. The constant includes the fixed multiplier of the machine word. -/
theorem boundary_rowWork (I : Type*) [Fintype I] [Nonempty I] {n r z d w : ℕ}
    (s : Shape) (factor C e : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (volume : s.volume (Fintype.card (I → Deck z)) ≤ r*n) (depth : d≤z)
    (word : w≤factor*logWidth r n) :
    C*(s.sites+s.edges+1)*(d+w+Nat.clog 2 (s.sites+2*s.edges+1)+3)^e ≤
      rowWork (C*(factor+7)^e) (Fintype.card (I → Deck z)) (logWidth r n) e s := by
  have h := boundary_width I (r:=r) (n:=n) (z:=z) (d:=d) (w:=w) s 0 factor hr hn volume (by simpa using depth) word
  have h' : d+w+Nat.clog 2 (s.sites+2*s.edges+1)+3 ≤ (factor+7)*logWidth r n := by simpa using h
  have hx : s.sites+s.edges+1 ≤ s.volume (Fintype.card (I → Deck z)) := by dsimp [Shape.volume]; omega
  calc
    _ ≤ C*s.volume (Fintype.card (I → Deck z))*((factor+7)*logWidth r n)^e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left C hx) (Nat.pow_le_pow_left h' e)
    _ = _ := by unfold rowWork; rw [mul_pow]; ring

/-- Upper bounds on the costs emitted by the two boundary compiler theorems.
These numeric functions refer to the incoming and outgoing site/cable shapes,
so the size proof applies to the same gate lists used for semantic execution. -/
def startCost (q interiors A a copies depth w : ℕ) (s : Shape) : ℕ :=
  1+copies*(300*(s.sites+2*s.edges+1)*
    (Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (Cover.AddressCircuit.ProductSlots q (depth+1))+1)^3 +
    1+(s.subdivide interiors).sites*A*(depth+2)^a+(s.subdivide interiors).edges*(2+3*w)*8)

/-- Cost of the finite minimizing motion circuit and its output route rows. -/
def finishCost (B b depth w : ℕ) (s : Shape) : ℕ :=
  (s.sites+s.edges+1)*B*(depth+w+Nat.clog 2 (s.sites+2*s.edges+1)+3)^b

/-- Uniform rate for the exact bounds of the two compiled boundary gate lists. -/
theorem boundary_costs (I : Type*) [Fintype I] [Nonempty I] (factor q interiors A a B b copies : ℕ) :
    ∃ C e, ∀ {n r z d w : ℕ} (s : Shape), 1 ≤ r → 1 ≤ n →
      s.volume (Fintype.card (I → Deck z)) ≤ r*n → d≤z → w≤factor*logWidth r n →
      startCost q interiors A a copies d w s ≤ rowWork C (Fintype.card (I → Deck z)) (logWidth r n) e s ∧
      finishCost B b d w s ≤ rowWork C (Fintype.card (I → Deck z)) (logWidth r n) e s := by
  obtain ⟨J,j,pre⟩ := RouteRows.subdivision_work_le q interiors A a copies
  refine ⟨J*(factor+7)^j+B*(factor+7)^b,max j b,?_⟩
  intro n r z d w s hr hn vol hd hw
  have hL : 1 ≤ logWidth r n := by
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr] : 2 ≤ 2*n*r)).trans' (by decide)
  have lift {u U C' C : ℕ} (hu : u≤U) (hC : C'≤C) : rowWork C' (Fintype.card (I → Deck z)) (logWidth r n) u s ≤
      rowWork C (Fintype.card (I → Deck z)) (logWidth r n) U s :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ hC) (Nat.pow_le_pow_right hL hu)
  refine ⟨(pre d w s).trans ?_,?_⟩
  · exact (boundary_rowWork I s factor J j hr hn vol hd hw).trans (lift (le_max_left ..) (Nat.le_add_right ..))
  · unfold finishCost
    rw [Nat.mul_comm (s.sites+s.edges+1) B]
    exact (boundary_rowWork I s factor B b hr hn vol hd hw).trans (lift (le_max_right ..) (Nat.le_add_left ..))

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
