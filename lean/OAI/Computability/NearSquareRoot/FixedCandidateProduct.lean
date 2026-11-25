import OAI.Computability.NearSquareRoot.FixedCandidateFrame

/-! # The physical pointwise product between the two transform calls -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code FixedPoint DigitPacking Space

def productClock (n : ℕ) := (capacity n+1)*GridTask.recordCost (addressBits n)

private abbrev Packet := Tally × List Dusk.Pair

private def alignProduct (p : Packet × Packet) := (p.1.1, p.1.2, p.2.2)

/-- One bounded command drops the redundant input-length ruler, then applies
the pointwise product pass while keeping the remaining ruler for the inverse transform. -/
theorem spectralProduct {I : Type} (n t : I → ℕ) (hn : ∀ i, 2 ≤ n i) (hnt : ∀ i, n i ≤ t i)
    (ht : ∀ i, productClock (n i) ≤ t i) (x y : (i : I) → Array (n i)) :
    BoundedTask t n (fun i => .fork (framed (x i)) (framed (y i)))
      (fun i => framed (fun j => FixedPoint.multiply (addressBits (n i)) (x i j) (y i j))) := by
  let arg i := ((tally (n i), records (x i)), (tally (n i), records (y i)))
  have align : Easy alignProduct := by unfold alignProduct; fun_prop
  have ha := BoundedTask.of_time (align.on arg)
  have sz (i : I) : size (arg i) ≤ 150001*(n i+1) := by
    change ((Tree.fork (framed (x i)) (framed (y i))).count) ≤ _
    simp only [Tree.count]
    have := framed_size (hn i) (x i)
    have := framed_size (hn i) (y i)
    omega
  have h₁ := ha.bound (time' := t) (space' := n) 150002 300003
    (fun i => by change size (arg i)+1 ≤ _; have := sz i; have := hnt i; omega)
    (fun i => by change size (arg i)+size (arg i)+1 ≤ _; have := sz i; omega)
  have pr := ProductPass.pointwiseSeparate (fun i => capacity (n i)) (fun i => addressBits (n i)) x y (fun _ => rfl)
  have h₂ := (pr.right (fun i => send (tally (n i)))).bound (time' := t) (space' := n) 4 196
    (fun i => by
      change size (tally (n i)) + productClock (n i) + 1 ≤ _
      rw [size_tally, tally_length]
      have := ht i; have := hnt i; omega)
    (fun i => by
      change (capacity (n i)+1)*(addressBits (n i)+1)+size (tally (n i))+1 ≤ _
      rw [size_tally, tally_length]
      have := array_volume (hn i); omega)
  exact sequence h₁ h₂

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
