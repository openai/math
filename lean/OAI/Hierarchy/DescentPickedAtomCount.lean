import OAI.Hierarchy.DescentNetworkWorld

namespace OAI
/-! # Bounding all newly born matrix atoms by the widths of the actually picked core wires -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {n : ℕ} {P : Type*} {bits : P→ℕ} {I : Type} [Fintype I]
variable (W : MarkedWorld F n P bits) (pick : I×Fin 2 ↪ W.graph.Edge)

omit [Field F] in
theorem picked_width_sum (picked : ∀t,pick t∈W.core) :
    (∑t : I×Fin 2,W.graph.width (pick t))≤W.liveWidth := by
  have sub : Finset.univ.map pick⊆W.core := by
    intro e he
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp he
    exact picked t
  unfold liveWidth
  simpa using Finset.sum_le_sum_of_subset (f:=W.graph.width) sub

omit [Field F] in
/-- Valid also when there are no usable pairs. Positive width is only needed for the quotient form. -/
theorem paired_count_width (picked : ∀t,pick t∈W.core) (z b : ℕ)
    (fit : ∀i s,W.graph.width (pick (i,s))=z*b) :
    Fintype.card I*(2*(z*b)) ≤ W.liveWidth := by
  have widths (t : I×Fin 2) : W.graph.width (pick t)=z*b := fit t.1 t.2
  simpa [widths,Nat.mul_assoc] using picked_width_sum W pick picked

omit [Field F] in
theorem paired_count_le (picked : ∀t,pick t∈W.core) (z b : ℕ) (hp : 0<z*b)
    (fit : ∀i s,W.graph.width (pick (i,s))=z*b) :
    Fintype.card I ≤ W.liveWidth/(2*(z*b)) :=
  (Nat.le_div_iff_mul_le (by omega)).mpr (paired_count_width W pick picked z b fit)

omit [Field F] in
/-- A single global history price pays each installed party exactly once. -/
theorem paired_birth_bill (picked : ∀t,pick t∈W.core) (z b : ℕ) (_hp : 0<z*b)
    (fit : ∀i s,W.graph.width (pick (i,s))=z*b) :
    (6*Fintype.card I)*(z*b)≤3*W.liveWidth := by
  have h := Nat.mul_le_mul_left 3 (paired_count_width W pick picked z b fit)
  exact (show 6*Fintype.card I*(z*b)=3*(Fintype.card I*(2*(z*b))) by ring).le.trans h

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
