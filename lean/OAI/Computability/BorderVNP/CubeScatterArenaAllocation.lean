import OAI.Computability.BorderVNP.CubeScatterArenaWordBounds
import OAI.Computability.BorderVNP.RoutingISACubeArena
import OAI.Computability.BorderVNP.CubeISALocalRowGeometrySpace
import OAI.Computability.BorderVNP.CubeISALocalRowRole

/-! # Concrete packet, singleton, team-row source, and checker allocations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources
open CubeHeaderInstall

/-- Team-row ABI with the actual native owner, powers, and directed-view arrays in this arena. -/
def Layout.scanner (a : Layout) (frame team axis selectors : ℕ) : TeamRowPrepare.Layout :=
  ⟨frame,a.header.header,a.header.d,axis,selectors,a.ownerBase,a.pairBase,a.pairStride,team⟩

/-- Order of the immutable arrays installed after the directory of owned vertices. -/
theorem Layout.source_order (a : Layout) : a.publicBase ≤ a.powerBase ∧
    a.powerBase+(a.n+1) ≤ a.ownerBase ∧ a.ownerBase+a.header.d ≤ a.pairBase := by
  simp only [powerBase,ordinalBase,widthBase,dataMean,cableMean,demands,nodes,heads,groupWeights,teamTotals,
    ownerBase,pairBase,TableLayout.reserveEnd,records,hostDirectory,pairDirectory]
  omega

/-- Genuine primary and secondary pointers produce the allocation premises of every
native owned row. The immutable arrays after the vertex directory use the high side
of the preservation bounds. -/
theorem Layout.scanner_allocation (a : Layout) (frame team axis selectors w : ℕ)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (packet : A.packetBase = a.header.packetBase) (single : A.singleBase = a.singleBank)
    (frameLow : frame+112 ≤ a.header.header) (axes : a.header.a = a.n+1)
    (alphabet : 0 < a.header.d) (payload : 0 < a.header.blocks*(a.h*a.b))
    (width : 0 < bankWidth a.n a.b a.h a.K a.s) (fit : a.stop < 2^w)
    (finiteCube : max (Fintype.card (Selector a.n a.K a.h)) (2^(a.n+1)) < 2^w) :
    Allocation A (a.scanner frame team axis selectors) a.powerBase a.vertexBase a.publicBase w := by
  let l := a.scanner frame team axis selectors
  let row := rowLayout A l a.powerBase
  have d : l.d = a.header.d := rfl
  have packetEnd : A.packetBase+(a.header.d*a.header.d)^(a.n+1)*2*a.header.blocks*bankWidth a.n a.b a.h a.K a.s ≤ A.singleBase := by
    rw [packet,single]; unfold Layout.singleBank Layout.packetEnd bankStop; omega
  have singleEnd : A.singleBase+a.header.d^(a.n+1)*a.header.d^(a.n+1)*(a.header.blocks*(a.h*a.b)) = a.vertexBase := by
    simp [single,vertexBase,Layout.alphabet,pow_two]
  have declaration : a.header.header+13+2*(a.header.d*a.header.d*(a.n+1))+(a.n+1) = A.packetBase := by
    simp [packet,Inputs.packetBase,Inputs.entries,axes]
  obtain ⟨_,sv,_,vp,pb,cs⟩ := a.separated
  obtain ⟨powerLow,powerOwner,ownerLow⟩ := a.source_order
  have pv : a.vertexBase ≤ a.publicBase := Nat.le_add_right _ _
  have pstop : a.pairBase ≤ a.stop := (Nat.le_add_right _ _).trans (pb ▸ cs)
  obtain ⟨pr,sr⟩ := bankRooms row w a.n a.b a.h a.K a.s frame A.singleBase a.stop alphabet payload width
    (show frame+112 ≤ A.packetBase by omega) (show a.header.header+13 ≤ A.packetBase by omega)
    (powerOwner.trans ((Nat.le_add_right _ _).trans (ownerLow.trans pstop))) packetEnd
    (singleEnd.le.trans (pv.trans (vp.trans pstop))) fit finiteCube
  exact ⟨pr,sr,packetEnd,singleEnd.le,(vp.trans pstop).trans_lt fit,by change frame+112 ≤ _; omega,
    by change a.header.header+13 ≤ _; omega,declaration.le,Or.inr (powerLow.trans ((Nat.le_add_right _ _).trans powerOwner)),
    Or.inr powerLow,Or.inr vp⟩

/-- Every immutable word of the scanner is outside the exact scratch intervals of
the checker. The source includes the declaration and total rows, group owners,
primary and secondary headers, alphabet powers and every directed view. -/
theorem Layout.scanner_checker_protected (a : Layout) (frame team axis selectors : ℕ)
    (frameLow : frame+112 ≤ a.header.header) (axes : a.header.a = a.n+1) (alphabet : 0 < a.header.d)
    {j : ℕ} (hj : j ∈ source (a.scanner frame team axis selectors) a.powerBase a.n) :
    LocalRow.Protected a.n a.h (a.header.header+13) a.packetEnd j := by
  have declaration : a.header.header+13+2*(a.header.d*a.header.d*(a.n+1))+(a.n+1) = a.header.packetBase := by
    simp [Inputs.packetBase,Inputs.entries,axes]
  have actualLen : a.n+1 ≤ a.header.d*a.header.d*(a.n+1) :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos alphabet alphabet)
  have packetHigh : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right _ _
  obtain ⟨sg,sv,_,vp,_,_⟩ := a.separated
  have pv : a.vertexBase ≤ a.publicBase := Nat.le_add_right _ _
  obtain ⟨powerLow,powerOwner,ownerLow⟩ := a.source_order
  simp only [source,scanner,Set.mem_union,Set.mem_Ico] at hj
  rcases hj with ((decl|own)|(((prim|head)|power)|view)) <;>
    rcases ‹_ ∧ _› with ⟨lo,hi⟩ <;> unfold LocalRow.Protected <;> omega

/-- The entire protected input inventory is below the next fresh arena,
where the signed evaluator installs the fixed cube recipes and table identifiers. -/
theorem Layout.scanner_source_lt (a : Layout) (frame team axis selectors : ℕ)
    (frameLow : frame+112 ≤ a.header.header) (axes : a.header.a = a.n+1)
    {j : ℕ} (hj : j ∈ source (a.scanner frame team axis selectors) a.powerBase a.n) : j < a.stop := by
  have declaration : a.header.header+13+2*(a.header.d*a.header.d*(a.n+1))+(a.n+1) = a.header.packetBase := by
    simp [Inputs.packetBase,Inputs.entries,axes]
  have packetHigh : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right _ _
  have vertexPublic : a.vertexBase ≤ a.publicBase := Nat.le_add_right _ _
  obtain ⟨sg,sv,_,vp,pb,cs⟩ := a.separated
  obtain ⟨powerLow,powerOwner,ownerLow⟩ := a.source_order
  rw [pow_two,Nat.mul_comm (a.header.d*a.header.d) a.pairStride] at pb
  simp only [source,scanner,Set.mem_union,Set.mem_Ico] at hj
  rcases hj with ((decl|own)|(((prim|head)|power)|view)) <;> rcases ‹_ ∧ _› with ⟨lo,hi⟩ <;> omega

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
