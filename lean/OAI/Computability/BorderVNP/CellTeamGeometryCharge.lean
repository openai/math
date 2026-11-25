import OAI.Computability.BorderVNP.CellPacketGeometryFixedReferences
import OAI.Computability.BorderVNP.CellTeamReportCharge
import OAI.Computability.BorderVNP.CellPacketGeometryTotals
import OAI.Computability.BorderVNP.GeometryAdviceCharge

/-! # Public words, delivered sites and supplemental bindings of a team

The public words and the reserved descriptors are disjoint sections of the
true sparse geometry arrays. Delivered one-copy strings and bottom bundles
are indexed by their actual source ordinals. The additional count vectors
charge their existing public address words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry Cube.TeamRowClock DiagonalTallyCellReports
open scoped Classical

/-- Restriction of an actual group load to the team's selected cells. -/
theorem assigned_eq_sum {I : Type*} [Fintype I] (owner : I → ℕ) (team : ℕ) (f : I → ℕ) :
    assignedSum owner team f = ∑ i ∈ Finset.univ.filter (fun i => owner i=team), f i := by
  rw [assignedSum,Finset.sum_filter]

/-- Each selected item ordinal occurs once in its declared delivery range. -/
theorem delivered_ordinals {C A : Type*} [Fintype C] [Fintype A]
    (owner : C → ℕ) (team desc : ℕ) (num : C → ℕ) (recv : A → C) (width : A → ℕ)
    (item : ((c : C) × Fin (num c)) ↪ A) (route : ∀ c j, recv (item ⟨c,j⟩)=c)
    (span : ∀ c j, desc ≤ width (item ⟨c,j⟩)) :
    desc*assignedSum owner team num ≤ assignedSum (owner ∘ recv) team width := by
  let I := (c : C) × Fin (num c)
  have h := assignedSum_subitems item (fun x : I => x.1) recv owner team (fun _ => desc) width
    (fun x => route x.1 x.2) (fun x => span x.1 x.2)
  apply le_trans _ h
  rw [assignedSum,assignedSum,Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  by_cases own : owner c=team
  · simp [own,Nat.mul_comm]
  · simp [own]

/-- The word count of the geometry packet pays for both of the physical sorts,
including the bit-width cost of examining a public word in a cell initializer. -/
theorem geometry_words_le_ticks (p d k u b w : ℕ) (hb : 1 ≤ b) (hw : 1 ≤ w) :
    (w+1)*(2^p+2^d) ≤ GeometryAdviceRate.ticks k u (Total p d) b w := by
  let o := Total p d
  have oSize : o = 2*(2^p+2^d) := by dsimp [o,Total]; ring
  have oBits : o ≤ o*b := Nat.le_mul_of_pos_right _ hb
  have words : o ≤ GeometryAdviceRate.packetWords k u o b := by unfold GeometryAdviceRate.packetWords; omega
  have copies : 1 ≤ GeometryAdvice.copyStripeBit.slots+1 := by omega
  have stripe := Nat.mul_le_mul (Nat.mul_le_mul_right w words) copies
  have base : (w+1)*(2^p+2^d) ≤ (o*w)*1 := by
    rw [oSize,mul_one]
    have c : 2^p+2^d ≤ (2^p+2^d)*w := Nat.le_mul_of_pos_right _ hw
    nlinarith only [c]
  apply base.trans (stripe.trans ?_)
  unfold GeometryAdviceRate.ticks
  change _ ≤ GeometryAdvice.beginStripe.slots + GeometryAdviceRate.packetWords k u o b*w*(GeometryAdvice.copyStripeBit.slots+1)+1+
    GeometryAdvicePrepare.stageTicks u k (GeometryAdviceRate.packetWords k u o b) w+GeometryOutput.ticks o b
  omega

/-- Agreement of the real per-cell public fields with their shared live geometry
sections. The four fields come from the frozen merged site streams. -/
structure SourceShape {Site S : Type} {C : ℕ} (p : Fin C → Placed Site) (D : SiteWords.Directory S Site C) : Prop where
  privateWires : ∀ c, (p c).privateWires=D.privateWires c
  boxes : ∀ c, (p c).boxes=D.cellBoxes c
  records : ∀ c, (p c).rows=D.cellRecords c
  reports : ∀ c, (p c).reports=D.reports c

/-- The public sort pays the full word count, and the descriptor sort pays
the box count of each cell. These counts allow a stable reorder of public
records within a cell, as performed by the frozen history emitter. -/
structure SourceFootprint {Site J : Type} {C : ℕ} (p : Fin C → Placed Site) (D : SiteWords.Directory J Site C) : Prop where
  /-- Total number of actual published source packet words. -/
  publicWords : (∑ c, ((p c).parts.flatMap Part.publicBuffer).length)=D.words.length
  /-- Actual one-copy box count at each original cell. -/
  boxes : ∀ c, (p c).boxes.length=(D.cellBoxes c).length

/-- Pointwise typed source replay supplies the public footprint immediately. -/
theorem SourceShape.footprint {Site J : Type} {C : ℕ} {p : Fin C → Placed Site} {D : SiteWords.Directory J Site C}
    (source : SourceShape p D) : SourceFootprint p D :=
  ⟨by simpa only [Placed.parts,source.privateWires,source.boxes,source.records,source.reports] using D.public_sum,
    fun c => congrArg List.length (source.boxes c)⟩

/-- Actual public field counts and all base and spare descriptors of the owned
cell array are bounded by the two geometry sort sizes. -/
theorem geometry_counts_of_footprint {s C p d : ℕ} {E I Site : Type}
    (T : LiveWords.Template E I Site s C) (cell : Fin s → Fin C) (args : E → ℕ) (fields : Fin s → I → ℕ)
    (places : Fin C → Placed Site) (shape : SourceFootprint places (T.directory cell args fields))
    (fit : C+T.atoms.length+C ≤ 2^p) (space : C+(Schema.coords T.chunkLabels.length).length+C ≤ 2^d)
    (owner : Fin C → ℕ) (team : ℕ) :
    assignedSum owner team (fun c => ((places c).parts.flatMap Part.publicBuffer).length) ≤ 2^p ∧
      assignedSum owner team (fun c => (places c).boxes.length+6) ≤ 2^d := by
  let selected := Finset.univ.filter fun c => owner c=team
  let D := T.directory cell args fields
  have total := shape.publicWords.trans (T.wordCapacity cell args fields)
  have pub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ selected)
    (fun c _ _ => Nat.zero_le (((places c).parts.flatMap Part.publicBuffer).length))
  have paid := pub.trans_eq total
  have headers := T.descriptors_sum_le cell args fields space selected
  rw [assigned_eq_sum,assigned_eq_sum]
  constructor
  · exact paid.trans (by omega)
  · apply le_trans _ headers
    apply Finset.sum_le_sum
    intro c _
    change (places c).boxes.length+6 ≤ 3*((plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).length+3)
    rw [shape.boxes c]
    change (D.cellBoxes c).length+6 ≤ _
    simp [plan]
    omega


/-- Actual public field counts and all base and spare descriptors of the owned
cell array are bounded by the two geometry sort sizes. -/
theorem geometry_counts {s C p d : ℕ} {E I Site : Type}
    (T : LiveWords.Template E I Site s C) (cell : Fin s → Fin C) (args : E → ℕ) (fields : Fin s → I → ℕ)
    (places : Fin C → Placed Site) (shape : SourceShape places (T.directory cell args fields))
    (fit : C+T.atoms.length+C ≤ 2^p) (space : C+(Schema.coords T.chunkLabels.length).length+C ≤ 2^d)
    (owner : Fin C → ℕ) (team : ℕ) :
    assignedSum owner team (fun c => ((places c).parts.flatMap Part.publicBuffer).length) ≤ 2^p ∧
      assignedSum owner team (fun c => (places c).boxes.length+6) ≤ 2^d :=
  geometry_counts_of_footprint T cell args fields places shape.footprint fit space owner team

/-- The physical owner scan stops before the terminal emitter's spare row.
Give this sentinel a different owner to restrict the emitted buffer counts
exactly to the actual cells, including when there are no real cells. -/
theorem real_geometry_counts_of_footprint {s C p d : ℕ} {E I Site : Type} (T : LiveWords.Template E I Site s (C+1))
    (cell : Fin s → Fin (C+1)) (arg : E → ℕ) (fields : Fin s → I → ℕ) (places : ℕ → Placed Site)
    (shape : SourceFootprint (fun c : Fin (C+1) => places c.val) (T.directory cell arg fields))
    (pf : (C+1)+T.atoms.length+(C+1) ≤ 2^p)
    (df : (C+1)+(Schema.coords T.chunkLabels.length).length+(C+1) ≤ 2^d)
    (owner : Fin C → ℕ) (team : ℕ) :
    assignedSum owner team (fun c => ((places c.val).parts.flatMap Part.publicBuffer).length) ≤ 2^p ∧
      assignedSum owner team (fun c => (places c.val).boxes.length+6) ≤ 2^d := by
  let full : Fin (C+1) → ℕ := Fin.lastCases (team+1) owner
  have eqn (size : ℕ → ℕ) : assignedSum full team (fun c => size c.val) = assignedSum owner team (fun c => size c.val) := by
    unfold assignedSum
    rw [Fin.sum_univ_castSucc]
    simp only [full,Fin.lastCases_castSucc,Fin.val_castSucc,Fin.lastCases_last,Nat.add_one_ne_self,ite_false,add_zero]
  obtain ⟨pub,box⟩ := geometry_counts_of_footprint T cell arg fields (fun c => places c.val) shape pf df full team
  exact ⟨(eqn (fun c => ((places c).parts.flatMap Part.publicBuffer).length)).symm.trans_le pub,
    (eqn (fun c => (places c).boxes.length+6)).symm.trans_le box⟩

/-- Restriction to emitted real cells of an exactly replayed public directory. -/
theorem real_geometry_counts {s C p d : ℕ} {E I Site : Type} (T : LiveWords.Template E I Site s (C+1))
    (cell : Fin s → Fin (C+1)) (arg : E → ℕ) (fields : Fin s → I → ℕ) (places : ℕ → Placed Site)
    (shape : SourceShape (fun c : Fin (C+1) => places c.val) (T.directory cell arg fields))
    (pf : (C+1)+T.atoms.length+(C+1) ≤ 2^p)
    (df : (C+1)+(Schema.coords T.chunkLabels.length).length+(C+1) ≤ 2^d)
    (owner : Fin C → ℕ) (team : ℕ) :
    assignedSum owner team (fun c => ((places c.val).parts.flatMap Part.publicBuffer).length) ≤ 2^p ∧
      assignedSum owner team (fun c => (places c.val).boxes.length+6) ≤ 2^d :=
  real_geometry_counts_of_footprint T cell arg fields places shape.footprint pf df owner team

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
