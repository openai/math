import OAI.Computability.BorderVNP.PackedBankPublicNodes
import OAI.Computability.BorderVNP.PackedBottomBoxCharges
import OAI.Computability.BorderVNP.CellPacketInputSize

/-!
# Charging a complete private birth box and its public names separately

The public bank contains the box reference and its cable and port ties.
The expanded account also covers the immutable private table, its sweep
syntax and the actual repeat visits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open CellSparse
open private boxes_words_le from OAI.Computability.BorderVNP.CellPacketInputSize

/-- Separating the public rows from the private table and sweep mass keeps
every word and syntax node of the actual site program in the expanded count. -/
theorem Site.static_le_masses (s : Site) :
    s.staticNodes ≤ s.publicNodes + 6*Packet.storedMass s.directory + s.directory.boxMass + 1 := by
  have h := boxes_words_le s.boxes
  unfold staticNodes publicNodes
  simp only [Packet.fieldList,List.length_cons,Packet.storedMass,Site.directory,
    Directory.tableNodes,Directory.boxMass,sweepMass] at *
  change _ ≤ _ at h
  change _ ≤ _ + (Directory.blockNodes s.directory.blocks+1) + 1
  dsimp only [Site.directory]
  omega

end Packing.Inherited

namespace Packing.BottomRepeat

open Crossing Inherited CellSparse
open scoped Classical

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)
variable (copies capFine stride : ℕ) (box : List Factor)
local notation "s" => bornWith N edges ports v copies capFine stride box

/-- Actual public words, guards and opaque box name are bounded solely by
the number of grouped incidences, independent of the private table and stride. -/
theorem bornWith_publicNodes : (s).publicNodes ≤ 1036*(1+Fintype.card (Row N v)) := by
  have hc : (s).rows.length = 1+Fintype.card (Row N v) := by
    simp [Site.rows,bornWith,ties_length,Nat.add_comm]
  have hf : ((s).rows.flatMap Packet.record).length ≤ 9*(s).rows.length := by
    have words (z : Record) (hz : z ∈ (s).rows) : (Packet.record z).length ≤ 9 := by
      simp only [Site.rows,bornWith,List.reverse_singleton,List.flatten_cons,List.flatten_nil,
        List.append_nil,List.singleton_append,List.mem_cons] at hz
      rcases hz with rfl | hz
      · change 5 ≤ 9; decide
      · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
        rfl
    have aux (rs : List Record) (h : ∀ z ∈ rs, (Packet.record z).length ≤ 9) :
        (rs.flatMap Packet.record).length ≤ 9*rs.length := by
      induction rs with
      | nil => simp
      | cons r rs ih =>
        have hh := h r List.mem_cons_self
        have ht := ih fun u hu => h u (.tail _ hu)
        simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]; omega
    exact aux _ words
  have hm := bornWith_recordMass N edges ports v copies capFine stride box
  change Directory.recordNodes (s).rows + 1 = _ at hm
  change ((s).rows.flatMap Packet.record).length+1+Directory.recordNodes (s).rows+1 ≤ _
  omega

/-- The actual repeated work slab and expanded factor visits are both
bounded by the common capacity for the fine sites and the copy stride. -/
theorem bornWith_expandedLoad (cap : ℕ) (hstride : stride ≤ cap) (hbox : box.length ≤ cap) :
    (s).expandedLoad ≤ copies*(2*cap) := by
  unfold Site.expandedLoad
  rw [bornWith_visits]
  change copies*stride + copies*box.length ≤ _
  rw [← Nat.mul_add]
  apply Nat.mul_le_mul_left
  omega

/-- The one-copy static interpreter cost uses only public incidence rows and
the genuine trivalent factor table and sweep bounds. -/
theorem bornWith_static_charge (cap : ℕ)
    (stored : Packet.storedMass (s).directory ≤ 1+81*cap)
    (sweep : (s).directory.boxMass ≤ 5+810001*cap) :
    (s).staticNodes ≤ 1036*(1+Fintype.card (Row N v)) + 12 + 810487*cap := by
  have h := (s).static_le_masses
  have hp := bornWith_publicNodes N edges ports v copies capFine stride box
  omega

end Packing.BottomRepeat

end BorderVNP
end Computability
end OAI
