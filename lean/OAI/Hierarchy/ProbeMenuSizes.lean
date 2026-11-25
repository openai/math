import OAI.Hierarchy.ProbeStripMenuDebitFields
import OAI.Hierarchy.ProbePhysicalCatalogue

namespace OAI
/-! # Fixed numerical bounds for the two original finite packet menus -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open AdaptiveProbe
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical BigOperators

namespace PacketWidths
variable {J K : Type*} [Fintype J] [Fintype K]

def alphabet (s : PacketWidths J) := Finset.univ.sup s.selector

def maximum (s : PacketWidths J) := Finset.univ.sup s.entries

def copiesAt (s : PacketWidths J) (scale width : ℕ) := width/(scale*commonWidth s.width)

theorem alphabet_ge (s : PacketWidths J) (i : J) : s.selector i≤ s.alphabet :=
  Finset.le_sup (Finset.mem_univ i)

theorem maximum_ge (s : PacketWidths J) (i : J) : s.entries i≤ s.maximum :=
  Finset.le_sup (Finset.mem_univ i)

theorem copy_bounds (s : PacketWidths J) (i : J) (scale width : ℕ)
    (positive : 0<s.width i) (base : 0<scale) :
    copied (scale*commonWidth s.width) (s.width i) width ≤ s.copiesAt scale width ∧
      s.copiesAt scale width ≤ copied scale (s.width i) width :=
  common_copies_sandwich s.width i scale width positive base

end PacketWidths
namespace StripDirectory
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→ Chord s} {req : A→E}
  {box : Set (E→ℝ)} {ε tree : ℝ} {N q : ℕ}

theorem cap_debit (m : Probe.FixedMenu F edge req box ε tree N) (j : m.index) (e : E) :
    useBits m j e≤(PacketWidths.ofMenu m).entries j := by
  let X := {a : Probe.PositiveDemand req j.val.val // req a.val=e}
  have embed : Function.Injective (fun a : X=>a.val.val) := fun x y h=>Subtype.ext (Subtype.ext h)
  have hcard := Fintype.card_le_of_injective (fun a : X=>a.val.val) embed
  exact (Nat.mul_le_mul_left (m.packet j).width hcard).trans (Nat.le_add_left _ _)

theorem cap_wire (m : Probe.FixedMenu F edge req box ε tree N) (j : m.index) (e : E) (i : Fin q) :
    installedBits m j e i≤(PacketWidths.ofMenu m).entries j := by
  unfold installedBits
  split
  · rename_i real
    exact (Finset.le_sup (f:=fun p : Fin (m.packet j).terms×E=>(m.packet j).count p.1 p.2)
      (Finset.mem_univ (⟨i.val,real⟩,e))).trans (Nat.le_add_right _ _)
  · exact Nat.zero_le _

end StripDirectory
end Hierarchy.ProtocolRAM
end

end OAI
