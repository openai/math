import OAI.Computability.BorderVNP.CellPacketGeometryReserved
import OAI.Computability.BorderVNP.CellPacketGeometryLiveTemplate

/-! # The exclusive end address and static report width of each sparse cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open CellSparse CellSparse.Packet
open private selected_eq from OAI.Computability.BorderVNP.CellPacketGeometryReserved

variable {C p d H dest : ℕ} {S Orig E : Type} {D : SiteWords.Directory S Orig C}
variable {pin : Orig → E} {arg : E → ℕ} {mem : ℕ → ℕ}
variable {fit : C+D.words.length+C ≤ 2^p} {space : C+(coords (D.referenceRows pin).length).length+C ≤ 2^d}
variable {π : Equiv.Perm (Fin (2^p))}

/-- The actual stop marker is strictly after the start, and it is the exclusive
end of the native three-word descriptor interval, even for a cell with no sites. -/
theorem Buffers.descriptor_end
    (h : Buffers D fit space dest H (fun i => ((D.referenceRows pin).get i).2)
      (fun i => ((D.referenceRows pin).get i).1) arg mem π) (c : Fin C) :
    let bank := descriptorBank dest p
    let lo := Markers.start space c
    let hi := Markers.stop space c
    let r := sectionRange mem bank lo hi
    mem (bank+(2^d+lo.val)) < mem (bank+(2^d+hi.val)) ∧
      r.1+r.2 = bank+mem (bank+(2^d+hi.val)) := by
  intro bank lo hi r
  have len := (h.chunks c).1
  rw [selected_eq] at len
  change mem (bank+(2^d+hi.val))-mem (bank+(2^d+lo.val))-1 = _ at len
  simp only [List.length_append,List.length_cons,List.length_nil] at len
  change _ ∧ bank+mem (bank+(2^d+lo.val))+1+(mem (bank+(2^d+hi.val))-mem (bank+(2^d+lo.val))-1) = _
  omega

end CellPacketGeometry.Schema

namespace CellPacketGeometry.LiveWords

open CellSparse CellSparse.Packet

variable {E I Orig : Type} {s C : ℕ}

/-- The numeric report addresses come from the branch. The local prepass reads
their width from a public length-only table generated from the template. -/
def Template.reportWordCount (T : Template E I Orig s C) (c : Fin C) : ℕ :=
  1+((T.reports c).map fun row => 1+row.length).sum

/-- The length-only control gives the exact word count of the real report section. -/
theorem Template.reportWordCount_eq (T : Template E I Orig s C) (owner : Fin s → Fin C)
    (args : E → ℕ) (fields : Fin s → I → ℕ) (c : Fin C) :
    T.reportWordCount c = (fieldList vector ((T.directory owner args fields).reports c)).length := by
  simp [Template.reportWordCount,Template.directory,fieldList,vector,List.length_flatMap,List.map_map,
    Function.comp_def,Nat.add_comm]

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
