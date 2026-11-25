import OAI.Hierarchy.DescentTerminalEmitterFrames
import OAI.Hierarchy.DescentTerminalFixedHeaders

namespace OAI
/-! # The printed quotient and tail are the actual bit length of all selected cables -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM Computability.BorderVNP.Crossing ProtocolRAM
open DescentTerminalCableOrder DescentTerminalHeaderGroups
open scoped Classical BigOperators
noncomputable section
variable {w q p D H : ℕ} {P : Type} [Fintype P] {width : P→ℕ} (N : Network D P width)
    (home : N.Site→Fin H) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    («public» : P ↪ ℕ) (node : N.Site ↪ ℕ) (op : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
    (S : Shape) (L : Layout)
local notation "cap" => S.plane.headerRows
local notation "hdr" => L.plane.header
local notation "whole" => L.plane.header.whole.base+(cap-1)
local notation "tail" => L.plane.header.rem.base+(cap-1)
local notation "total" => ∑e,N.width e

theorem cutoff (m : Memory w) (room : Room S L w) (nonempty : 0<cap) (hq : 0<q) (hp : 0<p)
    (limit : ℕ) (all : ∀e,pairIndex N home e<limit)
    (enough : (stream N home native «public» node op q hp limit).length≤cap)
    (reads : DescentTerminalDenseHeaderRAM.Reads hdr (padded (n:=cap) (stream N home native «public» node op q hp limit))
       (DescentTerminalDataPlane.file S.plane L.plane m)) (one : Later L whole) (two : Later L tail)
    (count : total/(q*p)<2^w) (part : q*p≤2^w) :
    (result S L m whole).val=total/(q*p) ∧ (result S L m tail).val=total%(q*p) := by
  let start:=DescentTerminalDataPlane.file S.plane L.plane m
  obtain ⟨out,physical,observed,_⟩:=native_headers_eof_fixed N home native «public» node op hdr start hq hp limit enough room.plane.widths reads
  have same:=exec_unique _ start _ _ (DescentTerminalDenseHeaderRAM.exec_any hdr start room.plane.widths).1 physical
  rw [←same,beforePair_all N home limit all] at observed
  obtain ⟨a,b⟩:=observed
  simp only [DescentTerminalDenseHeaderRAM.eof,ite_eq_right (Nat.ne_of_gt nonempty)] at a b
  rw [after_plane S L m room one,after_plane S L m room two]
  change (DescentTerminalDenseHeaderRAM.finalMem hdr cap start whole).val=_ ∧
    (DescentTerminalDenseHeaderRAM.finalMem hdr cap start tail).val=_
  exact ⟨(congrArg Fin.val a).trans (Fin.val_cast_of_lt count),
    (congrArg Fin.val b).trans (Fin.val_cast_of_lt ((Nat.mod_lt _ (Nat.mul_pos hq hp)).trans_le part))⟩

end
end Hierarchy.DescentTerminalEmitter

end OAI
