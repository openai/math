import OAI.Hierarchy.DescentOrdinaryRawSeatWords
import OAI.Hierarchy.DescentHaloChartHeader
import OAI.Hierarchy.DescentHaloRebaseRAM

namespace OAI
/-! # The seat and reverse-rank fields of an ordinary donor -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentSharedCableNames DescentHaloWalkRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {H : ℕ}

structure Setup where
  profile : ℕ
  motifWidth : ℕ
  oldBits : ℕ
  gain : ℕ
  slots : ℕ
  hostPitch : ℕ
  fieldBits : ℕ

abbrev Seat := Fin s.blocks × Fin s.cap × Fin 11

def ranked (chart : Cell (chartBits s)) (p : Cell (ParentIncidence.pathBits s.degree)) : ℕ :=
  ((Packed.readToken (breadth s.degree) p).map fun i=>
    ((encode (Packed.bits (breadth s.degree)) (breadth s.degree)).symm chart i).val).getD (breadth s.degree)

theorem ranked_read (v : Fin (breadth s.degree)→Fin (breadth s.degree+1))
    (p : Fin (breadth s.degree)) :
    ranked s (DescentHaloPackedRebase.digest v) (Packed.token (some p))=(v p).val :=by
  simp only [ranked,Packed.token_back,Option.map_some,DescentHaloPackedRebase.digest,
    Equiv.symm_apply_apply,Option.getD_some,DescentHaloPackedRebase.field]

local notation "P" => breadth s.degree

def reverseEntries (R : Fin H→Fin s.degree→Option (Fin H)) (h : Fin H) (p : Fin P) : Fin (P+1) :=
  ⟨Rebase.value R .rank h p,Nat.lt_succ_of_le (Rebase.value_le R .rank h p)⟩

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material

end OAI
