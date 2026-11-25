import OAI.Hierarchy.DescentPhysicalRootBook
import OAI.Hierarchy.DescentResetPrefixRoom

namespace OAI
/-! # Operand-bank bounds for the four physical reset root programs -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedColony DescentSharedLeafLookup DescentResetHostSize
open DescentSixParty.Chronology DescentResetGates DescentPackedPrivateMenu
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace RootSources
variable {n h r D cap H G M field bit w ceiling : ℕ}
local notation "L" => 2^r
local notation "Y" => 2^n
variable (src : RootSources D (2^r) cap)

/-- Primitive bank and scalar bounds shared by all four physical root menus. -/
structure OperandRoom (H G M w ceiling : ℕ) : Prop where
  localShape : ∀i,(src.here i).Fits w ceiling
  remoteShape : ∀i,Accessible src.peers (src.tagged i) H G M w ceiling
  ports : ∀i j,(src.signed i j).Fits w ceiling
  order : ∀i j,(src.oldOrder i j).Fits w ceiling
  reservations : ∀p j u,(src.reservation p j u).Fits w ceiling
  capacity : src.priorCap.Fits w ceiling
  depth : src.relativeDepth.Fits w ceiling

variable (room : src.OperandRoom H G M w ceiling)

include room in
theorem matrix_fit (j : Fin (DescentRotorWindowArchive.count D L cap)) :
    (src.matrixRow H j).Fits w ceiling := by
  unfold matrixRow
  rcases DescentRotorWindowArchive.ix.symm j with (((i|⟨p,i⟩)|⟨i,q⟩)|(⟨i,x⟩|⟨p,q,u⟩))
  · exact ⟨room.localShape i,trivial⟩
  · exact peer_fits src.peers (src.tagged i) ceiling (room.remoteShape i) p
  · exact ⟨room.ports i q,trivial⟩
  · exact room.order i x
  · exact room.reservations p q u

include room in
theorem good_fit (board : NonlinearExpanders.Graph n h) (packet f Ht C groupDigits batches layerBits : ℕ)
    (primitive : CanonicalTag Y→Cell bit) (s : Bool) (v : Code r) (k : Bool⊕Fin Y)
    (j : Fin (src.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive H s v k).1) :
    ((src.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive H s v k).2.reads j).Fits w ceiling := by
  rcases k with (flag|gate)
  · cases flag
    · exact src.matrix_fit room j
    · change (src.headerRow v j).Fits w ceiling
      unfold headerRow
      split
      · exact room.capacity
      · split
        · exact room.depth
        · exact ⟨room.localShape _,trivial⟩
  · change (src.roleRow H v j).Fits w ceiling
    unfold roleRow
    cases finSumFinEquiv.symm j with
    | inl a=>
      dsimp only [Sum.elim_inl]
      cases (finSumFinEquiv.symm a : Fin (DescentRotorWindowArchive.count D L cap)⊕Fin 1) with
      | inl wire=> exact src.matrix_fit room wire
      | inr _=> exact room.capacity
    | inr flag=>
      dsimp only [Sum.elim_inr]
      split
      · exact room.depth
      · exact ⟨room.localShape _,trivial⟩

include room in
theorem fallback_fit (board : NonlinearExpanders.Graph n h) (packet Ht C layerBits : ℕ) (ranks : Header)
    (s : Bool) (v : Code r×Option (Fin Y)) (j : Fin (inputCount D L cap n r))
    (books : ∀b∈[ranks.ranks,ranks.start,ranks.cut,ranks.broadcast],b.Fits w ceiling) :
    ((src.fall (field:=field) board packet Ht C layerBits H ranks s v).reads j).Fits w ceiling := by
  change (operand (H:=H) src.peers ranks src.self src.tagged src.sign (number.symm j)).Fits w ceiling
  rcases number.symm j with ((i|⟨p,i⟩)|(⟨i,q⟩|ix))
  · exact ⟨room.localShape i,trivial⟩
  · exact peer_fits src.peers (src.tagged i) ceiling (room.remoteShape i) p
  · exact ⟨room.ports i q,trivial⟩
  · exact ⟨books _ (by simp),⟨books _ (by simp),trivial⟩,
      books _ (by simp),⟨books _ (by simp),trivial⟩,trivial⟩
end RootSources

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
