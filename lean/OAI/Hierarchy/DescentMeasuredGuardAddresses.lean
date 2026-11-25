import OAI.Hierarchy.DescentReservedMatrixRow
import OAI.Hierarchy.DescentRecordedRootBook
import OAI.Hierarchy.DescentPreparedPrimitiveRole
import OAI.Hierarchy.DescentIssuedRootRoom

namespace OAI
/-! # The role and matrix jobs access the same attained old packet -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentPackedWalsh DescentPackedColony DescentPackedColony.Phase.Arena DescentPlainTerminal.Suffix
open DescentSixParty DescentResetGates DescentSharedLeafLookup DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr)
    (f fee full total portPitch : ℕ)
local notation "Y" => 2^n
local notation "groups" => 2^c
local notation "levels" => Nat.clog 2 (E.dim+2)

open DescentPrimitiveBirth DescentIssuedRotorRoles DescentSixParty.Chronology
variable (graph : NonlinearExpanders.Graph n h) (packet C groupDigits stop layerBits factor : ℕ)
    (primitive : DescentResetGates.CanonicalTag (2^n)→Cell bit) (page : RootPage r (2^n))
local notation "builder" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch graph packet C groupDigits stop layerBits factor primitive page
local notation "actual" => a.atlasSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch graph packet C groupDigits stop layerBits factor primitive page
local notation "alloc" => fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers H portPitch c (E.dim-c)
  table levels total (.lookup oldId .row)
local notation "arena" => RootTemplates.arena (a.headerEnd B) H groups M r n D

theorem issued_guard_addresses (room : (actual).OperandRoom H groups M w (a.headerEnd B)) :
    (∀side root j,(((B).good side root (.inl false)).2.reads j)=(actual).matrixRow H j) ∧
    (∀side root gate j,(((B).good side root (.inr gate)).2.reads j).Fits w
      ((arena).middle ((rootIndex r (2^n) (side,.inl (root,.inr gate))).val))) :=by
  have same (side) (root) (j) : ((B).good side root (.inl false)).2.reads j = (actual).matrixRow H j := (builder).reserved_matrix_reads (field:=field) graph packet f Ht C groupDigits stop layerBits primitive
    H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n alloc page side root j
  refine ⟨same,?_⟩
  intro side root gate j
  let id:=(rootIndex r (2^n) (side,.inl (root,.inr gate))).val
  have before : a.headerEnd B≤(arena).middle id:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  apply ProtocolRAMGeneratedWrite.fits_mono _ before
  rw [show ((B).good side root (.inr gate)).2.reads j = _ from
    actual_guard_row (field:=field) builder graph packet f Ht C groupDigits stop layerBits primitive H factor hubWidth
    old.roster old.hubs a.projectionEnd groups M stencil.n alloc page side root gate j]
  rcases (finSumFinEquiv.symm j : Fin (DescentRotorWindowArchive.count D (2^r) cap+1)⊕Fin 2)
    with head|flag
  · simp only [Sum.elim_inl]
    rcases (finSumFinEquiv.symm head : Fin (DescentRotorWindowArchive.count D (2^r) cap)⊕Fin 1)
      with data|_
    · exact (congrArg (fun e : Expr => e.Fits w (a.headerEnd B)) (same side root data)).mpr
        ((actual).matrix_fit room data)
    · exact room.capacity
  · simp only [Sum.elim_inr]
    split
    · exact room.depth
    · exact ⟨room.localShape _,trivial⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
