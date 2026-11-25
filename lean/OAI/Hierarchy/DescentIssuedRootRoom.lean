import OAI.Hierarchy.DescentRootOperandRoom
import OAI.Hierarchy.DescentPreparedRootFit
import OAI.Hierarchy.DescentPreparedFallbackRanks
import OAI.Hierarchy.DescentRecordedRootBook
import OAI.Hierarchy.DescentPreparedReservations

namespace OAI
/-! # All bank and instruction bounds of the issued reset book before execution -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSIMDLookup DescentPlainTerminal.Suffix DescentPackedColony DescentSharedLeafLookup DescentResetHostSize
open DescentSixParty.Chronology DescentSixParty DescentResetGates DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h₀ l t field Ht w h bit : ℕ}
    (a : Receiver D cap N n r c H G K R M h₀ l t field Ht w) (E : EstimatorArena)
    (stencil : StencilBook) (old : StencilBook.Sources) (stencilBase splitBank hubWidth : ℕ)
    (peers : Ports D) (oldId : Bank) (priorCapacity : Expr) (f fee full total portPitch : ℕ)
    (board : NonlinearExpanders.Graph n h) (packet C groupDigits batches layerBits factor : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit) (bookPage : RootPage r (2^n))
local notation "low" => 2^r
local notation "groups" => 2^c
local notation "B" => a.issuedBook E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
local notation "prev" => a.issuedSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
local notation "head" => a.headerEnd B
local notation "ar" => RootTemplates.arena head H groups M r n D
local notation "Page" => RootPage r (2^n)
local notation "pt" => fun table hdr=> ClosedReset.Recorded.reservationFields E hdr peers H portPitch c (E.dim-c) table
  (Nat.clog 2 (E.dim+2)) total (.lookup oldId .row)

private theorem portRoom {P : Ports D} {v u : Bank} {lo hi : ℕ}
    (access : Accessible P v H groups M w lo) (before : lo≤ hi) (fits : u.Fits w hi)
    (rows : H*chunks groups M≤ u.size) : Accessible P u H groups M w hi := by
  have lift {b : Bank} (ok : b.Fits w lo) : b.Fits w hi:=⟨ok.1,ok.2.1,ok.2.2.trans before⟩
  exact ⟨fun j=> lift (access.ids j),access.idsRoom,lift access.roster,access.rosterRoom,
    lift access.offsets,access.offRoom,lift access.chunks,access.chunkRoom,fits,rows⟩

local notation "scene" => a.atlasSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage

/-- Every matrix operand reads below the first root job. This applies equally before the
first job and after the entire catalogue has executed. -/
theorem issued_operand_room (last : a.preparedEnd B<2^w)
    (prior : Bank) (support : Accessible peers prior H groups M w head)
    (host : oldId.Fits w head) (depth : E.depthRows.Fits w head)
    (totals : (ClosedReset.Recorded.firstContactBank E).Fits w head)
    (order : ∀i j,((prev).oldOrder i j).Fits w head)
    (heads : (prev).priorCap.Fits w head ∧ (prev).relativeDepth.Fits w head)
    {endAt : ℕ} (le : head≤endAt) : (scene).OperandRoom H groups M w endAt := by
  have header:head<2^w:=(Nat.le_add_right ..).trans_lt last
  have first:=(B).limits a.projectionEnd H groups M
  have start:a.projectionEnd≤ head:=(first.1.trans first.2.1).trans first.2.2
  have lit:=a.issued_literals E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
    f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
  have pages:=(B).shared_span a.projectionEnd H groups M bookPage
  have comparator:(DescentRootOrderCast.bank ((B).castAt a.projectionEnd H groups M) stencil.n M).Fits w head:=by
    have count:(B).castWords M=2^(stencil.n*M):=by simp [RootBook.castWords,lit.2.2.2.1]
    have inside:=pages.1
    rw [count] at inside
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (inside.trans_lt header),inside⟩
  have bill:(B).auxAt a.projectionEnd H groups M+DescentReservationHeader.reserveEntries H (Nat.clog 2 (E.dim+2)) total≤ head:=by
    change _ ≤ (B).stop a.projectionEnd H groups M
    simpa only [lit.2.2.2.2.1] using pages.2
  let hdr:=(B).rankHeader a.projectionEnd H groups M bookPage
  let rate:=pt ((B).auxAt a.projectionEnd H groups M) hdr
  have quote (j i : Fin D) (u : Fin 6) : (rate j i u).Fits w head:=
    ClosedReset.Recorded.reservationFields_fits_of_span E hdr peers prior (.lookup oldId .row) ⟨host,trivial⟩ support bill
      (a.prepared_broadcast_room_of_top B header bookPage) depth totals header j i u
  let visible:=scene
  have bank (z : Column low cap) {endAt : ℕ} (le : head≤ endAt) :
      let b:=bankAt a.stencil a.tapped t D a.signedEnd H groups M z
      b.Fits w endAt ∧ H*chunks groups M≤ b.size := by
    let bound:=a.window_fits z (start.trans_lt header)
    exact ⟨⟨bound.1,bound.2.1,bound.2.2.trans (start.trans le)⟩,Nat.le_pow_clog (by decide) _⟩
  have measured {endAt : ℕ} (le : head≤ endAt) : visible.OperandRoom H groups M w endAt:=by
    refine ⟨fun i=>(bank (.inl (0,i)) le).1,fun i=>?_,fun i j=>(bank (.inr (j,i)) le).1,
      fun i j=>?_,fun q j u=>?_,?_,?_⟩
    · exact portRoom support le (bank (.inl (1,i)) le).1 (bank (.inl (1,i)) le).2
    · exact ProtocolRAMGeneratedWrite.fits_mono _ le ⟨comparator,order i j⟩
    · exact ProtocolRAMGeneratedWrite.fits_mono _ le (quote q j u)
    · exact ProtocolRAMGeneratedWrite.fits_mono _ le heads.1
    · exact ProtocolRAMGeneratedWrite.fits_mono _ le heads.2
  exact measured le

theorem issued_book_fits (pre : a.PrefixFits) (last : a.preparedEnd B<2^w)
    (neighbor : old.roster.Fits w head) (hub : old.hubs.Fits w head)
    (prior : Bank) (support : Accessible peers prior H groups M w head)
    (host : oldId.Fits w head) (depth : E.depthRows.Fits w head)
    (totals : (ClosedReset.Recorded.firstContactBank E).Fits w head)
    (order : ∀i j,((prev).oldOrder i j).Fits w head)
    (heads : (prev).priorCap.Fits w head ∧ (prev).relativeDepth.Fits w head)
    (lanes : ∀p : Page,M*max (((B).table p).2.field*((B).table p).1) ((B).table p).2.outputBits≤ w/2) :
    a.PreparedFits B := by
  let visible:=scene
  have measured {endAt : ℕ} (le : head≤endAt) : visible.OperandRoom H groups M w endAt :=
    a.issued_operand_room E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
      f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage
      last prior support host depth totals order heads le
  refine a.prepared_fit B pre last neighbor hub ?_ lanes
  intro p
  let ix:=(rootIndex r (2^n) p).val
  have early:head≤(ar).middle ix:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have name:=(rootIndex r (2^n) p).isLt
  have later:(ar).first (ix+1)≤ a.preparedEnd B:=Nat.add_le_add_left (Nat.mul_le_mul_left _ name) _
  have top:(ar).middle ix<2^w:=by
    have endAt:=RootArena.end_row (ar) ix
    have lowAt:(ar).middle ix≤(ar).output ix:=Nat.le_add_right ..
    omega
  have ready:=measured early
  rcases p with ⟨s,(⟨v,k⟩|v)⟩
  · have eqn:=(prev).reserved_good (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n pt bookPage s v k
    change ∀j,(((B).good s v k).2.reads j).Fits w ((ar).middle ix)
    apply (congrArg (fun job : Σ arity, RootTable arity =>
      ∀ j, (job.2.reads j).Fits w ((ar).middle ix)) eqn).mpr
    exact visible.good_fit ready board packet f Ht C groupDigits batches layerBits primitive s v k
  · intro j
    have eqn:=(prev).reserved_fallback_reads (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n pt bookPage s v j
    change (((B).exceptional s v).reads j).Fits w ((ar).middle ix)
    apply (congrArg (fun e : Expr => e.Fits w ((ar).middle ix)) eqn).mpr
    exact visible.fallback_fit (field:=field) ready board packet Ht C layerBits _ s v j
      (a.rank_readable_of_top B s v top).fit

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
