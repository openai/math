import OAI.Hierarchy.DescentIssuedRootRoom
import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentOperandPreparedPackets

namespace OAI
/-! # Address checks for the literal prior reset packet columns -/
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

local notation "scene" => a.atlasSources E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity
  f fee full total portPitch board packet C groupDigits batches layerBits factor primitive bookPage


private theorem raise_access {u v : Bank} {lo hi : ℕ} (ok : Accessible peers u H groups M w lo)
    (bound : lo≤hi) (word : v.Fits w hi) (capacity : H*chunks groups M≤v.size) :
    Accessible peers v H groups M w hi:=by
  have lift {bank : Bank} (old : bank.Fits w lo) : bank.Fits w hi:=
    ⟨old.1,old.2.1,old.2.2.trans bound⟩
  exact ⟨fun j=>lift (ok.ids j),ok.idsRoom,lift ok.roster,ok.rosterRoom,
    lift ok.offsets,ok.offRoom,lift ok.chunks,ok.chunkRoom,word,capacity⟩

private theorem address_more {lo hi : ℕ} (old : (scene).OperandRoom H groups M w lo) (bound : lo≤hi) :
    (scene).OperandRoom H groups M w hi:=by
  have lift {bank : Bank} (v : bank.Fits w lo) : bank.Fits w hi:=⟨v.1,v.2.1,v.2.2.trans bound⟩
  exact ⟨fun j=>lift (old.localShape j),fun j=>raise_access _ (old.remoteShape j) bound
    (lift (old.remoteShape j).source) (old.remoteShape j).srcRoom,fun i j=>lift (old.ports i j),
    fun i j=>ProtocolRAMGeneratedWrite.fits_mono _ bound (old.order i j),
    fun i j k=>ProtocolRAMGeneratedWrite.fits_mono _ bound (old.reservations i j k),
    ProtocolRAMGeneratedWrite.fits_mono _ bound old.capacity,ProtocolRAMGeneratedWrite.fits_mono _ bound old.depth⟩

theorem packet_addresses (checked : (scene).OperandRoom H groups M w head)
    (id : oldId.Fits w head) (idRows : H*chunks groups M≤oldId.size) :
    (∀i,Accessible peers ((scene).tagged i) H groups M w head) ∧
    Accessible peers oldId H groups M w head ∧
    (∀x,((scene).here x).Fits w head ∧ H*chunks groups M≤((scene).here x).size) ∧
    ∀x j,((scene).signed x j).Fits w head ∧ H*chunks groups M≤((scene).signed x j).size:=by
  exact ⟨checked.remoteShape,raise_access peers (checked.remoteShape (0:Fin low)) le_rfl id idRows,
    fun i=>⟨checked.localShape i,Nat.le_pow_clog (by decide) _⟩,
    fun i j=>⟨checked.ports i j,Nat.le_pow_clog (by decide) _⟩⟩

/-- Every entry in the actual seven-component exceptional key and in the original
matrix key reads its operands below the selected native aperture. -/
theorem packet_operand_fit (last : a.preparedEnd B<2^w) (checked : (scene).OperandRoom H groups M w head)
    (p : Page) : ∀j,(((B).table p).2.reads j).Fits w ((ar).middle (rootIndex r (2^n) p).val):=by
  let visible:=scene
  have measured {endAt : ℕ} (le : head≤endAt) : visible.OperandRoom H groups M w endAt:=
    address_more a E stencil old stencilBase splitBank hubWidth peers oldId priorCapacity f fee full total portPitch
      board packet C groupDigits batches layerBits factor primitive bookPage checked le
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
    change (B).good s v k = visible.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive H s v k at eqn
    rw [eqn]
    exact visible.good_fit ready board packet f Ht C groupDigits batches layerBits primitive s v k
  · intro j
    have eqn:=(prev).reserved_fallback_reads (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      H factor hubWidth old.roster old.hubs a.projectionEnd groups M stencil.n pt bookPage s v j
    change (((B).exceptional s v).reads j).Fits w ((ar).middle ix)
    apply (congrArg (fun expr : Expr => expr.Fits w ((ar).middle ix)) eqn).mpr
    exact visible.fallback_fit (field:=field) ready board packet Ht C layerBits _ s v j
      (a.rank_readable_of_top B s v top).fit

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
