import OAI.Hierarchy.TaggedWideBallotWords
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProbeFixedElectionPages

namespace OAI
/-! # Address bounds for the native ballot code and histogram fields -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart PurchaseStage WireTelescope WideCPU
open scoped Classical Fin.CommRing BigOperators

private theorem installed_histogram_field (F : Type*) [Field F] {z d k letters depth : ℕ}
    (sl : Slab) (s : StripChart.Boards z d k letters depth) (c : Mesh) (a : Attempt)
    (incoming : ℕ) (j : Fin letters) :
    (StripChart.build F (Slab.install sl s c) a incoming).board.batch.field j =
      HistogramShelf.field (⟨(Slab.arena sl s).base c (.attempt a), z+letters*Slab.rowFactor s⟩ : Bank) j := by
  cases a <;> rfl

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (h width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet
local notation "W" => wordBits h (2^v.W) copies
local notation "fs" => v.nativeFormats P h width
local notation "A" => v.privateArena P h width
local notation "slab" => v.slab (v.seed P h width) P width
local notation "B" => v.nativeBoards P h width
variable (a : Attempt)

/-- The complete allocated RAM lookup interval, including its power-of-two padding,
is contained in the original paid attempt. -/
theorem wide_ballot_code_fit (live : Event.attempt a∈events v.mesh)
    (room : (A).endAddress v.mesh<2^W) (floor : ℕ) (placed : (A).endAddress v.mesh≤floor) :
    (Ballot.code ((fs a).board.reportOut 6) (fs a).market.rows).Fits W floor := by
  let f := fs a
  let n := f.market.rows
  have pos : 0<n := by
    have count : n=PurchaseFrozen.count h (2^v.W) k*PurchaseFrozen.paths h v.sampler.degree v.depth :=
      candidate_count F v.mesh A P.joint.initial B a
    rw [count,PurchaseFrozen.count_eq]
    have axis:=v.positive
    have degree:=v.sampler_live
    unfold PurchaseFrozen.paths
    positivity
  have cap:=ProtocolRAMPurchaseSampler.span_le n
  have through : f.board.reportOut 6+ProtocolRAMPurchaseSampler.span n≤f.board.boughtFields 5+n := by
    change PostLayout.startColumns f.maskStart f.indexBits n+9*n+_≤
      PostLayout.startColumns f.maskStart f.indexBits n+15*n+n
    omega
  have stop:=through.trans (f.chargeColumns.2.2.2.1.trans
    ((v.attempt_room P h width a).trans ((A).within v.mesh _ live)))
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (stop.trans_lt room),stop.trans placed⟩,trivial⟩

variable (fits : (v.privateArena P h width).endAddress v.mesh<2^(wordBits h (2^v.W) copies))
  (copiesFit : v.menu.copiesAt v.copyScale width<2^(wordBits h (2^v.W) copies))

include fits in
theorem wide_ballot_field_fit (live : Event.attempt a∈events v.mesh)
    (floor : ℕ) (placed : (A).endAddress v.mesh≤floor) (j : Fin sig) : ((fs a).board.batch.field j).Fits W floor := by
  let bank : Bank := ⟨(A).base v.mesh (.attempt a), h+sig*Slab.rowFactor B⟩
  have span : bank.base+bank.size≤(A).base v.mesh (.attempt a)+(A).stride := by
    apply Nat.add_le_add_left
    change Slab.selectorSpan B≤Slab.stride slab B
    simp only [Slab.stride,PostLayout.column,PostLayout.startColumns,Slab.mask,Slab.flags,Slab.first,
      Nat.zero_add,Nat.add_assoc]
    exact Nat.le_add_right ..
  have bound:=span.trans ((A).within v.mesh _ live)
  have bankFit : bank.Fits W floor :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bound.trans_lt fits),bound.trans placed⟩
  let incoming := resolvedStock v.mesh A P.joint.initial (StripChart.build F B) a
  have eqn := installed_histogram_field F slab B v.mesh a incoming j
  have arenaEq : Slab.arena slab B = A := rfl
  rw [arenaEq] at eqn
  have fieldEq : (fs a).board.batch.field j = HistogramShelf.field bank j :=
    (congrArg (fun s : StripChart.Boards h (2^v.W) k sig v.depth =>
      (StripChart.build F s a incoming).board.batch.field j) (v.nativeBoards_install P h width)).symm.trans eqn
  rw [fieldEq]
  change bank.Fits W floor ∧ (scale sig .row).Fits W floor ∧ True
  refine ⟨bankFit,?_,trivial⟩
  have add (n : ℕ) : (scale n .row).Fits W floor := by
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨trivial,ih⟩
  exact add sig


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
