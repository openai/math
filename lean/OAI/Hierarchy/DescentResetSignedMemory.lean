import OAI.Hierarchy.DescentResetRankCalendar
import OAI.Hierarchy.DescentResetRankedReceipt
import OAI.Hierarchy.DescentPhysicalResetRankProgram

namespace OAI
/-! # One actual dated issuer from the original mixed cable keys through every signed slot -/
namespace Hierarchy.DescentResetRankedWindows.Layout
open ThreeFlat.RAM PhysicalProcedure
variable {X K X' K' w : ℕ}

/-- Calendar and semantic candidate extents are proved equal before compiling. -/
def reindex (L : Layout X K) (x : X'=X) (j : K'=K) : Layout X' K' :=
  ⟨L.base,L.bits,L.originalBits,L.lanes,L.hosts,L.groups,L.ports,L.before,
    fun t=>L.sourceSlot (Fin.cast j t),fun z t=>L.header (Fin.cast x z) (Fin.cast j t),
    fun z t=>L.original (Fin.cast x z) (Fin.cast j t)⟩

theorem reindex_code (L : Layout X K) (h : X'=X) (k : K'=K) (m : Computability.VPVNP.BurstRAM.Memory w) :
    (L.reindex h k).program w=L.program w ∧ (L.reindex h k).time=L.time ∧
    (L.reindex h k).memory m=L.memory m ∧ (L.reindex h k).endAddress=L.endAddress :=by
  subst X';subst K'
  exact ⟨rfl,rfl,rfl,rfl⟩

end Hierarchy.DescentResetRankedWindows.Layout

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open DescentResetCompactParent DescentResetCableSlots DescentResetOrdinalDigits DescentResetWireTags
open DescentRouterSlots DescentPackedTicketChronology DescentOrderedReset
open DescentResetLocalRoster
open scoped Classical BigOperators
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "U" => Fintype.card input.V
local notation "H₀" => input.placement.degree+2
local notation "Y" => (2^(Z).n:ℕ)
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "L" => (2^(S.groupWidth k tail i+k-(T).commonDepth)+1)*H₀*2^k
local notation "slots" => max Y (2^height)
local notation "pcCap" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "okCode" => fun t=>((T).codeLegal t).2
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Short" => DescentResetCompactParent.Word H₀ r Y L (A).cap slots pcCap

open DescentPackedColony DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentResetFieldAssembler
local notation "K" => totalLocal B
local notation "X" => 2^k
local notation "grp" => S.groupCount (i+1)
local notation "board_" => blocks B
local notation "entry" => (Z).rawHostRank T vertex
open DescentResetRankedWindows DescentResetSourceTicketCompare DescentResetFieldAssembler
variable {H M b t Wd : ℕ} (rack : Fin H→Option B.next.V)

local notation "rows" => H*chunks grp M
variable (base : ℕ) (ports : Ports 4) (header original : Fin (2^k)→Fin (totalLocal B)→Expr)
local notation "Λ" => rankLayout B base H b t M ports header original


local notation "dst" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
open DescentNextSignedWindow
set_option maxHeartbeats 1200000 in
theorem signed_memory (m : Memory Wd) (s : RankSources B (M:=M) (b:=b) (t:=t) rack ports header original m)
    (prev : (Λ).Previous Wd)
    (room : DescentResetWindowTail.endAddress (Λ).endAddress X (dst).cap b M H grp<2^Wd)
    (digits : max ((dst).degree+1) ((dst).cap+1)<2^b) :
    let e:=(Λ).endAddress
    let tail:=DescentResetWindowTail.program e X (dst).degree (dst).cap b M H grp Wd header (Λ).finalRank
    let op:=((Λ).program Wd).seq tail
    let clock:=(Λ).time+DescentResetWindowTail.time e X (dst).degree (dst).cap b M H grp header (Λ).finalRank
    let done:=DescentResetWindowTail.memory e X (dst).degree (dst).cap b M H grp header (Λ).finalRank ((Λ).memory m)
    op.Exec m done clock ∧
      (∀x j,Reads (DescentResetWindowTail.page e X (dst).cap b M H grp x j)
        (fun v g=>DescentSignedCableCodec.encode ((rack v).bind (fun node=>
          Stage.signedPanel dst ord S B.next.valid (fieldNames B) ((g,node),x) j))) M done) ∧
      (∀v,v<base ∨ DescentResetWindowTail.endAddress e X (dst).cap b M H grp≤v→done v=m v) ∧ CheapCode op := by
  intro e tail op clock done
  have span : e≤DescentResetWindowTail.endAddress e X (dst).cap b M H grp :=
    (Nat.le_add_right ..).trans (DescentResetWindowTail.lower ..)
  obtain ⟨rank,live,counts,back,ok⟩:=ranked_fields B rack base ports header original m s prev (span.trans_lt room)
  obtain ⟨write,issued,frame,cheap⟩:=tail_run B rack e header (Λ).finalRank ((Λ).memory m)
    (fun x j=>(live x j).1) (fun x p j=>(counts x p j).1) (fun x j=>(live x j).2)
    (fun x p j=>(counts x p j).2) (meta_room B rack s.near s.small) digits room
  refine ⟨Procedure.Exec.then rank write,issued,?_,?_⟩
  · intro n h
    obtain ⟨a,b,c,d⟩:=(Λ).ordered
    rcases h with small|large
    · exact (frame n (.inl ((((small.trans_le a).trans_le b).trans_le c).trans_le d))).trans (back n (.inl small))
    · exact (frame n (.inr large)).trans (back n (.inr (span.trans large)))
  · apply ProtocolRAM.cheap_seq
    · exact @ok
    · exact @cheap

/-- The public request type carries the same two original-cable functions on the
same finite slot set even when the proved calendar extents are heterogeneous. -/
def datedRankInputs (v : DescentDatedAddressBook.ResetOutput) (nx : v.receiver.blocks=X)
    (nj : v.receiver.candidates=K) : v.RankInputs :=
  ⟨ports,wordBefore B,fun j=>slotGate B (Fin.cast nj j),fun x j=>header (Fin.cast nx x) (Fin.cast nj j),
    fun x j=>original (Fin.cast nx x) (Fin.cast nj j)⟩

/-- The reset controller emitted before choosing a branch uses precisely the word
decoder and source-slot address function for every slot of the reached reset. -/
theorem dated_inputs_calendar (v : DescentDatedAddressBook.ResetOutput)
    (nx : v.receiver.blocks=X) (nj : v.receiver.candidates=K)
    {W₀ W₂ : MarkedWorld F d P bits} {z₀ D₀ j z₂ D₂ : ℕ}
    {first : Reached W₀ G q ε S k 0 z₀ D₀ w hist} {last : Reached W₂ G q ε S k j z₂ D₂ w hist}
    (a : Chronology.Path first input) (suffix : Chronology.Path input last)
    (calendar : List ℕ) (issued : (a.append suffix).capFactors=calendar) (cap₀ : first.placement.cap=256) :
    let cap:=(calendar.take i).prod*256
    v.calendarRankInputs D k n height (S.groupWidth k tail i) cap (DescentResetLocalRoster.programCount ctl.board height)
      ports (fun x j=>header (Fin.cast nx x) (Fin.cast nj j)) (fun x j=>original (Fin.cast nx x) (Fin.cast nj j)) =
      datedRankInputs B ports header original v nx nj := by
  intro cap
  have fn:=code_calendar B a suffix calendar issued cap₀
  have size : v.receiver.candidates=DescentResetLocalRoster.publicSlots ctl.board height k cap :=
    nj.trans (local_roster_calendar B a suffix calendar issued cap₀)
  have gates : (fun j : Fin v.receiver.candidates=>DescentResetLocalRoster.publicSourceSlot D k n height cap
      (DescentResetLocalRoster.programCount ctl.board height) v.receiver.candidates j.val) =
      (fun j=>slotGate B (Fin.cast nj j)) := by
    funext j
    exact (congrArg (fun m=>DescentResetLocalRoster.publicSourceSlot D k n height cap
      (DescentResetLocalRoster.programCount ctl.board height) m j.val) size).trans ((fn.2 (Fin.cast nj j)).symm)
  unfold DescentDatedAddressBook.ResetOutput.calendarRankInputs datedRankInputs
  rw [←fn.1,gates]

theorem rank_book_compatible (v : DescentDatedAddressBook.ResetOutput) (start : ℕ)
    (nx : v.receiver.blocks=X) (nj : v.receiver.candidates=K) (groups : v.receiver.groups=grp) :
    v.rankBook (datedRankInputs B ports header original v nx nj) start=
      (rankLayout B (v.rankPortEnd start) v.receiver.hosts v.assemblerBits v.ticketBits v.receiver.lanes (v.rankPorts start) header original).reindex nx nj := by
  unfold DescentDatedAddressBook.ResetOutput.rankBook datedRankInputs rankLayout Layout.reindex
  simp only [groups]

theorem dated_rank_code (v : DescentDatedAddressBook.ResetOutput) (start : ℕ)
    (nx : v.receiver.blocks=X) (nj : v.receiver.candidates=K) (groups : v.receiver.groups=grp) (m : Memory Wd) :
    let t:=v.rankBook (datedRankInputs B ports header original v nx nj) start
    let l:=rankLayout B (v.rankPortEnd start) v.receiver.hosts v.assemblerBits v.ticketBits v.receiver.lanes (v.rankPorts start) header original
    t.program Wd=l.program Wd ∧ t.time=l.time ∧ t.memory m=l.memory m ∧ t.endAddress=l.endAddress :=by
  intro t l
  change (v.rankBook _ _).program _=_ ∧ (v.rankBook _ _).time=_ ∧ (v.rankBook _ _).memory _=_ ∧ (v.rankBook _ _).endAddress=_
  rw [rank_book_compatible B ports header original v start nx nj groups]
  exact l.reindex_code nx nj m

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
