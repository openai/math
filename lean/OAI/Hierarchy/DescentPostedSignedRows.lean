import OAI.Hierarchy.DescentCalendarPreviousFields
import OAI.Hierarchy.DescentPostedSignedNames

namespace OAI
/-! # Canonical signed venue rows in the measured operand memory -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentSharedCableNames DescentResetFieldAssembler DescentResetLocalRoster
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRankedWindows
open DescentDenseHostOrder DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentResetCandidatePair
open scoped Classical
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "N" => totalLocal B
local notation "X" => 2^k
local notation "gs" => S.groupCount (i+1)
local notation "ht" => GroupStage.depthBound D n f g
variable {a : PhysicalReset} {floor w : ℕ} (I : a.DateInputs floor w)
local notation "v" => a.successor
local notation "base" => a.rebased floor
local notation "A" => (v).receiver
local notation "ss" => I.sectors
local notation "ST" => (v).sheetsStart base
local notation "plan" => (v).linkedRankInputs ss ST
local notation "head₀" => sheetHeader B ST (ss).pageBits
local notation "key₀" => sheetOriginal B ST (ss).pageBits
local notation "native" => (v).rankBook plan base
local notation "b" => (v).assemblerBits
local notation "t" => (v).ticketBits
local notation "P₀" => (v).rankPorts base
local notation "L" => rankLayout B ((v).rankPortEnd base) (A).hosts b t (A).lanes P₀ head₀ key₀
variable (hx : (A).blocks=X) (hj : (A).candidates=N) (gg : (A).groups=gs)

variable (before : (ss).before=publicBefore D k n ht (S.groupWidth k tail i)
      input.placement.cap (programCount ctl.board ht))
    (slot : ∀j,(ss).sourceSlot j=publicSourceSlot D k n ht input.placement.cap (programCount ctl.board ht)
      (A).candidates j.val)
variable (room : Fintype.card B.next.V≤(A).hosts)
local notation "host" => B.next.vertex.trans (Fin.castLEEmb room)
local notation "rack" => rackOf B host
variable (ok : I.Ready) (m : Memory w)
local notation "portMem" => ((v).rankPortPhase base w).image (I.candidateEntry ok m)
variable (src : RankSources B («b»:=b) («t»:=t) (M:=(A).lanes) rack P₀ head₀ key₀ portMem)
include hj before slot src in
theorem posted_operand_signed (cap : (A).capacity=B.next.placement.cap)
    (degree : I.degree=B.next.placement.degree)
    (digits : max (B.next.placement.degree+1) (B.next.placement.cap+1)<2^b)
    (x : Fin (A).blocks) (j : Fin (2*(A).capacity)) :
    Reads ((PhysicalReset.FinalInputs.predecessor I).signed x.val j.val)
      (fun hostId groupId=>DescentSignedCableCodec.encode (Prepare.signed B.next.placement
        (B.next.order.trans Fin.valEmbedding) S B.next.valid (Function.Embedding.refl _) host
        (x.cast hx) (j.cast (congrArg (2*·) cap)) hostId (groupId.cast gg))) (A).lanes (I.sheetsResult ok m):=by
  have original:=calendar_signed_output B I hx hj gg before slot rack ok m src cap degree digits x j
  simp_rw [posted_prepare_word B room] at original
  apply I.signed_at_sheets ok m x j _
  have same : DescentNextSignedWindow.Native.All.page ((v).fieldsEnd base) (A).blocks (A).capacity
      (A).signedBits (A).lanes (A).hosts (A).groups x j =
      DescentResetWindowTail.page ((v).rankEnd base) (A).blocks (A).capacity b (A).lanes (A).hosts (A).groups x j := by
    rw [ok.width]
    rfl
  rw [same]
  exact original

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
