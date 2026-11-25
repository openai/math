import OAI.Hierarchy.DescentCalendarMatrixOrigins
import OAI.Hierarchy.DescentNamedRootReindex

namespace OAI
/-! # Root rows measured at the public two-piece width of the physical stencil -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSIMDLookup DescentGL DescentPackedColony DescentPackedZip
open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSharedCableNames.Stage DescentStageEdgeReceipt DescentIssuedFallbackPanel DescentGroupPeerOrder
open DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 1000000
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "m" => S.groupWidth k tail i+k
local notation "dep" => GroupStage.depthBound D n f g
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "full" => (A).wire*((A).z*G.b)*cap
local notation "pad" => input.valid.host
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "peer" => PackedFlow.Padded.roster (D:=deg) (A) (Recorded.oldName input) pad
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount i)) ((id_).trans Fin.valEmbedding))

variable {M field bw N K R hm lb tiny p nbits t d₀ n₀ : ℕ}
  (machine : Receiver.IndexedRoots deg cap N n₀ (d₀-cc) cc H (S.groupCount i) K R M hm lb tiny field dep bw)
  (width : d₀=(Z).k) (size : n₀=(Z).n)
  (mem : Memory bw)
local notation "out" => machine.reindex rfl rfl size (congrArg (fun s=>s-cc) width) rfl rfl rfl rfl
local notation "rc₀" => machine.receiver
local notation "bk₀" => machine.book
local notation "src" => machine.sources
local notation "middle" => (rc₀).preparedMid bk₀ machine.prepared mem
local notation "rank₀" => fun v j=>(DescentSharedBookScan.ranks (a:=d₀-cc) (Y:=2^n₀) (D:=deg)
  ((bk₀).common (rc₀).projectionEnd H) (2^dep) (dep+2) middle v j).val
local notation "paid₀" => Recorded.paddedValue (b:=field) cc (d₀-cc) peer (Recorded.oldDepth B) (Recorded.oldWidth B)

/-- Eliminate the public total-width equality before reading the original root arrays. -/
theorem matrix_packet_at_width (hdr : OriginalHeader B pad (out).receiver (out).book mem)
    (recorded : B.Recorded p) (wider : t<field)
    (level : m-cc<2^nbits) (one : 1<2^nbits) (mass : 2^(m-cc)*full<2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows (m-cc) (2^(Z).n)≤2^t)
    (active : 0<full) (quotaPaid : 0<quota S.rounds) (degreePaid : 0<32*Nat.clog 2 (2*deg))
    (μ : DescentGL.Layout d₀) (won : HEq μ B.frame.basis) (small : cc≤d₀)
    (values : Fin H→Block cc→Block (d₀-cc)→Cell t)
    (marks : Fin H→Block cc→Block (d₀-cc)→Fin (2*cap)→Option (Live deg cap))
    (sample : ∀v hi x,values (id_ v) hi x=Recorded.realPanel (reset:=B) (width.trans B.keyWidth) μ nbits t v hi x)
    (cables : ∀v hi x j,marks (id_ v) hi x j=signedPanel A (input.order.trans Fin.valEmbedding) S input.valid
      names (donor ((Equiv.cast (congrArg Block (width.trans B.keyWidth))).trans digits) μ small v hi x) j)
    (area : (src).OperandRoom H J M bw ((rc₀).headerEnd bk₀))
    (markSize : ∀a s,H*chunks J M≤((src).signed a s).size)
    (rows : ∀j,Source ((src).matrixRow H j) (fun v hi=>RootSources.paddedRow
      (fun u b a=>(values u b a).val) peer marks rank₀ (fun _=>Receiver.matrixBefore μ small) paid₀ v hi j) M middle)
    (signed : ∀s a,Reads ((src).signed a s) (fun v hi=>DescentResetOppositePayload.widened deg cap field (marks v hi a s)) M middle)
    (mounted : Mounted (src).peers peer middle J M)
    (here : ∀a,Reads ((src).here a) (fun v hi=>((values v hi a).val:Cell field)) M middle)
    (tagged : ∀a,Reads ((src).tagged a) (fun v hi=>((values v hi a).val+1:Cell field)) M middle) :
    ∃x : OriginalArrays B pad field,RootPacket B (out).receiver (out).book (out).prepared mem hdr (out).sources x nbits t :=by
  subst d₀; subst n₀
  exact calendar_matrix_packet B (rc₀) (bk₀) machine.prepared mem hdr (src) recorded wider level one mass codes active quotaPaid
    degreePaid μ won small values marks sample cables area markSize rows signed mounted here tagged

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
