import OAI.Hierarchy.DescentMeasuredGuardAddresses
import OAI.Hierarchy.DescentReachedRootRegister
import OAI.Hierarchy.DescentNamedRootControls

namespace OAI
/-! # The actual issued root book determines its fresh primitive register -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentLocalArchiveOrder DescentCompiler DescentRotor
open DescentResetLocalNodes DescentNamedContact
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit) (a : Archive W) (earlier : Local a.bit)
variable [Fintype P] (stored : b.Recorded p)
open scoped Classical Fin.CommRing
open DescentPrimitiveBirth DescentDenseHostOrder DescentPackedResetRotorRoles
local notation "Z" => b.reset
local notation "m" => b.reset.unit/p
local notation "res" => b.reset.k-b.terminals.commonDepth
local notation "dim" => b.terminals.commonDepth
local notation "H" => S.hostSize (i+1)
local notation "Groups" => S.groupCount (i+1)

open DescentRotorWindowArchive DescentIssuedRotorRoles DescentSIMDLookup DescentRotorRootPresence
open DescentSharedBookScan DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentPacking.PackedMatch.Local.Stage DescentResetGates DescentHostDirectory DescentResetHostSize
open DescentPackedColony DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescentStageEdgeReceipt DescentColonies

variable {field nodes args bits₀ stop lanes oldLanes classes priceBits spanBits : ℕ}
local notation "height₀" => GroupStage.depthBound D n f g
local notation "seats" => (roster (Z).graph res height₀).card
local notation "board" => (⟨⟨S.hostSize i,H,seats,Groups,2^k,lanes⟩,
  res,(Z).n,nodes,args,bits₀,stop,oldLanes,classes,priceBits,spanBits⟩:DescentPrimitiveBirth.Layout)
local notation "deg₀" => cap.placement.degree
local notation "cap₀" => cap.placement.cap
variable (equalAxis : S.groupCount (i+1)*2^k=2^b.terminals.commonDepth)
local notation "mapping" => (fun t : CanonicalTag (2^(Z).n)=>(role t:Cell bits₀))

open DescentPaidResidentCount.Reset
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
variable {bw N₀ K₀ R₀ M₀ hm lb tiny nbits t : ℕ}
    (rc : Receiver cap.placement.degree cap.placement.cap N₀ (b.reset).n (b.reset.k-b.terminals.commonDepth) b.terminals.commonDepth (S.hostSize i) (S.groupCount i) K₀ R₀ M₀ hm lb tiny field (GroupStage.depthBound D n f g) bw)
    (book : RootBook (b.reset).n (b.reset.k-b.terminals.commonDepth) cap.placement.degree (2^(b.reset.k-b.terminals.commonDepth)) cap.placement.cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader b cap.valid.host rc book mem) (src : RootSources cap.placement.degree (2^(b.reset.k-b.terminals.commonDepth)) cap.placement.cap)
    (raw : OriginalArrays b cap.valid.host field)
    (packet : ClosedReset.Window.RootPacket b rc book space mem hdr src raw nbits t)
local notation "total₀" => cap.placement.wire*(cap.placement.z*G.b)*cap₀

open DescentPackedWalsh DescentPlainTerminal.Suffix DescentPackedColony.Phase.Arena DescentSharedLeafLookup
variable (E : EstimatorArena) (st : StencilBook) (stInputs : StencilBook.Sources)
    (stBase splitBank hubWidth : ℕ) (peers : Ports cap.placement.degree) (hostIndex : Bank) (oldCap : Expr)
    (fee full total portPitch factor : ℕ) (page : RootPage (b.reset.k-b.terminals.commonDepth) (2^b.reset.n))
local notation "baseSource" => rc.issuedSources E st stInputs stBase splitBank hubWidth peers hostIndex oldCap
  f fee full total portPitch
local notation "observedBook" => rc.issuedBook E st stInputs stBase splitBank hubWidth peers hostIndex oldCap
  f fee full total portPitch (Z).graph (Z).width C m stop (DescentRecordedRotorLayers.width f cap₀) factor mapping page
local notation "observedSource" => rc.atlasSources E st stInputs stBase splitBank hubWidth peers hostIndex oldCap
  f fee full total portPitch (Z).graph (Z).width C m stop (DescentRecordedRotorLayers.width f cap₀) factor mapping page
local notation "boughtAt" => fun table hdr=>ClosedReset.Recorded.reservationFields E hdr peers (S.hostSize i)
  portPitch dim (E.dim-dim) table (Nat.clog 2 (E.dim+2)) total (.lookup hostIndex .row)

set_option maxHeartbeats 700000 in
include stored packet in
/-- The physical book and its padded atlas are the two projections of the same
named reset. All per-gate address agreements then follow from that construction. -/
def issued_root_register (sameLanes : oldLanes=M₀)
    (books : book=observedBook) (rows : src=observedSource)
    (operands : src.OperandRoom (S.hostSize i) (2^dim) M₀ bw (rc.headerEnd book))
    (controls : DescentPackedZip.Source src.priorCap (fun (_ : Fin (S.hostSize i)) (_ : Block dim)=>(cap₀:Cell field))
        M₀ (rc.preparedMid book space mem) ∧
      DescentPackedZip.Source src.relativeDepth (fun (h : Fin (S.hostSize i)) (_ : Block dim)=>
        (Receiver.depthDigit dim (Fintype.card cap.V) (ClosedReset.Recorded.oldDepth b) h:Cell field))
        M₀ (rc.preparedMid book space mem))
    (short : M₀*max (field*guardInputs deg₀ (2^res) cap₀) (bits₀*stop)≤bw/2)
    (pos : 0<M₀) (floor : ℕ) (later : Memory bw) (past : rc.preparedEnd book≤floor)
    (room : floor<2^bw) (frame : ∀j,j<floor→later j=rc.preparedImage book space mem j)
    (elapsed : 0< i) (sorted : SourceSorted W cap.order)
    (baseRoom : max (max res (2^(Z).n)) (2^res)<2^field) (nRoom : (Z).n<field)
    (depthRoom : res+1<2^field) (capRoom : cap₀<2^field)
    (narrow : t≤field) (level : res<2^nbits) (one : 1<2^nbits) (amount : 2^res*total₀<2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows res (2^(Z).n)≤2^t)
    (active : 0<total₀) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*deg₀))
    (date : ℕ) (grain : z=S.grainAt G.b p date)
    (stopAt : ClosedReset.calendarBatchCount S n ctl.bitsR f cap₀ G.b date≤ stop) :
    RootRegister b hp whole a earlier board
      (guards (rc.headerEnd book) (S.hostSize i) (Groups*2^k) M₀ res (Z).n deg₀) later rfl rfl rfl:=by
  have layout : book=(baseSource).reserved (field:=field) (Z).graph (Z).width f height₀ C m stop
      (DescentRecordedRotorLayers.width f cap₀) mapping (S.hostSize i) factor hubWidth stInputs.roster stInputs.hubs
      rc.projectionEnd (Groups*2^k) M₀ st.n boughtAt page :=by
    rw [equalAxis]
    exact books
  have room₀ : (observedSource).OperandRoom (S.hostSize i) (2^dim) M₀ bw (rc.headerEnd observedBook):=by
    simpa only [←rows,←books] using operands
  have flagRoom (lo : Block res) : (S.hostSize i)*DescentSIMDLookup.chunks (2^dim) M₀≤(src.here lo).size:=by
    rw [rows]
    exact Nat.le_pow_clog (by decide) _
  have fits:=rc.issued_guard_addresses E st stInputs stBase splitBank hubWidth peers hostIndex oldCap
    f fee full total portPitch (Z).graph (Z).width C m stop (DescentRecordedRotorLayers.width f cap₀) factor
    mapping page room₀
  refine acquired_root_register (nodes:=nodes) (args:=args) (lanes:=lanes) (classes:=classes)
    (priceBits:=priceBits) (spanBits:=spanBits) b hp whole a earlier stored equalAxis rc book space mem hdr src raw packet
    baseSource (Z).graph factor hubWidth stInputs.roster stInputs.hubs rc.projectionEnd st.n boughtAt page sameLanes
    layout ?_ ?_ operands flagRoom ?_ ?_ short pos floor later past room frame elapsed sorted baseRoom nRoom
    depthRoom capRoom narrow level one amount shape active quotaPos degreePos date grain stopAt
  · subst book
    subst src
    exact fits.1
  · rw [rows]
    rfl
  · subst src
    exact controls
  · subst book
    exact fits.2

end
end Hierarchy.DescentPrimitivePalette

end OAI
