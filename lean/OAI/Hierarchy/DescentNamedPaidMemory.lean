import OAI.Hierarchy.DescentPhysicalFundedRows
import OAI.Hierarchy.DescentFundedStageReturn
import OAI.Hierarchy.DescentRecordedVenueDateImage

namespace OAI
/-! # The genuine pre-compaction paid array in the returned reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentCompiler DescentSixParty DescentSixParty.ClosedReset.Window DescentDenseHostOrder
open DescentFundedCensus DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentPackedZip
open DescentSixParty.ClosedReset DescentPackedColony
open DescentGL DescentPaidResidentCount.Reset DescentSharedCableNames DescentIssuedFallbackPanel DescentColonies
open DescentCommonHost DescentRelativeContacts DescentPlainTerminal DescentPlainTerminal.Suffix DescentCommonPalette
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k age z D n h C f g cut tail wire hist : ℕ}
    {ctl : ResetRates G S k D n h C f g cut tail} {prior : Reached W G q ε S k age z D wire hist}
    (B : ClosedReset prior ctl) {p : ℕ} (recorded : B.Recorded p)
    (drift maxDegree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
    (venue : StageVenueTail.Date) (io : Dated.Operands) (floor : ℕ)
local notation "A" => prior.placement
local notation "Z" => B.reset
local notation "dep" => GroupStage.depthBound D n f g
local notation "rel" => ((Z).k-B.terminals.commonDepth)
local notation "pool" => roster (Z).graph rel dep
local notation "a" => named G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "foot" => (a).stageStart floor
local notation "cens" => (a).successor.venue.census
local notation "fund" => (a).successor.funded
local notation "roots" => namedRoots G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor
local notation "atlas" => namedAtlas G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR
  oldLanes primitiveLanes printedBits venue io floor
variable {w : ℕ} {u : (named G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR oldLanes primitiveLanes printedBits venue io.wire io.roster floor).DateInputs ((named G S ctl.board k tail age p f g drift maxDegree payload e previous M nextM C ctl.bitsR oldLanes primitiveLanes printedBits venue io.wire io.roster floor).stageStart floor) w} (run : u.FinalInputs)
local notation "phase" => (a).stencilPhase u.shape foot u.count u.hub u.g u.Y
local notation "flag" j:arg => presence («a»:=a) (floor:=foot) j
local notation "samePorts" => fundedPorts (funded_residual B) B.dimension run.ports

local notation "b₀" => (a).rebased foot
local notation "v₀" => (a).successor
local notation "base" => (v₀).fundedEnd b₀
local notation "start" => (v₀).finalEnd b₀
local notation "key" => (⟨(phase).saved,0⟩:Bank)
local notation "cc" => B.terminals.commonDepth
local notation "small₀" => (S.groupWidth k tail age+k-cc)
local notation "L" => 2^small₀
local notation "b" => (cens).bits
local notation "H" => venue.hosts
local notation "M₀" => 2^e
local notation "field" => u.roots.field
local notation "header" => (phase).S.t
local notation "sig" => DescentSignedCableCodec.width (A).degree (A).cap
local notation "mass" => (A).wire*((A).z*G.b)*(A).cap
local notation "block" => S.resetInputDigits ctl.base ctl.radix age
local notation "basis" => B.frame.basis
local notation "enough₀" => B.frame.enough.trans (Nat.sub_le ..)
local notation "oldIx" hi:arg lo:arg => (rearrange basis).symm (join enough₀ hi lo)
local notation "after" m:arg => (fund).memory start run.earlier key m
local notation "paidRAM" m:arg => DescentFundedCensus.memory run.jobs base (after m)
local notation "jCount" eg:arg => source_rows (p:=p) B drift maxDegree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor eg

/-- The array contains one genuine paid count for every original shape, old
host, and high group, including physically unused hosts and the final partial word.
These are exactly the words read by the dense venue compactor. -/
theorem paid_memory
    (batch : e≤previous) (small : previous≤S.groupWidth k tail age)
    (rootRows : u.roots=roots batch small) (menu : u.atlas=atlas u.shape u.count)
    (grain : z=S.grainAt G.b p (age+1)) (degree : venue.degree=D) (capacity : venue.cap=(A).cap)
    (oldRoom : Fintype.card prior.V≤H) (mem : Memory w) (safe : run.Room)
    (stencil : Fin H→Block cc→Cell (header*L)) (incoming : Fin (2*(A).cap)→Fin H→Block cc→Fin L→Cell sig)
    (snap : PaddedSnapshot B oldRoom field) (fBits : ℕ)
    (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount age)) prior.V k↪ℕ)
    (panel : ∀v hi,stencil ((prior.vertex v).castLE oldRoom) hi=
      encode header L (Recorded.realPanel (reset:=B) rfl basis fBits header v hi))
    (signed : ∀j v hi lo,incoming j ((prior.vertex v).castLE oldRoom) hi lo=
      DescentSignedCableCodec.encode (Stage.signedPanel A order S prior.valid names
        (((block (oldIx hi lo)).1,v),(block (oldIx hi lo)).2) j))
    (up : small₀<2^fBits) (one : 1<2^fBits) (enough : L*mass<2^fBits)
    (legal : 2*DescentFallbackShapeTable.rows small₀ (2^(Z).n)≤2^header)
    (active : 0< mass) (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*(A).degree))
    (countFits : mass<2^b) (arrivalFits : 2*(A).cap<2^b)
    (stored : Source (samePorts).stencil stencil M₀ (after mem))
    (old : Source (samePorts).old (ownOld («b»:=b) B oldRoom) M₀ (after mem))
    (relay : Source (samePorts).relay (ownArrivals («b»:=b) B incoming) M₀ (after mem))
    (presence : ∀j:Fin (pool).card,Source (flag (j.cast (jCount degree).symm))
      (Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom) j) M₀ (after mem))
    (rootsRead : ∀s t,Source ((samePorts).bank s t) (savedInput B oldRoom snap) M₀ (after mem))
    (j : Fin (pool).card) (pos : Row H (2^cc) M₀) :
    (paidRAM mem) (((v₀).venue.original base).base+j.val*(H*chunks (2^cc) M₀)+(row H (2^cc) M₀ pos).val)=
      ((data (fun v hi=>payable (precision:=b) B recorded oldRoom (finProdFinEquiv (v,j)) hi) pos).val:Word w) :=by
  have rewriteRows:=funded_array B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor run batch small rootRows menu grain degree capacity base (after mem)
  have fit:=(funded_room_array B recorded drift maxDegree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor run batch small rootRows menu grain degree capacity base).mp safe.jobs
  let seen:=fun j:Fin (pool).card=>flag (j.cast (jCount degree).symm)
  have received:=issued_funded_read B recorded oldRoom stencil incoming snap samePorts seen base (after mem) fit
    order names panel signed up one enough legal active quotaPos degreePos countFits arrivalFits stored old relay presence rootsRead j pos
  rw [rewriteRows.2.2]
  have same : ((v₀).venue.original base).base=
      (⟨(pool).card,H,2^cc,M₀,b,(cens).broadcast⟩:Shape).out base:=by
    change base+2*((cens).jobs+1)*2^((cens).broadcast*M₀)=_
    rw [jCount degree]
    rfl
  rw [same]
  exact received

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
