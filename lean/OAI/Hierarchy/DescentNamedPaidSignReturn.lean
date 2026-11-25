import OAI.Hierarchy.DescentNamedPaidChannels
import OAI.Hierarchy.DescentRecordedFundingTaps
import OAI.Hierarchy.DescentPhysicalResetHeadFrame

namespace OAI
/-! # Post-stencil paid arrival reads from the original stage-venue and selected physical basis -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentCompiler DescentSixParty DescentSixParty.ClosedReset.Window DescentDenseHostOrder
open DescentFundedCensus DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentPackedZip
open DescentSixParty.ClosedReset DescentPackedColony
open DescentGL DescentPaidResidentCount.Reset DescentSharedCableNames DescentIssuedFallbackPanel DescentColonies
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

local notation "c₀" => S.groupWidth k tail age
local notation "high" => c₀-e
local notation "low" => e+k
local notation "physical" => (⟨venue.hosts,S.groupCount age,2^k,venue.lanes,M₀,b,high,low,cc,(A).degree,(A).cap,M₀⟩:Setup)
local notation "phase₀" => (a).rootPhase u.shape foot u.count u.hub u.g u.Y u.roots w
local notation "signal" => (fun j:Fin (2*(fund).capacity)=>(Expr.lookup ((phase₀).tapped (j.cast (congrArg (2*·) run.signedCount))) .row))
private theorem split_sum {c e k : ℕ} (h : e≤c) : c-e+(e+k)=c+k:=by omega
local notation "ageDim" batch:arg => split_sum (k:=k) batch

local notation "stc" => (a).throughStencil u.shape foot u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "tc" => (a).throughStencilTicks u.shape foot u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "rc" => (a).rootPhase u.shape foot u.count u.hub u.g u.Y u.roots w
open DescentFallbackPeriod.Projected
open ThreeFlat.RAM PhysicalProcedure

/-- Every arrival word consumed by the post-reset paid census is an actual
previous signed slot, at the inverse image of the selected complete-cube GL
map. The date preserves the previous columns first, then the GL output. -/
theorem reached_paid_signs
    (batch : e≤previous) (small : previous≤c₀) (listed : u.roots=roots batch small)
    (degree : venue.degree=D) (capacity : venue.cap=(A).cap) (hosts : S.hostSize age=H)
    (wirePitch : venue.lanes=2^previous) (oldRoom : Fintype.card prior.V≤H)
    (ready : u.Ready) (peer : Fin H→Fin D→Option (Fin H)) (priorStart : ℕ)
    (before measured result : Memory w) (held : stageVenue prior oldRoom io venue.lanes b priorStart peer before)
    (wireRoom : ∀(x : Block k)(j : Fin (2*(A).cap)),(io.wire x.val j.val).Fits w priorStart ∧
      H*chunks (S.groupCount age) venue.lanes≤(io.wire x.val j.val).size)
    (floorLE : priorStart≤foot)
    (scanned : (stc).Exec before measured tc) (completed : u.throughOperandDate.Runs before result)
    (μ : DescentGL.Layout (high+low)) (chosen : HEq μ basis)
    (saved : measured (phase).saved=((DescentExterior.matrixCode μ).val:Word w)) :
    (∀j:Fin (2*(A).cap),Source (signal (j.cast (congrArg (2*·) capacity.symm)))
      (fun v hi=>encode sig (physical).donors (fun l=>fundingSign B oldRoom j v hi
        (l.cast (by change 2^(high+low-cc)=L;rw [ageDim (batch.trans small)])))) M₀ result) ∧
    result (phase).saved=((DescentExterior.matrixCode μ).val:Word w):=by
  obtain ⟨afterStencil,first,_,keep⟩:=(a).throughStencil_any_framed u.shape foot u.count u.hub u.g u.Y u.src
    u.sourceRows u.oldDegree w before ready.prime ready.stencil
  have equal:=exec_unique (stc) before measured afterStencil scanned first
  have stableLow : ∀i,i<priorStart→measured i=before i:=fun i lo=>(congrFun equal i).trans (keep i (.inl (lo.trans_le floorLE)))
  have earlier:=funding_old_wire (prior:=prior) oldRoom io peer before measured held wireRoom stableLow
  have wr : (rc).saved.Fits w (rc).origin :=
    ⟨u.bookFits.key.1,u.bookFits.key.2.1,by
      change (phase).saved+1≤(phase).endAddress
      exact stencil_saved_before (u:=u)⟩
  have cp:(a).c/2=(A).cap:=run.signedCount.symm.trans capacity
  have dd:(a).ports=(A).degree:=degree.trans prior.branch.symm
  have gc:2^c₀=S.groupCount age:=S.group_power ctl.base ctl.radix age
  have ratio : 2^(previous-e)*M₀=venue.lanes:=by rw [←pow_add,Nat.sub_add_cancel batch,wirePitch]
  have depthEq:k=high+low-c₀:=by rw [ageDim (batch.trans small)];omega
  have pack:M₀*2^(high+low-c₀)=2^low:=by rw [←depthEq,←pow_add]
  have oldRegisters:∀j x,(rc).old j x=io.wire x.val j.val:=by
    intro j x
    change u.roots.old j x=_
    rw [listed]
    rfl
  have oldReads:∀(j:Fin (2*(A).cap))(x:Block k),Reads (io.wire x.val j.val) (fun v gr=>DescentSignedCableCodec.encode
    (DescentPacking.PackedMatch.Local.Stage.Prepare.signed A (prior.order.trans Fin.valEmbedding) S prior.valid (Function.Embedding.refl _)
      (prior.vertex.trans (Fin.castLEEmb oldRoom)) x j v gr)) (2^(previous-e)*M₀) measured:=by
    rw [ratio];exact earlier
  have stamped:=u.projection_after ready scanned completed
  have rows:=funding_tap_rows («high»:=c₀-e) («low»:=e+k) (M:=2^e) B oldRoom (rc) dd cp rfl hosts gc B.commonDepth.symm depthEq (ageDim (batch.trans small))
    u.bookFits.toPrefixFits μ chosen (pow_add 2 e k) pack io measured result saved wr stamped oldRegisters oldReads
  constructor
  · intro j
    have read := rows j
    simp only [Fin.cast_cast, Setup.donors] at read ⊢
    exact read
  · have keyLo : (phase).saved<(rc).origin:=stencil_saved_before (u:=u)
    exact (stamped _ (keyLo.trans_le (rc).origin_le_projection)).trans
      (((rc).prefix_hardware u.bookFits.toPrefixFits measured).2.2 _ (.inl keyLo) |>.trans saved)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
