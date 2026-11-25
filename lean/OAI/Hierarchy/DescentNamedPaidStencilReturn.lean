import OAI.Hierarchy.DescentNamedPaidSignReturn
import OAI.Hierarchy.DescentPreparedRootArrays

namespace OAI
/-! # The selected, measured root stencil reaches the original funded-count instruction -/
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
local notation "stc" => (a).throughStencil u.shape foot u.count u.hub u.g u.Y u.src u.sourceRows u.oldDegree w
local notation "tc" => (a).throughStencilTicks u.shape foot u.count u.hub u.g u.Y u.sourceRows u.oldDegree w
local notation "rc" => (a).rootPhase u.shape foot u.count u.hub u.g u.Y u.roots w
open DescentPlainTerminal.Suffix DescentFallbackPeriod DescentFallbackPeriod.Projected
open ThreeFlat.RAM PhysicalProcedure

local notation "rawHost" pad:arg => prior.vertex.trans (Fin.castLEEmb pad)

private theorem basis_column {u₀ nbits M t w₀ dest : ℕ} (room : Fintype.card prior.V≤H)
    (at_ : u₀=c₀+k) (μ : DescentGL.Layout u₀) (won : HEq μ basis) (mem : Memory w₀)
    (stored : ∃v:Fin H→Block cc→Block (u₀-cc)→Cell t,
      (∀pos:Row H (2^cc) M,mem (dest+(row H (2^cc) M pos).val)=
        ((data (fun h hi=>encode t (2^(u₀-cc)) (v h hi)) pos).val:Word w₀)) ∧
      ∀vertex hi lo,v ((rawHost room) vertex) hi lo=Recorded.realPanel (reset:=B) at_ μ nbits t vertex hi lo) :
    ∃v:Fin H→Block cc→Fin L→Cell t,
      (∀pos:Row H (2^cc) M,mem (dest+(row H (2^cc) M pos).val)=
        ((data (fun h hi=>encode t L (v h hi)) pos).val:Word w₀)) ∧
      ∀vertex hi lo,v ((rawHost room) vertex) hi lo=Recorded.realPanel (reset:=B) rfl basis nbits t vertex hi lo:=by
  subst u₀
  obtain rfl:=eq_of_heq won
  exact stored

/-- The recorded unmodified stencil is the physical input to the paid-count
lookup for all rows, including padded hosts and the last packed group. -/
theorem reached_paid_stencil {a₁ a₂ fBits : ℕ}
    (ready : u.Ready) (safe : run.Room) (oldRoom : Fintype.card prior.V≤H)
    (actors : (cens).jobs=(v₀).actor.shapes) (has : 0<(v₀).actor.shapes)
    (actorRows : (v₀).actor.hosts*(v₀).actor.chunksPerHost=H*chunks (2^cc) M₀)
    (hosts : S.hostSize age=H)
    (before measured result : Memory w) (scanned : (stc).Exec before measured tc)
    (completed : u.throughOperandDate.Runs before result)
    (at_ : a₁+a₂=c₀+k) (μ : DescentGL.Layout (a₁+a₂)) (won : HEq μ basis)
    (printed : PackedFlow.Padded.Published (h:=a₁) (l:=a₂) M₀ header (phase).output (rawHost oldRoom)
      (Recorded.realPanel (reset:=B) at_ μ fBits header) measured) :
    ∃stencil : Fin H→Block cc→Cell (header*L),Source (samePorts).stencil stencil M₀ result ∧
      ∀v hi,stencil ((prior.vertex v).castLE oldRoom) hi=encode header L
        (Recorded.realPanel (reset:=B) rfl basis fBits header v hi):=by
  have reached:=u.projection_after ready scanned completed
  have rows:(phase).S.rows=H*chunks (2^cc) M₀:=by
    change S.hostSize age*chunks (2^c₀) M₀=_
    rw [hosts,B.commonDepth]
  have stop:(phase).output+H*chunks (2^cc) M₀=(rc).origin:=by
    change _=(phase).S.endAddress (phase).base
    rw [StencilBook.output_end,rows]
    rfl
  have num:=basis_column (B:=B) (venue:=venue) (oldRoom) at_ μ won measured printed
  obtain ⟨actual,read,real⟩:=num
  have priorRead:∀pos:Row H (2^cc) M₀,result ((phase).output+(row H (2^cc) M₀ pos).val)=
      ((data (fun v hi=>encode header L (actual v hi)) pos).val:Word w):=by
    intro pos
    let ix:=(phase).output+(row H (2^cc) M₀ pos).val
    have low:ix<(rc).origin:=stop ▸ Nat.add_lt_add_left (row H (2^cc) M₀ pos).isLt _
    exact (reached ix (low.trans_le (rc).origin_le_projection)).trans
      (((rc).prefix_hardware u.bookFits.toPrefixFits measured).2.2 ix (.inl low) |>.trans (read pos))
  let bk : Bank:=⟨(phase).output,Nat.clog 2 ((v₀).actor.hosts*(v₀).actor.chunksPerHost)⟩
  have capacity : H*chunks (2^cc) M₀≤bk.size:=by
    change _≤2^Nat.clog 2 _
    rw [actorRows]
    exact Nat.le_pow_clog (by decide) _
  have fit:bk.Fits w start:=(run.prior_funding_ports ready safe actors has).2.1.1
  have oldPlane:=source_column bk start fit result (fun v hi=>encode header L (actual v hi)) capacity priorRead
  refine ⟨fun v hi=>encode header L (actual v hi),?_,?_⟩
  · rw [(funded_registers (funded_residual B) B.dimension run.ports).2.2]
    exact oldPlane
  · intro v hi
    exact congrArg (encode header L) (funext (real v hi))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
