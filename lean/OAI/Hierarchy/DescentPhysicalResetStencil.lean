import OAI.Hierarchy.DescentPhysicalResetReceipt
import OAI.Hierarchy.DescentRecordedStencilCell
import OAI.Hierarchy.DescentResetPortTotal
import OAI.Hierarchy.DescentResetIssuedWords

namespace OAI
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000

open DescentIssuedFallbackPanel DescentGLPacked DescentPlainTerminal DescentPlainTerminal.Suffix DescentPackedZip
open DescentPackedFlowPair.Padded DescentPacking.PackedMatch.Local
namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (a : DescentDatedAddressBook.PhysicalReset) (floor : ℕ)
local notation "E" => a.estimator floor
local notation "P₀" => a.chart floor
local notation "C₀" => a.flow floor
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "owners" => Fintype.card input.V
local notation "full" => (A).wire*((A).z*G.b)*(A).cap


local notation "HP" => S.hostSize i
local notation "cc" => reset.terminals.commonDepth
local notation:max "xy" eqn:arg => (Equiv.cast (congrArg Block ((eqn).trans reset.keyWidth))).trans sourceDigits
local notation:max "hostIDs" eqn:arg => ((A).numberedHeader (xy eqn) input.vertex).site
local notation:max "savedAt" fresh:arg => fresh+(2^(E).dim)^(E).dim+(2^(E).dim)^(E).dim
local notation:max "firstAt" fresh:arg => (savedAt fresh)+1
local notation "originalWidth" => S.groupWidth k tail i+k

local notation "rootChart" => BankImage.Dated.chart (E).endAddress (P₀).routedHosts a.high a.low a.bits
local notation "fresh" => (P₀).remixEnd a.payload a.gain a.positive
local notation "pub" => a.successor.middle.stencil
local notation "batch" => 2^a.e
local notation "ratio" => 2^a.re
local notation "bitsS" => DescentPackedWalsh.rowBits a.hosts a.high
local notation "bitsP" => DescentPackedFlowPublication.Book.pitchBits a.hosts a.high

private theorem exec_of_same_program {w t t' : ℕ} {src dst : Memory w} {left right : Procedure w}
    (run : left.Exec src dst t) (code : left=right) (ticks : t=t') : right.Exec src dst t' := by
  subst right
  subst t'
  exact @run

include accepted in
/-- A recorded reset evaluated by the very fixed procedure which the calendar runs on every input. -/
theorem through_stencil_reserved {w : ℕ} (sh : a.StencilShape) (nbits tbits : ℕ)
    (dim : (E).dim=reset.reset.k) (hosts : a.hosts=HP) (ports : a.ports=D)
    (depth : a.depthCut=f) (budget : a.fullBudget=full) (quotaEq : a.classBound=K)
    (book : pub=stencilLayout (reset:=reset) (p:=p) E a.ports batch nbits tbits)
    (src count hub : Bank) (mem : Memory w) (low : ℕ)
    (prep : Procedure w) (t : ℕ)
    (programEq : a.prime floor src count (S.groupCount i) (A).degree w=prep.seq (((E).header (w:=w)).program.seq ((E).cpu w)))
    (tickEq : a.primeTicks floor (S.groupCount i) (A).degree w=t+(4+10*((E).staticEnd-(E).origin)+(E).clock))
    (primed :
      let digits:=xy dim
      let name:=hostIDs dim
      let loc:=PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports.ge)
      ∃prior : Memory w,prep.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=(E).high) (l:=(E).low) (b:=(E).precision) A name digits f K loc
          (E).depthRows.base (E).gainRows.base (E).start prior ∧
        PackedFlow.Canvas.Originals («HP»:=HP) (D:=a.ports) (u:=(E).high) (l:=(E).low) (b:=(E).precision)
          A name digits (P₀).first (C₀).middle (C₀).pitch prior ∧ ∀x<floor,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : (E).precision=S.localWalshBits p (E).dim f K)
    (localGain : (E).gainBits=gainBits (E).dim f K (S.censusBits p))
    (fit : (E).Fits w) (stage : (E).dim+1≤2^w) (small : (E).payload≤w)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (endRoom : (E).staticEnd<2^w) (issue : PhysicalTrajectory.Room w (E).dim (E).solveAt (E).bank)
    (siteEnd : (P₀).first+HP*2^(E).high≤(E).origin)
    (pairEnd : (C₀).middle+a.ports*(C₀).pitch≤(E).origin)
    (width : HP*2^(E).high≤(C₀).pitch)
    (back : (a.stencilPhase sh floor count hub g (2^reset.reset.n)).Room w)
    (oldCells : low≤ min floor (E).start) (beforeTables : low≤(E).origin)
    (oldCount : count.Fits w low) (oldHubs : hub.Fits w low) (oldRoster : a.previousRoster.Fits w low)
    (hubsRoom : HP≤hub.size) (portRoom : HP*(A).degree≤a.previousRoster.size)
    (counted : mem count.base=(owners:Word w)) (hubWord : ∀v,mem (hub.base+((hostIDs dim) v).val)=(((A).hub v).toNat:Word w))
    (neighbors : ∀v j,mem (a.previousRoster.base+(v.val*(A).degree+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster (D:=(A).degree) A (hostIDs dim) input.valid.host v j):Word w))
    (stored : (((rootChart).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length).Fits w fresh)
    (stores : ((1+a.ports)+(E).dim)*HP*2^(E).high≤(((rootChart).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length).size)
    (spectra : (firstContactBank E).Fits w (firstAt fresh)) (depthFit : (E).depthRows.Fits w (firstAt fresh))
    (packing : ratio*batch*2^((E).dim-cc)=2^(E).low) (capBits : 2^((E).dim-cc)*full<2^nbits)
    (levelBits : (E).dim-cc<2^nbits) (one : 1<2^nbits)
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w) (hostBits : HP<2^w)
    (roomCode : 2*DescentFallbackShapeTable.rows ((E).dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*(A).degree)) :
    let phase:=a.stencilPhase sh floor count hub g (2^reset.reset.n)
    ∃(μ : Layout (E).dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      (a.throughStencil sh floor count hub g (2^reset.reset.n) src (S.groupCount i) (A).degree w).Exec mem dst
        (a.throughStencilTicks sh floor count hub g (2^reset.reset.n) (S.groupCount i) (A).degree w) ∧
      dst phase.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<low,dst x=mem x) ∧
      StencilReservationWords (reset:=reset) E dim a.ports ports.ge dst ∧
      phase.S.OldOrder phase.X phase.base phase.bank g cc μ dst ∧
      PackedFlow.Padded.Published (h:=(E).high) (l:=(E).low) batch tbits phase.output
        ((hostIDs dim).toEmbedding.trans (Fin.castLEEmb input.valid.host))
        (fun v hi x=>(2*Stencil.shapeCode ((E).dim-cc) (2^reset.reset.n)
          (fieldsRelative cc (originalCell (reset:=reset) v ((rearrange reset.frame.basis).symm
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))))+
          (((A).hub v) || decide ((reset.frame.host v,group (reset.reset.placement.b (reset.frame.host v))
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))∈reset.reset.placement.keys)).toNat:ℕ)) dst := by
  intro phase
  let N:=2^cc/(ratio*batch)
  have factor:2^cc=N*(ratio*batch):=by
    simpa only [book,stencilLayout,PackedFlow.Padded.stencilBook] using sh.divides
  have hh:(E).hosts=HP*((E).dim+1+a.ports):=by change a.hosts*(a.high+a.low+1+a.ports)=_;rw [hosts];rfl
  have early:(E).origin≤(E).start:=((P₀).estimator_prefix a.payload a.gain a.positive).trans (Nat.le_add_right ..)
  have big:HP*2^(E).high≤2^bitsS:=by rw [←hosts];exact DescentPackedWalsh.rows_le _ _
  have peer:HP*2^(E).high≤2^bitsP:=by
    rw [←hosts,DescentPackedFlowPublication.Book.pitchBits,pow_add]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
  have initial:(E).endAddress≤fresh:=((P₀).estimator_range a.payload a.gain a.positive).2.2
  let chart:=stencilLayout (reset:=reset) (p:=p) E a.ports batch nbits tbits
  have table:(a.stencilPhase sh floor count hub g (2^reset.reset.n)).S=chart:=book
  have lowR : ∀j : Fin a.ports,(⟨(C₀).middle+j.val*(C₀).pitch,bitsP⟩:Bank).Fits w (E).endAddress :=
    fun j => back.peers (Fin.cast sh.ports.symm j)
  have area := back.area
  change Size rootChart (((1+(pub).maxPorts)+(E).dim)*(pub).hosts) (E).high (E).low (pub).b w at area
  rw [book] at area
  have totalBound := back.total
  dsimp only [DescentDatedAddressBook.PhysicalReset.stencilPhase, PackedFlow.ResetMiddle.endAddress,
    PackedFlow.ResetMiddle.base, PackedFlow.ResetMiddle.first, PackedFlow.ResetMiddle.saved, PackedFlow.ResetMiddle.dim,
    PackedFlow.ResetMiddle.width, PackedFlow.ResetMiddle.sheets] at totalBound
  rw [book] at totalBound
  have shortBound := back.short
  change (pub).M*max ((pub).n*Stencil.count (pub).r ((pub).degree+(pub).degree)) ((pub).t*2^(pub).r)≤w/2 at shortBound
  rw [book] at shortBound
  have wordBound := back.word
  change (pub).n*(pub).M≤w at wordBound
  rw [book] at wordBound
  obtain ⟨μ,dst,tied,runs,_,storedM,kept,readback,ordered,words⟩:=accepted.issued_stencil_reserved E dim mem prep t a.ports ports.ge hh
    (P₀).first (C₀).middle (C₀).pitch floor width (siteEnd.trans early) (pairEnd.trans early)
    (.inl siteEnd) (.inl pairEnd) primed grain old branch live localBits localGain fit stage small score endRoom issue
    rootChart (E).endAddress bitsS bitsP a.positive le_rfl back.counts lowR big peer area back.words
    back.fence back.power back.offsets back.switches back.planes fresh back.kept back.saveRoom
    count hub a.previousRoster low oldCells beforeTables initial oldCount oldHubs oldRoster hubsRoom portRoom
    counted hubWord neighbors stored stores spectra depthFit ratio batch N nbits tbits packing factor (Nat.two_pow_pos _) (Nat.two_pow_pos _)
    totalBound shortBound wordBound capBits levelBits one headerBits hostBits roomCode positiveD
  let peerBanks (ports' : ℕ) (j : Fin ports') : Bank := ⟨(C₀).middle+j.val*(C₀).pitch,bitsP⟩
  let siteBank : Bank := ⟨(P₀).first,bitsS⟩
  have moveEq := congrArg (fun n => gathered rootChart (E).endAddress (E).solveAt siteBank
    (peerBanks n) HP a.high a.low w) sh.ports
  have feeEq := congrArg (fun n => gatherFee rootChart (E).endAddress (E).solveAt siteBank
    (peerBanks n) HP a.high a.low) sh.ports
  have highE : (E).high = a.high := rfl
  have lowE : (E).low = a.low := rfl
  have dimE : (E).dim = a.high + a.low := rfl
  refine ⟨μ,dst,tied,?_,?_,kept,readback,?_,?_⟩
  · apply exec_of_same_program @runs
    · dsimp only [DescentDatedAddressBook.PhysicalReset.throughStencil, DescentDatedAddressBook.PhysicalReset.stencilPhase,
        PackedFlow.ResetMiddle.code, PackedFlow.ResetMiddle.first, PackedFlow.ResetMiddle.saved, PackedFlow.ResetMiddle.chip,
        PackedFlow.ResetMiddle.dim, PackedFlow.ResetMiddle.stages, PackedFlow.ResetMiddle.base, PackedFlow.ResetMiddle.bank,
        PackedFlow.ResetMiddle.sheets, PackedFlow.ResetMiddle.width, middle]
      simp only [programEq,book,stencilLayout,PackedFlow.Padded.stencilBook,depth,budget,quotaEq]
      rw [moveEq]
      simp only [dimE, highE, lowE, StencilBook.r, N]
      rfl
    · dsimp only [DescentDatedAddressBook.PhysicalReset.throughStencilTicks, DescentDatedAddressBook.PhysicalReset.stencilPhase,
        PackedFlow.ResetMiddle.time, PackedFlow.ResetMiddle.first, PackedFlow.ResetMiddle.saved, PackedFlow.ResetMiddle.chip,
        PackedFlow.ResetMiddle.dim, PackedFlow.ResetMiddle.stages, PackedFlow.ResetMiddle.base, PackedFlow.ResetMiddle.bank,
        PackedFlow.ResetMiddle.sheets, PackedFlow.ResetMiddle.width, middleTime]
      simp only [tickEq,book,stencilLayout,PackedFlow.Padded.stencilBook,depth,budget]
      rw [feeEq]
      simp only [dimE, highE, lowE, StencilBook.r, N]
      rfl
  · exact storedM
  · dsimp only [phase,PackedFlow.ResetMiddle.base,PackedFlow.ResetMiddle.bank,PackedFlow.ResetMiddle.sheets,
      PackedFlow.ResetMiddle.width,PackedFlow.ResetMiddle.first,PackedFlow.ResetMiddle.saved,PackedFlow.ResetMiddle.dim,
      DescentDatedAddressBook.PhysicalReset.stencilPhase]
    rw [book]
    with_unfolding_all exact ordered
  · dsimp only [phase,PackedFlow.ResetMiddle.output,PackedFlow.ResetMiddle.base,PackedFlow.ResetMiddle.sheets,
      PackedFlow.ResetMiddle.width,PackedFlow.ResetMiddle.first,PackedFlow.ResetMiddle.saved,PackedFlow.ResetMiddle.dim,
      DescentDatedAddressBook.PhysicalReset.stencilPhase]
    rw [book]
    with_unfolding_all exact words


include accepted in
theorem through_stencil {w : ℕ} (sh : a.StencilShape) (nbits tbits : ℕ)
    (dim : (E).dim=reset.reset.k) (hosts : a.hosts=HP) (ports : a.ports=D)
    (depth : a.depthCut=f) (budget : a.fullBudget=full) (quotaEq : a.classBound=K)
    (book : pub=stencilLayout (reset:=reset) (p:=p) E a.ports batch nbits tbits)
    (src count hub : Bank) (mem : Memory w) (low : ℕ)
    (prep : Procedure w) (t : ℕ)
    (programEq : a.prime floor src count (S.groupCount i) (A).degree w=prep.seq (((E).header (w:=w)).program.seq ((E).cpu w)))
    (tickEq : a.primeTicks floor (S.groupCount i) (A).degree w=t+(4+10*((E).staticEnd-(E).origin)+(E).clock))
    (primed :
      let digits:=xy dim
      let name:=hostIDs dim
      let loc:=PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports.ge)
      ∃prior : Memory w,prep.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=(E).high) (l:=(E).low) (b:=(E).precision) A name digits f K loc
          (E).depthRows.base (E).gainRows.base (E).start prior ∧
        PackedFlow.Canvas.Originals («HP»:=HP) (D:=a.ports) (u:=(E).high) (l:=(E).low) (b:=(E).precision)
          A name digits (P₀).first (C₀).middle (C₀).pitch prior ∧ ∀x<floor,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : (E).precision=S.localWalshBits p (E).dim f K)
    (localGain : (E).gainBits=gainBits (E).dim f K (S.censusBits p))
    (fit : (E).Fits w) (stage : (E).dim+1≤2^w) (small : (E).payload≤w)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (endRoom : (E).staticEnd<2^w) (issue : PhysicalTrajectory.Room w (E).dim (E).solveAt (E).bank)
    (siteEnd : (P₀).first+HP*2^(E).high≤(E).origin)
    (pairEnd : (C₀).middle+a.ports*(C₀).pitch≤(E).origin)
    (width : HP*2^(E).high≤(C₀).pitch)
    (back : (a.stencilPhase sh floor count hub g (2^reset.reset.n)).Room w)
    (oldCells : low≤ min floor (E).start) (beforeTables : low≤(E).origin)
    (oldCount : count.Fits w low) (oldHubs : hub.Fits w low) (oldRoster : a.previousRoster.Fits w low)
    (hubsRoom : HP≤hub.size) (portRoom : HP*(A).degree≤a.previousRoster.size)
    (counted : mem count.base=(owners:Word w)) (hubWord : ∀v,mem (hub.base+((hostIDs dim) v).val)=(((A).hub v).toNat:Word w))
    (neighbors : ∀v j,mem (a.previousRoster.base+(v.val*(A).degree+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster (D:=(A).degree) A (hostIDs dim) input.valid.host v j):Word w))
    (stored : (((rootChart).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length).Fits w fresh)
    (stores : ((1+a.ports)+(E).dim)*HP*2^(E).high≤(((rootChart).chosen (E).dim).bank (DescentGLNielsen.schedule (E).dim).length).size)
    (spectra : (firstContactBank E).Fits w (firstAt fresh)) (depthFit : (E).depthRows.Fits w (firstAt fresh))
    (packing : ratio*batch*2^((E).dim-cc)=2^(E).low) (capBits : 2^((E).dim-cc)*full<2^nbits)
    (levelBits : (E).dim-cc<2^nbits) (one : 1<2^nbits)
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w) (hostBits : HP<2^w)
    (roomCode : 2*DescentFallbackShapeTable.rows ((E).dim-cc) (2^reset.reset.n)≤2^tbits)
    (positiveD : 0<32*Nat.clog 2 (2*(A).degree)) :
    let phase:=a.stencilPhase sh floor count hub g (2^reset.reset.n)
    ∃(μ : Layout (E).dim) (dst : Memory w), HEq μ reset.frame.basis ∧
      (a.throughStencil sh floor count hub g (2^reset.reset.n) src (S.groupCount i) (A).degree w).Exec mem dst
        (a.throughStencilTicks sh floor count hub g (2^reset.reset.n) (S.groupCount i) (A).degree w) ∧
      dst phase.saved=((DescentExterior.matrixCode μ).val:Word w) ∧ (∀x<low,dst x=mem x) ∧
      phase.S.OldOrder phase.X phase.base phase.bank g cc μ dst ∧
      PackedFlow.Padded.Published (h:=(E).high) (l:=(E).low) batch tbits phase.output
        ((hostIDs dim).toEmbedding.trans (Fin.castLEEmb input.valid.host))
        (fun v hi x=>(2*Stencil.shapeCode ((E).dim-cc) (2^reset.reset.n)
          (fieldsRelative cc (originalCell (reset:=reset) v ((rearrange reset.frame.basis).symm
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))))+
          (((A).hub v) || decide ((reset.frame.host v,group (reset.reset.placement.b (reset.frame.host v))
            (join (reset.frame.enough.trans (Nat.sub_le ..)) hi
              (Fin.cast (congrArg (fun z=>2^(z-cc)) (dim.trans reset.keyWidth)) x)))∈reset.reset.placement.keys)).toNat:ℕ)) dst := by
  intro phase
  obtain ⟨μ,dst,tied,run,stored,kept,_,orders,words⟩:=
    accepted.through_stencil_reserved a floor sh nbits tbits dim hosts ports depth budget quotaEq book src count hub mem low prep t programEq tickEq primed grain old branch live localBits localGain fit stage small score endRoom issue siteEnd pairEnd width back oldCells beforeTables oldCount oldHubs oldRoster hubsRoom portRoom counted hubWord neighbors stored stores spectra depthFit packing capBits levelBits one headerBits hostBits roomCode positiveD
  exact ⟨μ,dst,tied,run,stored,kept,orders,words⟩

end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
