import OAI.Hierarchy.DescentRecordedCanvas
import OAI.Hierarchy.DescentResetRowsAfterSolver

namespace OAI
/-! # From original packed sockets through the measured basis to the actual remixed fields -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader
open DescentBaseProfile DescentBaseVariance DescentWalshPrecision DescentPackedWalsh
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentGLPacked.BankImage DescentGLPacked.BankImage.Dated ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (accepted : reset.Recorded p) (E : EstimatorArena)
local notation "A" => input.placement
local notation "K" => quota S.rounds
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "owners" => Fintype.card input.V
local notation "full" => (A).wire*((A).z*G.b)*(A).cap

include accepted in
theorem signed_remix_parts {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank)
    (C' : Chart) (origin bitSites bitPeers : ℕ) (pcap : 0<E.precision)
    (base : E.endAddress≤origin)
    (siteFit : (⟨siteBase,bitSites⟩:Bank).Fits w origin)
    (pairFit : ∀j : Fin maxPorts,(⟨peerBase+j.val*pitch,bitPeers⟩:Bank).Fits w origin)
    (rows : S.hostSize i*2^E.high≤2^bitSites) (paidRows : S.hostSize i*2^E.high≤2^bitPeers)
    (area : Size C' (((1+maxPorts)+E.dim)*S.hostSize i) E.high E.low E.precision w)
    (endWords : wordEnd origin E.high E.low≤C'.input.base) (gap : C'.input.base+C'.input.size≤C'.flags)
    (scaleWords : (powers origin E.dim).Fits w C'.input.base)
    (addresses : (cols origin E.dim).offsets.Fits w C'.input.base)
    (switches : (cols origin E.dim).switches.Fits w C'.input.base)
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    let ps := fun j : Fin maxPorts=>(⟨peerBase+j.val*pitch,bitPeers⟩:Bank)
    let sites : Bank:=⟨siteBase,bitSites⟩
    let H:=S.hostSize i
    let nG:=((1+maxPorts)+E.dim)*H
    let tables:=controlImage (h:=E.high) (l:=E.low) (w:=w) origin pcap
    let route:=routes C' nG E.high E.low E.precision w
    let move:=gathered C' origin E.solveAt sites ps H E.high E.low w
    let fee:=gatherFee C' origin E.solveAt sites ps H E.high E.low
    let previous:=prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))
    let suffix:=(tables.program.seq route.program).seq move
    ∃(prior : Memory w) (μ : DescentGL.Layout E.dim) (dst : Memory w),HEq μ reset.frame.basis ∧
      (previous.seq suffix).Exec mem dst ((t+(4+10*(E.staticEnd-E.origin)+E.clock))+
        ((8+10*(tables.length+route.length))+fee)) ∧ CheapCode suffix ∧
      (∀channel,DescentGLPacked.Dense (h:=E.high) (l:=E.low)
        (slice (((C'.chosen E.dim).bank (DescentGLNielsen.schedule E.dim).length).base) H (2^E.high) channel)
        (fun v x=>PackedFlow.Channels.values
          (fun (v:Fin H) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
          (fun (j : Fin maxPorts) (v:Fin H) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
          pcap channel v ((rearrange μ).symm x)) dst) ∧
      (∀a : Fin E.dim,dst (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→dst a=mem a) ∧
      (previous.Exec mem (E.image (E.literal prior)) (t+(4+10*(E.staticEnd-E.origin)+E.clock))) ∧
      (suffix.Exec (E.image (E.literal prior)) dst ((8+10*(tables.length+route.length))+fee)) ∧
      (∀a<origin,dst a=E.image (E.literal prior) a) ∧
      E.FirstTotals (publicLoad E dim maxPorts ports hostCount) (E.image (E.literal prior)) ∧
      ∀v,E.image (E.literal prior) (E.depthRows.base+(name v).val*(E.dim+1))=
        (((A).mixerHeader digits name).depth A f v:Word w) := by
  intro digits name ps sites H nG tables route move fee previous suffix
  obtain ⟨prior,μ,_prep,equal,earlier,selected,_action,raw,low,totals,depth⟩:=accepted.after_canvas_named E dim mem prepare t maxPorts ports hostCount
    siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed grain old branch live localBits localGain
    fit stage small score endRoom issue
  obtain ⟨dst,run,cheap,published,outer⟩:=Dated.selected_fields C' origin E.solveAt sites ps
    (fun (v:Fin H) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
    (fun (j : Fin maxPorts) (v:Fin H) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
    μ (E.image (E.literal prior)) selected base raw.load raw.flow rows (fun _=>paidRows) siteFit pairFit area pcap endWords gap
    scaleWords addresses switches planes
  refine ⟨prior,μ,dst,equal,earlier.then run,cheap,published,?_,?_,earlier,run,fun a ha=>outer _ (Or.inl ha),totals,depth⟩
  · intro j
    apply (outer _ (.inl ?_)).trans (selected j)
    have hi:=Nat.mul_le_mul_right (3*2^E.dim+1) j.isLt
    rw [Nat.succ_mul] at hi
    dsimp [EstimatorArena.endAddress,PhysicalTrajectory.pointer,PhysicalTrajectory.outputBase,DescentGL.RowStageRAM.placed] at base ⊢
    omega
  · intro a ha away
    have prior:E.start≤E.endAddress:=by rw [E.endAddress_eq];omega
    exact (outer _ (.inl ((lt_min_iff.mp ha).2.trans_le (prior.trans base)))).trans (low a ha away)

include accepted in
theorem signed_remix_named {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank)
    (C' : Chart) (origin bitSites bitPeers : ℕ) (pcap : 0<E.precision)
    (base : E.endAddress≤origin)
    (siteFit : (⟨siteBase,bitSites⟩:Bank).Fits w origin)
    (pairFit : ∀j : Fin maxPorts,(⟨peerBase+j.val*pitch,bitPeers⟩:Bank).Fits w origin)
    (rows : S.hostSize i*2^E.high≤2^bitSites) (paidRows : S.hostSize i*2^E.high≤2^bitPeers)
    (area : Size C' (((1+maxPorts)+E.dim)*S.hostSize i) E.high E.low E.precision w)
    (endWords : wordEnd origin E.high E.low≤C'.input.base) (gap : C'.input.base+C'.input.size≤C'.flags)
    (scaleWords : (powers origin E.dim).Fits w C'.input.base)
    (addresses : (cols origin E.dim).offsets.Fits w C'.input.base)
    (switches : (cols origin E.dim).switches.Fits w C'.input.base)
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    let ps := fun j : Fin maxPorts=>(⟨peerBase+j.val*pitch,bitPeers⟩:Bank)
    let sites : Bank:=⟨siteBase,bitSites⟩
    let H:=S.hostSize i
    let nG:=((1+maxPorts)+E.dim)*H
    let tables:=controlImage (h:=E.high) (l:=E.low) (w:=w) origin pcap
    let route:=routes C' nG E.high E.low E.precision w
    let move:=gathered C' origin E.solveAt sites ps H E.high E.low w
    let fee:=gatherFee C' origin E.solveAt sites ps H E.high E.low
    let previous:=prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))
    let suffix:=(tables.program.seq route.program).seq move
    ∃(prior : Memory w) (μ : DescentGL.Layout E.dim) (dst : Memory w),HEq μ reset.frame.basis ∧
      (previous.seq suffix).Exec mem dst ((t+(4+10*(E.staticEnd-E.origin)+E.clock))+
        ((8+10*(tables.length+route.length))+fee)) ∧ CheapCode suffix ∧
      (∀channel,DescentGLPacked.Dense (h:=E.high) (l:=E.low)
        (slice (((C'.chosen E.dim).bank (DescentGLNielsen.schedule E.dim).length).base) H (2^E.high) channel)
        (fun v x=>PackedFlow.Channels.values
          (fun (v:Fin H) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
          (fun (j : Fin maxPorts) (v:Fin H) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
          pcap channel v ((rearrange μ).symm x)) dst) ∧
      (∀a : Fin E.dim,dst (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→dst a=mem a) ∧
      (∀a<origin,dst a=E.image (E.literal prior) a) ∧
      E.FirstTotals (publicLoad E dim maxPorts ports hostCount) (E.image (E.literal prior)) ∧
      ∀v,E.image (E.literal prior) (E.depthRows.base+(name v).val*(E.dim+1))=
        (((A).mixerHeader digits name).depth A f v:Word w) := by
  intro digits name ps sites H nG tables route move fee previous suffix
  obtain ⟨prior,μ,dst,eq,run,cheap,ok,read,old,_,_,low,tot,depth⟩:=accepted.signed_remix_parts E dim mem prepare t
    maxPorts ports hostCount siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed
    grain old branch live localBits localGain fit stage small score endRoom issue C' origin bitSites bitPeers
    pcap base siteFit pairFit rows paidRows area endWords gap scaleWords addresses switches planes
  exact ⟨prior,μ,dst,eq,run,cheap,ok,read,old,low,tot,depth⟩

include accepted in
theorem signed_remix {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
    (maxPorts : ℕ) (ports : D≤ maxPorts) (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts))
    (siteBase peerBase pitch keep : ℕ) (width : S.hostSize i*2^E.high≤pitch)
    (siteEnd : siteBase+S.hostSize i*2^E.high≤E.start) (peerEnd : peerBase+maxPorts*pitch≤E.start)
    (siteSave : siteBase+S.hostSize i*2^E.high≤E.origin ∨ E.staticEnd≤ siteBase)
    (peerSave : peerBase+maxPorts*pitch≤E.origin ∨ E.staticEnd≤peerBase)
    (primed :
      let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
      let name := ((A).numberedHeader digits input.vertex).site
      let loc := PackedFlow.Canvas.loc A name digits f input.valid.host (input.branch.le.trans ports)
      ∃prior : Memory w,prepare.Exec mem prior t ∧
        PackedFlow.Canvas.Loaded (u:=E.high) (l:=E.low) (b:=E.precision) A name digits f K loc
          E.depthRows.base E.gainRows.base E.start prior ∧
        PackedFlow.Canvas.Originals (HP:=S.hostSize i) (D:=maxPorts) (u:=E.high) (l:=E.low) (b:=E.precision)
          A name digits siteBase peerBase pitch prior ∧ ∀x<keep,prior x=mem x)
    (grain : z=S.grainAt G.b p (i+1)) (old : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (live : 0<full)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (endRoom : E.staticEnd<2^w)
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank)
    (C' : Chart) (origin bitSites bitPeers : ℕ) (pcap : 0<E.precision)
    (base : E.endAddress≤origin)
    (siteFit : (⟨siteBase,bitSites⟩:Bank).Fits w origin)
    (pairFit : ∀j : Fin maxPorts,(⟨peerBase+j.val*pitch,bitPeers⟩:Bank).Fits w origin)
    (rows : S.hostSize i*2^E.high≤2^bitSites) (paidRows : S.hostSize i*2^E.high≤2^bitPeers)
    (area : Size C' (((1+maxPorts)+E.dim)*S.hostSize i) E.high E.low E.precision w)
    (endWords : wordEnd origin E.high E.low≤C'.input.base) (gap : C'.input.base+C'.input.size≤C'.flags)
    (scaleWords : (powers origin E.dim).Fits w C'.input.base)
    (addresses : (cols origin E.dim).offsets.Fits w C'.input.base)
    (switches : (cols origin E.dim).switches.Fits w C'.input.base)
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base) :
    let digits := (Equiv.cast (congrArg Block (dim.trans reset.keyWidth))).trans sourceDigits
    let name := ((A).numberedHeader digits input.vertex).site
    let ps := fun j : Fin maxPorts=>(⟨peerBase+j.val*pitch,bitPeers⟩:Bank)
    let sites : Bank:=⟨siteBase,bitSites⟩
    let H:=S.hostSize i
    let nG:=((1+maxPorts)+E.dim)*H
    let tables:=controlImage (h:=E.high) (l:=E.low) (w:=w) origin pcap
    let route:=routes C' nG E.high E.low E.precision w
    let move:=gathered C' origin E.solveAt sites ps H E.high E.low w
    let fee:=gatherFee C' origin E.solveAt sites ps H E.high E.low
    let previous:=prepare.seq ((E.header (w:=w)).program.seq (E.cpu w))
    let suffix:=(tables.program.seq route.program).seq move
    ∃(μ : DescentGL.Layout E.dim) (dst : Memory w),HEq μ reset.frame.basis ∧
      (previous.seq suffix).Exec mem dst ((t+(4+10*(E.staticEnd-E.origin)+E.clock))+
        ((8+10*(tables.length+route.length))+fee)) ∧ CheapCode suffix ∧
      (∀channel,DescentGLPacked.Dense (h:=E.high) (l:=E.low)
        (slice (((C'.chosen E.dim).bank (DescentGLNielsen.schedule E.dim).length).base) H (2^E.high) channel)
        (fun v x=>PackedFlow.Channels.values
          (fun (v:Fin H) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
          (fun (j : Fin maxPorts) (v:Fin H) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
          pcap channel v ((rearrange μ).symm x)) dst) ∧
      (∀a : Fin E.dim,dst (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      ∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→dst a=mem a := by
  intro digits name ps sites H nG tables route move fee previous suffix
  obtain ⟨_,μ,dst,equal,run,cheap,words,rowsRead,keepOld,_,_,_⟩:=accepted.signed_remix_named E dim mem prepare t
    maxPorts ports hostCount siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed
    grain old branch live localBits localGain fit stage small score endRoom issue C' origin bitSites bitPeers
    pcap base siteFit pairFit rows paidRows area endWords gap scaleWords addresses switches planes
  exact ⟨μ,dst,equal,run,cheap,words,rowsRead,keepOld⟩

end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
