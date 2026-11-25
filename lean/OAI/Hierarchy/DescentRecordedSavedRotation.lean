import OAI.Hierarchy.DescentRecordedSignedRemix
import OAI.Hierarchy.DescentExteriorRotationWord

namespace OAI
/-! # The physical reset word is saved from the same selected and remixed execution -/
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
theorem saved_rotation {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
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
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base)
    (baseWord out : ℕ) (off decode : Bank)
    (ofit : off.Fits w out) (dfit : decode.Fits w out)
    (os : (2^E.dim)^E.dim ≤ off.size) (ds : (2^E.dim)^E.dim ≤ decode.size)
    (ob : off.base=baseWord) (db : decode.base=baseWord+(2^E.dim)^E.dim)
    (ptrLow : ∀a : Fin E.dim,PhysicalTrajectory.pointer E.dim E.solveAt a.val < out)
    (fits : out+1 < 2^w) (rom : (DescentExteriorRotationWord.resetSheet E.dim w baseWord).Resident mem)
    (lowROM : baseWord+(2^E.dim)^E.dim+(2^E.dim)^E.dim ≤ min keep E.start)
    (sepROM : baseWord+(2^E.dim)^E.dim+(2^E.dim)^E.dim ≤ E.origin ∨ E.staticEnd ≤ baseWord) :
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
    let ptr:=fun a : Fin E.dim=>PhysicalTrajectory.pointer E.dim E.solveAt a.val
    let op:=DescentExteriorRotationWord.reset off decode ptr
    ∃(μ : DescentGL.Layout E.dim) (mid dst : Memory w),HEq μ reset.frame.basis ∧
      ((previous.seq suffix).seq (scan w out 1 op)).Exec mem dst
        (((t+(4+10*(E.staticEnd-E.origin)+E.clock))+((8+10*(tables.length+route.length))+fee))+(20+24*E.dim)) ∧
      CheapCode (suffix.seq (scan w out 1 op)) ∧ dst out=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀a,out≠a→dst a=mid a) ∧
      (∀channel,DescentGLPacked.Dense (h:=E.high) (l:=E.low)
        (slice (((C'.chosen E.dim).bank (DescentGLNielsen.schedule E.dim).length).base) H (2^E.high) channel)
        (fun v x=>PackedFlow.Channels.values
          (fun (v:Fin H) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
          (fun (j : Fin maxPorts) (v:Fin H) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
          pcap channel v ((rearrange μ).symm x)) mid) ∧
      ∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→ out≠a→dst a=mem a := by
  intro digits name ps sites H nG tables route move fee previous suffix ptr op
  obtain ⟨μ,mid,eq,ran,cheap,denseRead,chosen,frame⟩:=accepted.signed_remix E dim mem prepare t maxPorts ports hostCount
    siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed grain old branch live localBits localGain
    fit stage small score endRoom issue C' origin bitSites bitPeers pcap base siteFit pairFit rows paidRows area endWords
    gap scaleWords addresses switches planes
  have held : (DescentExteriorRotationWord.resetSheet E.dim w baseWord).Resident mid := by
    intro a lo hi
    change baseWord ≤ a at lo
    change a < baseWord+(2^E.dim)^E.dim+(2^E.dim)^E.dim at hi
    exact (frame a (by omega) (by omega)).trans (rom a lo hi)
  have save:=DescentExteriorRotationWord.reset_run out off decode ptr mid ofit dfit ptrLow fits
  have read:=DescentExteriorRotationWord.reset_read baseWord out off decode ptr mid μ ofit dfit os ds ob db held chosen
  have outer:=fun a (away : out≠a)=>DescentExteriorRotationWord.record_frame out a mid op away
  exact ⟨μ,mid,ProtocolRAM.image out 1 op mid,eq,ran.then save.1,cheap_seq cheap save.2,read,outer,denseRead,
    fun a h ne away=>(outer a away).trans (frame a h ne)⟩

include accepted in
theorem saved_rotation_fresh {w : ℕ} (dim : E.dim=reset.reset.k) (mem : Memory w) (prepare : Procedure w) (t : ℕ)
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
    (planes : ∀j : Fin E.dim,(Original.bank (plane origin E.dim) E.high j).Fits w C'.input.base)
    (fresh : ℕ) (ptrLow : ∀a : Fin E.dim,PhysicalTrajectory.pointer E.dim E.solveAt a.val < fresh)
    (space : fresh+(2^E.dim)^E.dim+(2^E.dim)^E.dim+1 < 2^w) :
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
    let ptr:=fun a : Fin E.dim=>PhysicalTrajectory.pointer E.dim E.solveAt a.val
    let n:=(2^E.dim)^E.dim
    let I:=DescentExteriorRotationWord.resetSheet E.dim w fresh
    let off : Bank:=⟨fresh,E.dim*E.dim⟩
    let table : Bank:=⟨fresh+n,E.dim*E.dim⟩
    let out:=fresh+n+n
    let op:=DescentExteriorRotationWord.reset off table ptr
    let save:=I.program.seq (scan w out 1 op)
    ∃(μ : DescentGL.Layout E.dim) (mid dst : Memory w),HEq μ reset.frame.basis ∧
      ((previous.seq suffix).seq save).Exec mem dst
        (((t+(4+10*(E.staticEnd-E.origin)+E.clock))+((8+10*(tables.length+route.length))+fee))+
          ((4+10*(n+n))+(20+24*E.dim))) ∧ CheapCode (suffix.seq save) ∧
      dst out=((DescentExterior.matrixCode μ).val:Word w) ∧
      (∀a,a < fresh ∨ out+1 ≤ a→dst a=mid a) ∧
      (∀channel,DescentGLPacked.Dense (h:=E.high) (l:=E.low)
        (slice (((C'.chosen E.dim).bank (DescentGLNielsen.schedule E.dim).length).base) H (2^E.high) channel)
        (fun v x=>PackedFlow.Channels.values
          (fun (v:Fin H) a=>(PackedFlow.Padded.load A name digits v a:Cell E.precision))
          (fun (j : Fin maxPorts) (v:Fin H) a=>(PackedFlow.Padded.flow A name digits j v a:Cell E.precision))
          pcap channel v ((rearrange μ).symm x)) mid) ∧
      ∀a< min keep E.start,(a<E.origin ∨ E.staticEnd≤a)→a < fresh→dst a=mem a := by
  intro digits name ps sites H nG tables route move fee previous suffix ptr n I off table out op save
  obtain ⟨μ,mid,eq,ran,cheap,denseRead,chosen,frame⟩:=accepted.signed_remix E dim mem prepare t maxPorts ports hostCount
    siteBase peerBase pitch keep width siteEnd peerEnd siteSave peerSave primed grain old branch live localBits localGain
    fit stage small score endRoom issue C' origin bitSites bitPeers pcap base siteFit pairFit rows paidRows area endWords
    gap scaleWords addresses switches planes
  obtain ⟨after,price,read,outer⟩:=DescentExteriorRotationWord.reset_fresh E.dim fresh ptr mid ptrLow space
  exact ⟨μ,mid,ProtocolRAM.image out 1 op (I.output mid),eq,ran.then after,cheap_seq cheap price,read μ chosen,
    outer,denseRead,fun a h ne lt=>(outer a (.inl lt)).trans (frame a h ne)⟩


end ClosedReset.Recorded
end
end Hierarchy.DescentSixParty

end OAI
