import OAI.Hierarchy.DescentTerminalCableSourceFrame
import OAI.Hierarchy.DescentNamedOriginalPreflight
import OAI.Hierarchy.DescentObservedBootReel

namespace OAI
/-! # The native suffix following the sole matrix and seventeen-column early relocation -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentMixedRouter Catalyst DescentInitialHost DescentExteriorReplay
open DescentTerminalPreflightSpace DescentTerminalFixedSlices DescentTerminalPrimitiveArena
open DescentTerminalPointerDigits DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing CallPool
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F:Type} [Field F] {cp ar:ℕ} (X:Approximation F cp ar) (G:PoweredGadget F) (S:AtomSchedule)
  {k tail:ℕ} (baseGroups:S.baseGroups=2^tail) (radix:S.radix=2^k)
  (g p q drift:ℕ) (op:RotorSpec) (headerRows paidRows:ℕ)
local notation "spec" => preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
local notation "ports" => Fintype.card (Port ar X.width)
variable (j r t base compact:ℕ) (tag:ℕ→Bool) (rotation:ℕ→ℕ)
  (phase:Phase F) (snapshots:Snapshots k)
local notation "C" => replayCalendar X S k tail j r snapshots
local notation "early_" => DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t ports
local notation "slices_" => phase.stop early_
local notation "rom_" => (C).packetEnd slices_
local notation "shelf" => (spec).scanPages rom_ q
local notation "census_" => (shelf).stop
local notation "matrix" => DescentExteriorMatrixUpdate.Calendar.stop S k tail base+S.length
local notation "bks" => (spec).scalar.blocks
local notation "H" => (spec).scalar.shops
local notation "hw_" => phase.output.receiver
variable (blocks:2^k=phase.output.receiver.blocks) (shops:S.hostSize S.length=phase.output.receiver.hosts) (roleBase:ℕ)
  (peer:Bank) (paid actor:Fin (2^k)→Bank) (signed:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
local notation "ptr" => fun (f:Fin 4) (j:Fin phase.output.argumentSlots) (b:Fin bks) =>
  phase.output.terminalPointers phase.dateBase f j (b.cast blocks)
variable {w:ℕ} (cohortRoom :
  let book := replayCalendar X S k tail j r snapshots
  let endAddress := DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail base j r t (Fintype.card (Port ar X.width))
  let layout := preflightSpec X G S k g p tail (geometryFormat G S k g p tail q drift op headerRows paidRows)
  book.stop (layout.scanPages (book.packetEnd (phase.stop endAddress)) q).stop < 2^w)
local notation "fixed_" => fixedPreflight X G S baseGroups radix g p q drift op headerRows paidRows census_ rom_ w
  peer ((C).homes slices_) paid actor signed matrix roleBase (phase.banks early_) ptr
local notation "fixedImage" => fixedPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows census_ rom_ w
  peer ((C).homes slices_) paid actor signed matrix roleBase (phase.banks early_) ptr
local notation "fixedFee" => fixedPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows census_ rom_
  peer ((C).homes slices_) paid actor signed matrix ptr

def postEarlyPreflight : Procedure w :=
  ((phase.program early_ w).seq ((C).program slices_ census_ cohortRoom)).seq fixed_

def postEarlyPreflightMemory (m:Memory w) : Memory w :=
  fixedImage ((C).memory slices_ census_ cohortRoom (phase.memory early_ m))

def postEarlyPreflightClocks := (phase.cost early_+(C).cost slices_ census_ cohortRoom)+fixedFee

local notation "out_" => postEarlyPreflightMemory X G S baseGroups radix g p q drift op headerRows paidRows j r t
  base phase snapshots blocks roleBase peer paid actor signed cohortRoom
local notation "code_" => postEarlyPreflight X G S baseGroups radix g p q drift op headerRows paidRows j r t
  base phase snapshots blocks roleBase peer paid actor signed cohortRoom
local notation "clock_" => postEarlyPreflightClocks X G S (k:=k) (tail:=tail) g p q drift op headerRows paidRows j r t
  base phase snapshots blocks peer paid actor signed cohortRoom

local notation "s₀" => S.firstWidth G.b p
local notation "colors" => DescentPrimitivePalette.colors G s₀ (S.grainAt G.b p 0) op
local notation "maxArgs" => NativeBranch.privateSlotCapacity G S drift
local notation "roleBits" => fun f:Fin 6 => DescentTerminalCombinedRole.width colors (max 8 (2^S.capGain))
  maxArgs p drift f*(S.epochPower^S.localTokenExponent)*(spec).groups
local notation "replayResult" m => (C).memory slices_ census_ cohortRoom (phase.memory early_ m)
local notation "primitiveResult" m => fixedPreflightPrimitive X G S (k:=k) (tail:=tail) g p q drift op headerRows
  paidRows census_ rom_ w paid actor signed matrix roleBase (phase.banks early_) ptr (replayResult m)

include shops in
theorem post_early_preflight_site_words
    (word:(spec).maskBase census_<2^w) (positive:0<w) (alive:0<H)
  (earlier:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((C).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signed peer (shelf).total (shelf).modulo ((C).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,H≤(paid b).size) (signedRows:∀b j,H≤(signed b j).size) (m:Memory w) :
    ((((code_).Exec m (out_ m) clock_ ∧ CheapCode code_ ∧
      (∀a,a<early_ ∨ (spec).maskBase census_≤a → out_ m a=m a) ∧ (shelf).Reads (out_ m)) ∧
    (∀a<rom_,out_ m a=(C).memory slices_ census_ cohortRoom (phase.memory early_ m) a) ∧
    (∀a<slices_,out_ m a=phase.memory early_ m a) ∧
    (∀f (b:Fin (hw_).blocks) (h:Fin (hw_).hosts),
      out_ m ((phase.banks early_ f).base+(finProdFinEquiv (b,h)).val)=
        ((phase.write f (DescentTerminalSliceShelf.seen phase.chart m b h)).val:Word w)) ∧
    ∀i:Fin (C).packets,((C).homes slices_).read (out_ m) (i.val:Word w)=
      ((C).homes slices_).read ((C).memory slices_ census_ cohortRoom (phase.memory early_ m)) (i.val:Word w)) ∧
    ∀a, census_≤a → a<(spec).cohortEnd census_ →
      out_ m a=(replayResult m) a ∧ (primitiveResult m) a=(replayResult m) a) ∧
    (∀a,a<(spec).weights census_→ out_ m a=(primitiveResult m) a) ∧
    (shelf).Reads ((spec).bookAtPrimitive census_ peer signed
      (decodeBook S G baseGroups radix p q 3 (spec).cap (spec).printBits (by decide)) (primitiveResult m)) := by
  have equal : (spec).cohortEnd census_=(C).stop census_:=rfl
  obtain ⟨low,mid,high,base0,_⟩:=(C).addresses slices_ census_
  have romSpace : rom_≤census_:=Nat.le_add_right ..
  have slicesBefore : slices_≤rom_:=low.trans (mid.trans high)
  have earlyBefore : early_≤ slices_:=by
    unfold DescentTerminalFixedSlices.Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop
      DescentTerminalSliceShelf.fence DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  have reelBefore : base≤early_:=by
    unfold DescentExteriorMatrixUpdate.Calendar.earlyEnd DescentExteriorMatrixUpdate.Calendar.earlyAt
      DescentExteriorMatrixUpdate.Calendar.stop DescentExteriorMatrixUpdate.Calendar.tableAt
    omega
  have matrixBefore : matrix+1≤(spec).cohortEnd census_:=by
    have loc : matrix+1≤early_:=Nat.le_add_right ..
    rw [equal]
    exact loc.trans (earlyBefore.trans (slicesBefore.trans (romSpace.trans base0)))
  have space_:slices_<2^w:=(slicesBefore.trans (romSpace.trans base0)).trans_lt cohortRoom
  have b:=phase.run early_ m earlier one space_
  have c:=(C).exec_memory slices_ census_ cohortRoom romSpace alive rank (phase.memory early_ m)
  let matched:=(C).memory slices_ census_ cohortRoom (phase.memory early_ m)
  have roles (f:Fin 6) : (phase.banks early_ f).base+(phase.banks early_ f).size≤(spec).cohortEnd census_:=by
    rw [equal];exact (phase.banks_before early_ f).trans (slicesBefore.trans (romSpace.trans base0))
  have tails (f:Fin 4) (j:Fin phase.output.argumentSlots) (b:Fin bks) :=
    phase.output.terminal_field_room phase.dateBase (earlier.trans_lt (earlyBefore.trans_lt space_))
      (f.castLE (by decide : 4≤7)) j (b.cast blocks)
  have afterDate : phase.output.finalEnd phase.dateBase≤(spec).cohortEnd census_:=by
    have o:=phase.output.terminal_order phase.dateBase
    rw [equal]
    exact o.1.trans (o.2.1.trans (o.2.2.trans (earlier.trans (earlyBefore.trans (slicesBefore.trans (romSpace.trans base0))))))
  have ptrEnd : ∀f j b,(ptr f j b).base+(ptr f j b).size≤(spec).cohortEnd census_:=
    fun f j b=>(tails f j b).1.2.2.trans afterDate
  have ptrRows : ∀f j b,H≤(ptr f j b).size:=by
    intro f j b
    rw [show H = (hw_).hosts from shops]
    simpa only [one,Nat.mul_one,DescentDatedAddressBook.ResetOutput.terminalPointers] using (tails f j b).2
  have run:=fixed_preflight_run X G S baseGroups radix g p q drift op headerRows paidRows census_ rom_ w peer
    ((C).homes slices_) paid actor signed matrix roleBase (phase.banks early_) ptr matched le_rfl before word positive
    matrixBefore roles roleEnd ptrEnd ptrRows paidRowsFit signedRows
  have frames:=fixed_preflight_frames_and_census X G S baseGroups radix g p q drift op headerRows paidRows census_ rom_ w peer
    ((C).homes slices_) paid actor signed matrix roleBase (phase.banks early_) ptr matched le_rfl before word positive
    matrixBefore roles roleEnd ptrEnd ptrRows paidRowsFit signedRows
  refine ⟨⟨?_,frames.2⟩,frames.1.2.1,frames.1.2.2.2⟩
  have frame:=frames.1
  have stopFit : (C).stop census_≤(spec).maskBase census_:=by
    rw [←equal]
    obtain ⟨l₁,l₂,l₃,l₄,l₅,l₆,l₇,l₈,l₉⟩:=(spec).layers census_
    exact l₁.trans (l₂.trans (l₃.trans (l₄.trans (l₅.trans (l₆.trans (l₇.trans (l₈.trans l₉)))))))
  have savedReplay (i:ℕ) (lt:i<rom_) : out_ m i=matched i:=frame.1 i (.inl lt)
  have savedSlices (i:ℕ) (lt:i<slices_) : out_ m i=phase.memory early_ m i:=
    (savedReplay i (lt.trans_le slicesBefore)).trans (c.2.2 i (.inl lt))
  have ran : (code_).Exec m (out_ m) clock_ := by
    unfold postEarlyPreflight postEarlyPreflightClocks postEarlyPreflightMemory
    exact Procedure.Exec.then (Procedure.Exec.then (@b.1) (@c.1)) (@run.1)
  have cheap : CheapCode code_ := by
    unfold postEarlyPreflight
    exact @cheap_seq _ _ _ (@cheap_seq _ _ _ (@b.2.1) (@c.2.1)) (@run.2.1)
  refine ⟨⟨@ran,@cheap,?_,@run.2.2⟩,savedReplay,savedSlices,?_,?_⟩
  · intro i outside
    have slicesHigh := slicesBefore.trans (romSpace.trans (base0.trans stopFit))
    have u := frame.1 i (outside.imp (fun h => h.trans_le (earlyBefore.trans slicesBefore)) id)
    have v := c.2.2 i (outside.imp (fun h => h.trans_le earlyBefore) (fun h => stopFit.trans h))
    have x := b.2.2.1 i (outside.imp id (fun h => slicesHigh.trans h))
    exact (u.trans v).trans x
  · intro f block home
    have length_ : (hw_).blocks*(hw_).hosts≤(phase.banks early_ f).size:=Nat.le_pow_clog (by decide) _
    have high_:=phase.banks_before early_ f
    have coord:=(finProdFinEquiv (block,home)).isLt
    exact (savedSlices _ ((Nat.add_lt_add_left (coord.trans_le length_) _).trans_le high_)).trans
      (b.2.2.2 f block home)
  · intro i
    have high_ : ((C).homes slices_).base+((C).homes slices_).size=rom_:=rfl
    have bound := Nat.mod_lt (i.val:Word w).val (Nat.two_pow_pos ((C).homes slices_).bits)
    exact savedReplay _ ((Nat.add_lt_add_left bound _).trans_le high_.le)

include shops in
theorem post_early_preflight_run_and_census
    (word:(spec).maskBase census_<2^w) (positive:0<w) (alive:0<H)
  (earlier:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((C).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signed peer (shelf).total (shelf).modulo ((C).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,H≤(paid b).size) (signedRows:∀b j,H≤(signed b j).size) (m:Memory w) :
    (((code_).Exec m (out_ m) clock_ ∧ CheapCode code_ ∧
      (∀a,a<early_ ∨ (spec).maskBase census_≤a → out_ m a=m a) ∧ (shelf).Reads (out_ m)) ∧
    (∀a<rom_,out_ m a=(C).memory slices_ census_ cohortRoom (phase.memory early_ m) a) ∧
    (∀a<slices_,out_ m a=phase.memory early_ m a) ∧
    (∀f (b:Fin (hw_).blocks) (h:Fin (hw_).hosts),
      out_ m ((phase.banks early_ f).base+(finProdFinEquiv (b,h)).val)=
        ((phase.write f (DescentTerminalSliceShelf.seen phase.chart m b h)).val:Word w)) ∧
    ∀i:Fin (C).packets,((C).homes slices_).read (out_ m) (i.val:Word w)=
      ((C).homes slices_).read ((C).memory slices_ census_ cohortRoom (phase.memory early_ m)) (i.val:Word w)) ∧
    ∀a, census_≤a → a<(spec).cohortEnd census_ →
      out_ m a=(replayResult m) a ∧ (primitiveResult m) a=(replayResult m) a :=
  (post_early_preflight_site_words X G S baseGroups radix g p q drift op headerRows paidRows
    j r t base phase snapshots blocks shops roleBase peer paid actor signed cohortRoom word positive alive
    earlier one rank roleEnd before paidRowsFit signedRows m).1

include shops in
/-- All phases run on the same machine, including on malformed histories. Source banks are
ordinary dated memory. Both the six role tables and the public-home bank have derived addresses. -/
theorem post_early_preflight_run
    (word:(spec).maskBase census_<2^w) (positive:0<w) (alive:0<H)
  (earlier:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((C).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signed peer (shelf).total (shelf).modulo ((C).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,H≤(paid b).size) (signedRows:∀b j,H≤(signed b j).size) (m:Memory w) :
    ((code_).Exec m (out_ m) clock_ ∧ CheapCode code_ ∧
      (∀a,a<early_ ∨ (spec).maskBase census_≤a → out_ m a=m a) ∧ (shelf).Reads (out_ m)) ∧
    (∀a<rom_,out_ m a=(C).memory slices_ census_ cohortRoom (phase.memory early_ m) a) ∧
    (∀a<slices_,out_ m a=phase.memory early_ m a) ∧
    (∀f (b:Fin (hw_).blocks) (h:Fin (hw_).hosts),
      out_ m ((phase.banks early_ f).base+(finProdFinEquiv (b,h)).val)=
        ((phase.write f (DescentTerminalSliceShelf.seen phase.chart m b h)).val:Word w)) ∧
    ∀i:Fin (C).packets,((C).homes slices_).read (out_ m) (i.val:Word w)=
      ((C).homes slices_).read ((C).memory slices_ census_ cohortRoom (phase.memory early_ m)) (i.val:Word w) :=
  (post_early_preflight_run_and_census X G S baseGroups radix g p q drift op headerRows paidRows
    j r t base phase snapshots blocks shops roleBase peer paid actor signed cohortRoom word positive alive
    earlier one rank roleEnd before paidRowsFit signedRows m).1

open Chronology
variable (boot:Procedure w) (bootTicks:ℕ) (date:ℕ→DateCode w)
  (countStart:ℕ) (source:ℕ→ℕ) (countRows:ℕ)

local notation "dated" => DateCode.afterBoot boot date S.length
local notation "countCode" => DescentLowCountBook.program w countStart source countRows
local notation "reelCode" => DescentExteriorMatrixUpdate.Calendar.earlyProgram S k tail base tag rotation j r t ports compact w
local notation "earlyCost" => DescentExteriorMatrixUpdate.Calendar.earlyClock S k tail j r t ports

/-- The complete middle after the seed verdict with a single early relocation. -/
def fundedMiddle : Procedure w := ((dated).seq ((countCode).seq reelCode)).seq code_

def fundedMiddleClocks :=
  (DateCode.afterTicks bootTicks date S.length+((4+11*countRows)+earlyCost))+clock_

local notation "datedMemory" => DateCode.history date
local notation "counted" => DescentLowCountBook.output countStart source
local notation "relocated" => DescentExteriorMatrixUpdate.Calendar.earlyImage S k tail base tag rotation j r t ports compact

include shops in
/-- Captured selectors retain their values on the reached date. The original compact
input is preserved outside the count pages; all six phase digits and the padded packet
home output are computed on the same execution. -/
theorem funded_middle_run
    (word:(spec).maskBase census_<2^w) (positive:0<w) (alive:0<H)
  (prev:∀i<S.length,rotation i<base) (seed:compact+32*DescentExteriorShelf.span j r t ports≤base)
  (earlier:phase.output.metadataEnd phase.dateBase≤early_) (one:chunks (hw_).groups (hw_).lanes=1)
  (rank:∀t<S.length,∀b,snapshots.compact t=some b→b.Fits w ((C).scratch slices_))
  (roleEnd:roleBase+DescentTerminalRoleTables.count roleBits≤(spec).cohortEnd census_)
  (before:(spec).Before census_ paid actor signed peer (shelf).total (shelf).modulo ((C).homes slices_) (shelf).boundaries)
  (paidRowsFit:∀b,H≤(paid b).size) (signedRows:∀b j,H≤(signed b j).size)
    (boot:Procedure w) (bootTicks:ℕ) (date:ℕ→DateCode w)
    (countStart:ℕ) (source:ℕ→ℕ) (countRows:ℕ) (raw initial:Memory w) (booted:boot.Exec raw initial bootTicks)
    (initialCheap:CheapCode boot) (total:∀i<S.length,∀s,∃out,(date i).Runs s out)
    (dateCheap:∀i<S.length,(date i).cheap)
    (countRoom:countStart<2^w) (sourceApart:∀i<countRows,countStart+i≤ source i)
    (sourceRoom:∀i<countRows,source i+1<2^w) :
    let m:=DateCode.history date initial S.length
    let counts:=DescentLowCountBook.output countStart source m countRows
    let reel:=relocated counts
    let out:=out_ reel
    (((DateCode.afterBoot boot date S.length).seq ((DescentLowCountBook.program w countStart source countRows).seq reelCode)).seq code_).Exec raw out
        ((DateCode.afterTicks bootTicks date S.length+((4+11*countRows)+earlyCost))+clock_) ∧
      CheapCode (((DateCode.afterBoot boot date S.length).seq ((DescentLowCountBook.program w countStart source countRows).seq reelCode)).seq code_) ∧
      (∀u,u<early_→ out u=reel u) ∧
      (∀u,u<base→ out u=counts u) ∧
      (∀u,u<base→(u<countStart ∨ countStart+countRows≤u)→ out u=m u) ∧
      (shelf).Reads out := by
  intro m counts reel out
  have start : (DateCode.afterBoot boot date S.length).Exec raw m (DateCode.afterTicks bootTicks date S.length) :=
    DateCode.boot_history boot bootTicks date raw initial (@booted) S.length total
  have startCheap : CheapCode (DateCode.afterBoot boot date S.length) :=
    DateCode.after_cheap boot date S.length (@initialCheap) dateCheap
  have capture : (DescentLowCountBook.program w countStart source countRows).Exec m counts (4+11*countRows) :=
    DescentLowCountBook.run countStart source m countRows countRoom sourceApart sourceRoom
  have captureCheap : CheapCode (DescentLowCountBook.program w countStart source countRows) :=
    @(DescentLowCountBook.hardware w countStart source countRows).1
  have equal : (spec).cohortEnd census_=(C).stop census_:=rfl
  obtain ⟨low,mid,high,base0,_⟩:=(C).addresses slices_ census_
  have romSpace : rom_≤census_:=Nat.le_add_right ..
  have slicesBefore : slices_≤rom_:=low.trans (mid.trans high)
  have earlyBefore : early_≤ slices_:=by
    unfold DescentTerminalFixedSlices.Phase.stop DescentTerminalCompiledPrefix.AddressPlan.sliceStop
      DescentTerminalSliceShelf.fence DescentTerminalSliceShelf.stage DescentTerminalPointerDigits.Gather.rom DescentOperandStateBanks.guard
    simp only [Nat.add_assoc, Nat.le_add_right]
  have reelBefore : base≤early_:=by
    unfold DescentExteriorMatrixUpdate.Calendar.earlyEnd DescentExteriorMatrixUpdate.Calendar.earlyAt
      DescentExteriorMatrixUpdate.Calendar.stop DescentExteriorMatrixUpdate.Calendar.tableAt
    omega
  have matrixBefore : matrix+1≤(spec).cohortEnd census_:=by
    have loc : matrix+1≤early_:=Nat.le_add_right ..
    rw [equal]
    exact loc.trans (earlyBefore.trans (slicesBefore.trans (romSpace.trans base0)))
  have space_:slices_<2^w:=(slicesBefore.trans (romSpace.trans base0)).trans_lt cohortRoom
  have moved:=DescentExteriorMatrixUpdate.Calendar.early_run S k tail base tag rotation j r t ports compact
    counts positive prev seed (earlyBefore.trans_lt space_)
  have final:=post_early_preflight_run X G S baseGroups radix g p q drift op headerRows paidRows
    j r t base phase snapshots blocks shops roleBase peer paid actor signed cohortRoom word positive alive earlier
    one rank roleEnd before paidRowsFit signedRows reel
  have copied (u:ℕ) (lo:u<base):out u=counts u :=
    (final.1.2.2.1 u (.inl (lo.trans_le reelBefore))).trans (moved.2.2 u (.inl lo))
  exact ⟨Procedure.Exec.then (Procedure.Exec.then (@start) (Procedure.Exec.then (@capture) (@moved.1))) (@final.1.1),
    @cheap_seq _ _ _ (@cheap_seq _ _ _ (@startCheap) (@cheap_seq _ _ _ (@captureCheap) (@moved.2.1))) (@final.1.2.1),
    fun u hu=>final.1.2.2.1 u (.inl hu),copied,
    fun u hu away=>(copied u hu).trans (DescentLowCountBook.frame countStart source m countRows u away),
    final.1.2.2.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
