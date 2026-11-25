import OAI.Hierarchy.DescentTerminalWingPitch
import OAI.Hierarchy.DescentTerminalSliceDated
import OAI.Hierarchy.DescentTerminalSliceSpace
import OAI.Hierarchy.DescentDatedSliceShelfRate
import OAI.Hierarchy.DescentNamedSliceOpenInvoice

namespace OAI
/-! # One terminal role normalization phase on the paid reset calendar -/
namespace Hierarchy.DescentTerminalFixedSlices
open DescentDatedAddressBook DescentCompiler DescentSixParty DescentTerminalSliceRuns
open DescentSIMDLookup DescentTerminalPointerDigits DescentOperandStateBanks ProtocolRAM
open DescentPrimitivePalette DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false

/-- The address before the primitive table is the *rebased* date location. The later start of
the six output tables is chosen by the public address plan. -/
structure Phase (F:Type) [Field F] where
  gadget : PoweredGadget F
  op : RotorSpec
  stageBits : ℕ
  grain : ℕ
  piece : ℕ
  drift : ℕ
  birthArity : ℕ
  groupCapacity : ℕ
  output : ResetOutput
  dateBase : ℕ
  tokenBlocks : output.receiver.blocks=output.primitive.chart.blocks
  countBlocks : output.receiver.blocks=output.metadata.chart.blocks
  tokenRows : output.primitive.chart.rows=
    output.receiver.hosts*chunks output.receiver.groups output.receiver.lanes
  countRows : output.metadata.chart.rows=
    output.receiver.hosts*chunks output.receiver.groups output.receiver.lanes

namespace Phase
variable {F:Type} [Field F] (P:Phase F)
local notation "v" => P.output
local notation "B" => (v).receiver.blocks
local notation "H" => (v).receiver.hosts
local notation "N" => (v).nodes
local notation "Gs" => (v).receiver.groups
local notation "L" => Columns (v).argumentSlots
def digits := DescentTerminalSliceShelf.physicalWidth Gs N (v).primitive.chart.bits (v).nodeBits

def chart := datedChart (v) P.dateBase P.tokenBlocks P.countBlocks

def write := writePanel (s:=P.stageBits) (Z:=P.grain) (M:=(v).argumentSlots) («N»:=N) (groups:=Gs) (d:=P.digits)
  P.gadget P.op P.birthArity P.groupCapacity P.piece P.drift (datedWidths (v))

def program (start w:ℕ) := DescentTerminalSliceShelf.program start P.chart P.write H w

def memory (start:ℕ) {w:ℕ} (m:Memory w) := DescentTerminalSliceShelf.memory start P.chart P.write H m

def cost (start:ℕ) := DescentTerminalSliceShelf.cost start P.chart H P.digits

def banks (start:ℕ) (f:Fin 6) := DescentTerminalSliceShelf.field start L P.digits (B*H) f.val

def stop (start:ℕ) := DescentTerminalCompiledPrefix.AddressPlan.sliceStop start (v).argumentSlots P.digits B H

theorem banks_before (start:ℕ) (f:Fin 6) :
    (P.banks start f).base+(P.banks start f).size≤P.stop start :=
  DescentTerminalSliceShelf.source_before start L P.digits (B*H) f

theorem stop_bound (start h factor:ℕ)
    (static : DescentTerminalPointerFrame.size L P.digits≤2*2^(h/2))
    (localWork : (L+1)*(B+1)≤factor) :
    P.stop start≤ start+128*(2^(h/2)+H*factor) :=
  DescentTerminalSliceShelf.fence_le start L P.digits h H B factor static localWork

private theorem inside (start:ℕ) :
    start≤P.stop start ∧ 2^P.digits≤P.stop start := by
  let rows := B * H
  let stride := DescentTerminalPointerFrame.size L P.digits + DescentTerminalSliceShelf.pad rows
  have end_ : P.stop start = Gather.rom start L rows + 6*stride := rfl
  have startRom : start ≤ Gather.rom start L rows :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have one : 0<L := by dsimp [Columns]; omega
  have table : 2^P.digits ≤ DescentTerminalPointerFrame.size L P.digits :=
    (Nat.le_mul_of_pos_left _ one).trans (Nat.le_add_right _ _)
  have tail : stride ≤ 6*stride := Nat.le_mul_of_pos_left _ (by decide)
  rw [end_]
  exact ⟨startRom.trans (Nat.le_add_right _ _),
    ((table.trans (Nat.le_add_right _ _)).trans tail).trans (Nat.le_add_left _ _)⟩

theorem fits {w:ℕ} (start:ℕ) (done_:(v).metadataEnd P.dateBase≤ start)
    (one:chunks Gs (v).receiver.lanes=1) (space:P.stop start<2^w) (j:Fin L) (b:Fin B) :
    (P.chart j b).Fits start H w :=
  dated_room (v) P.dateBase P.tokenBlocks P.countBlocks start done_ ((P.inside start).1.trans_lt space) one
    (by rw [P.tokenRows,one,Nat.mul_one]) (by rw [P.countRows,one,Nat.mul_one]) j b

/-- The complete pass is the same on every incoming bit assignment. The six returned words
are evaluated on physical observations from that incoming memory, in block-major order. -/
theorem run {w:ℕ} (start:ℕ) (m:Memory w) (done_:(v).metadataEnd P.dateBase≤ start)
    (one:chunks Gs (v).receiver.lanes=1) (space:P.stop start<2^w) :
    (P.program start w).Exec m (P.memory start m) (P.cost start) ∧ CheapCode (P.program start w) ∧
    (∀i,i<start ∨ P.stop start≤ i→P.memory start m i=m i) ∧
    ∀(f:Fin 6)(b:Fin B)(h:Fin H),P.memory start m ((P.banks start f).base+(finProdFinEquiv (b,h)).val)=
      ((P.write f (DescentTerminalSliceShelf.seen P.chart m b h)).val:Word w) :=
  DescentTerminalSliceShelf.native start P.chart P.write m (P.fits start done_ one space)
    ((P.inside start).2.trans_lt space) space

theorem read {w:ℕ} (start:ℕ) (m:Memory w) (done_:(v).metadataEnd P.dateBase≤ start)
    (one:chunks Gs (v).receiver.lanes=1) (space:P.stop start<2^w)
    (f:Fin 6) (b:Fin B) (h:Fin H) :
    P.memory start m ((P.banks start f).base+(b.val*H+h.val))=
      ((P.write f (DescentTerminalSliceShelf.seen P.chart m b h)).val:Word w) := by
  have order:(finProdFinEquiv (b,h)).val=b.val*H+h.val:=by change h.val+H*b.val=_;ring
  simpa only [order] using (P.run start m done_ one space).2.2.2 f b h

theorem invoice {w h factor:ℕ} (start:ℕ) (done_:(v).metadataEnd P.dateBase≤ start)
    (one:chunks Gs (v).receiver.lanes=1) (space:P.stop start<2^w) (positive:0<H)
    (static:DescentTerminalPointerFrame.size L P.digits≤2*2^(h/2)) (work:(L+1)*(B+1)≤factor) :
    DescentStaticWordColumn.names (P.program start w)+P.cost start≤16384*(2^(h/2)+H*factor) :=
  DescentTerminalSliceShelf.invoice start P.chart P.write (fun _=>0:Memory w)
    (P.fits start done_ one space) space positive static work

section Dated
variable {n d:ℕ} (G:PoweredGadget F) (S:AtomSchedule) (board:NonlinearExpanders.Graph n d)
    (k tail age p f g drift degree payload:ℕ) (ordinary:ℕ→Dated.Ordinary) (op:RotorSpec)
    (operandLanes primitiveLanes:ℕ) (previous:StageVenueTail.Date) (addr:ℕ→ℕ→Bank)
    (roster:Bank) (floor:ℕ)
local notation "dated" => PhysicalReset.scheduled G S board k tail age p f g drift degree payload ordinary op
  (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes previous addr roster floor

/-- All original and new role addresses depend only on the public last date of the chart. -/
def scheduled : Phase F where
  gadget:=G
  op:=op
  stageBits:=S.firstWidth G.b p
  grain:=S.grainAt G.b p 0
  piece:=p
  drift:=drift
  birthArity:=max 8 (2^S.capGain)
  groupCapacity:=NativeBranch.privateSlotCapacity G S drift
  output:=(dated).successor
  dateBase:=(dated).rebased ((dated).stageStart floor)
  tokenBlocks:=rfl
  countBlocks:=rfl
  tokenRows:=rfl
  countRows:=rfl

local notation "real" => scheduled G S board k tail age p f g drift degree payload ordinary op
  operandLanes primitiveLanes previous addr roster floor

theorem scheduled_layout (last:age+1=S.length) :
    (real).output.receiver.blocks=2^k ∧ (real).output.receiver.hosts=S.hostSize S.length ∧
    (real).output.receiver.groups=S.baseGroups ∧ (real).output.nodes=S.retainedNodes ∧
    (real).output.argumentSlots=S.retainedArgumentsAt G drift ∧
    (real).output.metadataEnd (real).dateBase=(dated).fullEnd floor := by
  refine ⟨rfl,congrArg S.hostSize last,?_,rfl,rfl,rfl⟩
  change S.groupCount (age+1)=S.baseGroups
  simp only [last,AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one]

/-- Full dyadic pitch at the final reset gives one original group word at every host. -/
theorem scheduled_one (last:age+1=S.length) (fixed:S.baseGroups=2^tail)
    (signed:(dated).successor.venue.next.signedLanes=S.groupCount S.length) :
    chunks (real).output.receiver.groups (real).output.receiver.lanes=1 := by
  have groups:S.groupCount S.length=S.baseGroups:=by simp [AtomSchedule.groupCount]
  change chunks (S.groupCount (age+1)) (dated).successor.venue.next.signedLanes=1
  rw [last,signed,groups,fixed]
  exact DescentSIMDLookup.covered_chunks (Nat.two_pow_pos _) le_rfl

end Dated
/-- Numeric conditions computed from the actual public program, independently of its input. -/
structure Paid (h exponentFactor:ℕ) : Prop where
  one : chunks Gs (v).receiver.lanes=1
  static : DescentTerminalPointerFrame.size L P.digits≤2*2^(h/2)
  work : (L+1)*(B+1)≤exponentFactor

section OpenHost
open DescentCompiler.TerminalScale DescentStaticWordColumn
variable (G:PoweredGadget F) (t J f g reset sites τ drift:ℕ)
local notation "S_" => stageNumbers G t J f g reset sites (tail τ J)
local notation "k_" => groupBits t J (S_).hostGain (S_).capGain (cutRate t f g)
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)
local notation "κ" => groupRate G t f g reset
local notation "scan" => α+κ+4

/-- Inserting the fixed phase between two attained original procedures uses the same
open-host invoice as the block gather and all six scalar sheets together. -/
theorem open_price (s h w E factor start:ℕ) (covered:P.Paid h (scale J scan))
    (ended:(v).metadataEnd P.dateBase≤ start) (space:P.stop start<2^w)
    (hosts:H=(S_).hostSize (S_).length) (positive:0<H)
    (slots:(v).argumentSlots≤(S_).retainedArgumentsAt G drift) (blocks:B≤2^k_)
    (late:drift+1≤ scale J 1) (reserve:localSocketRate G t g+scan≤τ)
    (large:10≤h) (support:2^h≤2*(sites*(S_).copies)) (power:2^J≤ s)
    (arch:w+1≤factor*h) (packed:h≤32*(2^Nat.clog 2 (NativeBranch.localLimit G S_)*s))
    (front back:Procedure w) (rest prior:ℕ)
    (before:(rest+7*names (front.seq back))*(w+1)*2^J≤prior*(((S_).copies*s)*(sites+2^J*E))) :
    (rest+P.cost start+7*names ((front.seq (P.program start w)).seq back))*(w+1)*2^J≤
      (prior+7*16384*(2*factor))*(((S_).copies*s)*(sites+2^J*E)) := by
  have geometry:=P.fits start ended covered.one space
  have footprint:DescentTerminalSliceShelf.fence start L P.digits (B*((S_).hostSize (S_).length))<2^w := by
    rw [←hosts]
    exact space
  have raw:=native_slices_open_price G t J f g reset sites τ drift s h w E factor start
    P.chart P.write (fun _=>0:Memory w) late reserve large support power arch packed
    (hosts ▸ positive) (Nat.add_le_add_left (Nat.mul_le_mul_left 3 slots) 2) blocks
    covered.static (by rw [←hosts];exact geometry) ((P.inside start).2.trans_lt space)
    footprint front back rest prior before
  simpa only [program,cost,←hosts] using raw

end OpenHost

section Calibrated
open Filter DescentCompiler.TerminalScale
variable {n degree:ℕ} (G:PoweredGadget F) (board:NonlinearExpanders.Graph n degree)
    (op:RotorSpec) (t f g reset τ D drift cutoff:ℕ)
local notation "σ" => ResetOutput.receiverRate G board op t f g reset D
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)
local notation "κ" => groupRate G t f g reset
local notation "J_" h:arg => Nat.log 2 h/(2*cutoff)
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "τ_" h:arg => DescentCompiler.TerminalScale.tail τ (J_ h)
local notation "S_" h:arg sites:arg => stageNumbers G t (J_ h) f g reset sites (τ_ h)

/-- On the true final reset, both the cost of the six lookup tables and the row scan are
bounded by their original public calibration. No candidate-dependent data enters this bound. -/
theorem calibrated (branch:G.b≤2^(capRate G t g)) (positive:0<cutoff)
    (pitch:2*(τ+κ+σ)≤cutoff) (tables:2*(τ+(σ+α))≤cutoff) :
    ∀ᶠh:ℕ in atTop,∀sites age p priorDegree (ordinary:ℕ→Dated.Ordinary)
      (old:StageVenueTail.Date) (operandLanes primitiveLanes floor:ℕ) (addr:ℕ→ℕ→Bank) (roster:Bank),
      let S:=S_ h sites
      let job:=scheduled G S board (k_ h) (τ_ h) age p f g drift priorDegree h ordinary op
        operandLanes primitiveLanes old addr roster floor
      age+1=S.length→p≤h→priorDegree≤D→ old.degree=D→
      old.cap=((capCalendar G.b t g (J_ h)).take age).prod*256→ old.paidBits=S.censusBits p→
      job.Paid h (scale (J_ h) (α+κ+4)) := by
  filter_upwards [PhysicalReset.calibrated_final (t:=t) (reset:=reset) (τ:=τ) («B»:=cutoff)
    (f:=f) (g:=g) G board op D drift branch positive pitch,
    DescentTerminalSliceShelf.named_digits G board op t f g reset τ D drift cutoff branch positive tables,
    eventually_late (drift+1) cutoff positive] with h packed paid mature
  intro sites age p priorDegree ordinary old operandLanes primitiveLanes floor addr roster
  dsimp only
  intro last grain degree_ oldDegree cap_ census
  let S:=S_ h sites
  let job:=scheduled G S board (k_ h) (τ_ h) age p f g drift priorDegree h ordinary op
    operandLanes primitiveLanes old addr roster floor
  have final:=packed sites age p priorDegree ordinary old operandLanes primitiveLanes floor addr roster
    last grain degree_ oldDegree cap_ census
  have physical:=paid sites age p priorDegree ordinary old operandLanes primitiveLanes floor addr roster
    grain degree_ oldDegree cap_ census
  have base:S.baseGroups=2^(τ_ h):=rfl
  have single:=scheduled_one G S board (k_ h) (τ_ h) age p f g drift priorDegree h ordinary op
    operandLanes primitiveLanes old addr roster floor last base final.1
  refine ⟨single,?_,?_⟩
  · change DescentTerminalPointerFrame.size (Columns job.output.argumentSlots)
      (DescentTerminalSliceShelf.physicalWidth (S.groupCount (age+1)) job.output.nodes
        job.output.primitive.chart.bits job.output.nodeBits)≤_
    rw [last]
    exact physical.2
  · apply slice_pass_multiplier G t (J_ h) f g reset sites τ drift
    change drift+1≤2^(1*((J_ h)+1))
    rw [Nat.one_mul]
    exact mature.trans ((Nat.le_succ _).trans (Nat.lt_two_pow_self (n:=J_ h+1)).le)

end Calibrated

end Phase
end
end Hierarchy.DescentTerminalFixedSlices

end OAI
