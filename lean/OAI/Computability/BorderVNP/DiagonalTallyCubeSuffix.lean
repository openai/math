import OAI.Computability.BorderVNP.DiagonalTallyRAMAllocatedRun
import OAI.Computability.BorderVNP.DiagonalTallyPacketEmitRun

/-! # Building cube tally operands from the chosen ID array -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCubeSuffix

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM
open DiagonalTallyPacketEmit (written written_before written_at written_step)

/-- Dimensions and physical addresses of the append operation. -/
structure Frame where
  /-- Number of existing private-cell operands. -/
  prior : ℕ
  /-- Number of actual owned cube vertices. -/
  count : ℕ
  /-- Beginning of the five-word operand table. -/
  descriptors : ℕ
  /-- Actual output of the selected cube ID reader. -/
  ids : ℕ
  /-- Source word holding zero. -/
  zeroAddr : ℕ
  /-- Number of parameter coordinates before the gadget bank. -/
  parameters : ℕ

/-- Actual frame seeds supplied by the cell pass and packet-vertex pass. -/
def Frame.resident (f : Frame) (d : ℕ) (m : ℕ → ℕ) : Prop :=
  m (d+35)=f.prior ∧ m (d+46)=f.count ∧ m (d+44)=f.descriptors ∧
    m (d+71)=f.ids ∧ m (d+81)=f.zeroAddr ∧ m (d+95)=f.parameters

/-- Start of the cube suffix following all previously checked cell summaries. -/
def Frame.start (f : Frame) : ℕ := f.descriptors+5*f.prior

/-- Runtime descriptor fields. The frame word at slot 82 already contains the address
of a true literal word and is therefore a one-element reference vector. -/
def Frame.field (f : Frame) (d i : ℕ) : ℕ :=
  let k := i%5
  if k=0 then f.parameters else if k=1 then f.ids+i/5 else if k=2 then d+82 else if k=3 then d+83 else f.zeroAddr

/-- Complete suffix writes and final update of the dynamic operand count. -/
def Frame.image (f : Frame) (d : ℕ) (m : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (written f.start (f.field d) m (5*f.count)) (d+35) (f.prior+f.count)

/-- Read the old count and public addresses, prepare the suffix cursor and directory
addresses, and compute the final count. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 3,.constant 4 5,
  readFrame 5 62 63 35,readFrame 6 62 63 46,readFrame 7 62 63 44,readFrame 8 62 63 71,
  readFrame 9 62 63 81,readFrame 10 62 63 95,.publicWord 11 0,.constant 12 82,
  .binary .add 11 11 12,.binary .add 12 11 1,.binary .mul 13 4 5,.binary .add 13 7 13,
  .copy 14 6,.binary .add 15 5 6,.copy 16 0]

/-- Write the five words for a single vertex, including a dynamic ID pointer and
the directory word serving as a one-element vector of literal-bit addresses. -/
def step : Code := .block [.binary .mul 19 4 16,.binary .add 20 13 19,.binary .add 18 8 16,
  .store 20 10,.binary .add 20 20 1,.store 20 18,.binary .add 20 20 1,.store 20 11,
  .binary .add 20 20 1,.store 20 12,.binary .add 20 20 1,.store 20 9,.binary .add 16 16 1]

/-- Write every cube operand and install the total cell-plus-cube record count. -/
def appendCubeOperands : Code := .block [setup,.whileLt 16 14 step,writeFrame 15 62 63 35]

private structure State (f : Frame) (d i : ℕ) (orig : ℕ → ℕ) (z : NatState) : Prop where
  z0 : z.reg 0=0
  z1 : z.reg 1=1
  z2 : z.reg 2=2
  z3 : z.reg 3=3
  z4 : z.reg 4=5
  ids : z.reg 8=f.ids
  zeroAddr : z.reg 9=f.zeroAddr
  parameters : z.reg 10=f.parameters
  oneRef : z.reg 11=d+82
  oneEnd : z.reg 12=d+83
  start : z.reg 13=f.start
  count : z.reg 14=f.count
  total : z.reg 15=f.prior+f.count
  cursor : z.reg 16=i
  mem : z.mem=written f.start (f.field d) orig (5*i)

variable {w : ℕ}

private theorem step_runs (f : Frame) (d : ℕ) (orig : ℕ → ℕ) (i : ℕ)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (hi : i<f.count) (hroom : f.start+5*f.count<2^w) (hid : f.ids+f.count<2^w)
    (hs : State f d i orig (.ofWords s m)) :
    BoundedRun pub mac step s m step.slots (State f d (i+1) orig) := by
  let z := NatState.ofWords s m
  change State f d i orig z at hs
  have init := hs
  obtain ⟨z0,z1,z2,z3,z4,idb,zAddr,par,oRef,oEnd,start,count,total,cursor,mem⟩ := hs
  have safe : step.fixedSafe w (readings pub) z := by
    simp [step,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,addressOp,z1,z4,idb,start,cursor]
    omega
  apply (step.runFixed pub mac s m safe).mono le_rfl
  intro z' eq
  rw [eq]
  change State f d (i+1) orig (step.fixedEval (readings pub) z)
  constructor
  case cursor => simp [step,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,cursor,z1]
  case mem =>
    simp [step,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,z1,z4,idb,zAddr,par,
      oRef,oEnd,start,cursor,mem]
    rw [show 5*(i+1) = 5*i+1+1+1+1+1 by omega]
    conv_rhs => rw [← written_step,← written_step,← written_step,← written_step,← written_step]
    simp [Frame.field,Nat.mul_add_div (by decide : 0<5),Nat.add_assoc]
  all_goals
    rwa [Code.fixedEval_protected step _ z (show step.protects 16 = true by decide) _ (by decide)]

/-- Exact native assembly of the cube suffix. The preceding cell descriptors survive
when the frame and operand banks occupy disjoint intervals. -/
theorem appendCubeOperands_runs (f : Frame) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hr : f.resident (pub 0).val (readings m))
    (hdir : (pub 0).val+95<2^w) (hspace : f.start+5*f.count<2^w)
    (hids : f.ids+f.count<2^w) :
    ∃ es t mt, Runs pub mac appendCubeOperands s m es t mt ∧
      traceCost es ≤ setup.slots+f.count*(step.slots+1)+1+(writeFrame 15 62 63 35).slots ∧
      readings mt=f.image (pub 0).val (readings m) ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) := by
  obtain ⟨prior,count,desc,ids,zeroAddr,param⟩ := hr
  simp only [readings] at prior count desc ids zeroAddr param
  change f.descriptors+5*f.prior+5*f.count<2^w at hspace
  have hw : w≠0 := by rintro rfl; simp at hdir
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [setup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
      readings,Function.update,addressOpFits,addressOp,hw,prior,count,desc] at ⊢
    omega
  obtain ⟨a,t,ra,ha,ht⟩ := setup.runReadOnly pub mac m s safe
  have init : State f (pub 0).val 0 (readings m) (.ofWords t m) := by
    constructor
    case mem => funext j; simp [written,NatState.ofWords]
    all_goals
      change readings t _ = _
      rw [ht]
      simp (config := {decide := true}) [setup,readFrame,Code.block,Code.evalNat,readings,Function.update,addressOp,
        prior,count,desc,ids,zeroAddr,param,Frame.start]
  obtain ⟨b,u,mu,rb,hb,hu⟩ := run_counted_loop pub mac 16 14 step f.count step.slots
    (fun i => State f (pub 0).val i (readings m)) (fun _ _ h => ⟨h.cursor,h.count⟩)
    (fun i hi su mu h => step_runs f _ _ i pub mac su mu hi hspace hids h) 0 (by omega) t m init
  let z := NatState.ofWords u mu
  have endSafe : (writeFrame 15 62 63 35).fixedSafe w (readings pub) z := by
    simp [writeFrame,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,readings]; omega
  obtain ⟨c,y,my,rc,hc,hy⟩ := (writeFrame 15 62 63 35).runFixed pub mac u mu endSafe
  have run := ra.seq (rb.seq rc)
  refine ⟨_,_,_,run,?_,?_,DiagonalTallyRAM.ordinary_run (show DiagonalTallyRAM.ordinary appendCubeOperands = true by decide) run⟩
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+traceCost c) ≤ _
    simp only [Nat.sub_zero] at hb
    omega
  · have h := congrArg NatState.mem hy
    change readings my=((writeFrame 15 62 63 35).fixedEval (readings pub) z).mem at h
    rw [h]
    change State f (pub 0).val f.count (readings m) z at hu
    simp [writeFrame,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,Frame.image,
      hu.total,hu.mem,readings]

end DiagonalTallyCubeSuffix

end BorderVNP
end Computability
end OAI
