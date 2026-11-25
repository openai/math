import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReports
import OAI.Computability.BorderVNP.RoutingISATableEvents
import OAI.Computability.BorderVNP.DiagonalTallyReportPublish
import OAI.Computability.BorderVNP.DiagonalTallyReportHeaderRun

/-! # Native register and memory transitions of finite scalar report preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyCellReports
open TeamRAM

/-- Public pointers and uniform field alphabet/word width for this team. -/
structure Layout where
  /-- Address of the team frame. -/
  frame : ℕ
  /-- Pointer stored in frame word 92. -/
  control : ℕ
  /-- Beginning of the compact six-word owned-cell directory. -/
  headers : ℕ
  /-- Beginning of the two-word supplemental counters per global cell. -/
  counters : ℕ
  /-- Table of appended bit lengths by global cell ordinal. -/
  tails : ℕ
  /-- Number of scalar labels in the fixed finite field alphabet. -/
  scalars : ℕ
  /-- Number of little-endian bits reported per scalar. -/
  digits : ℕ

/-- The setup reads these actual frame words, including the true owned count
published before report preparation. -/
def Layout.Seed (l : Layout) (owned : ℕ) (m : ℕ → ℕ) : Prop :=
  m (l.frame+92)=l.control ∧ m (l.frame+90)=owned ∧ m (l.control+17)=l.headers ∧
  m (l.control+27)=l.scalars ∧ m (l.control+22)=l.digits ∧ m (l.control+14)=l.counters ∧
  m (l.control+7)=l.tails

/-- Registers retained across all subsequent cells and report guesses. -/
def Layout.Loaded (l : Layout) (r : Reg → ℕ) : Prop :=
  r 10=l.scalars ∧ r 11=l.digits ∧ r 13=l.counters ∧ r 14=l.tails

/-- Physical setup of the row loop. -/
theorem setup_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (owned : ℕ) (ptr : (pub 0).val=l.frame) (seed : l.Seed owned (readings m))
    (frame : l.frame+92 < 2^w) (control : l.control+27 < 2^w) (room : l.headers+6*owned < 2^w) :
    ∃ es t, Runs pub mac setup s m es t m ∧ TraceOK es [] es.length ∧ traceCost es ≤ setup.slots ∧
      l.Loaded (readings t) ∧ (t 0).val=l.headers ∧ (t 1).val=l.headers+6*owned := by
  obtain ⟨hc,ho,hh,hs,hd,hct,ht⟩ := seed
  simp only [readings] at hc ho hh hs hd hct ht
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [setup,readControl,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,addressOp,readings,ptr,hc,ho,hh]
    omega
  obtain ⟨es,t,run,cost,st⟩ := setup.runReadOnly pub mac m s safe
  have quiet := run.unsigned_events (by decide : setup.unsigned=true)
  have trace : TraceOK es [] es.length :=
    ⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (quiet e he).1,fun e he => (quiet e he).2⟩
  refine ⟨es,t,run,trace,cost,?_⟩
  change l.Loaded (readings t) ∧ readings t 0=_ ∧ readings t 1=_
  rw [st]
  simp (config := {decide := true}) [setup,readControl,readFrame,Code.block,Code.evalNat,Function.update,
    addressOp,readings,ptr,hc,ho,hh,hs,hd,hct,ht,Layout.Loaded,Nat.mul_comm 6]

/-- The three header fields read by this stage and the bits chosen at this row. -/
structure Row where
  /-- Global cell ordinal in the current compact header. -/
  number : ℕ
  /-- Physical beginning of this cell’s supplied bit array. -/
  base : ℕ
  /-- Length of the already delivered boundary before the reports. -/
  canonical : ℕ
  /-- Actual fresh report bits in chronological order. -/
  bits : List Bool

/-- Start of the actual reported-bit interval in the supplied bank. -/
def Row.start (r : Row) := r.base+r.canonical

/-- Only the first three words of the six-word public header are read. -/
def Row.Stored (r : Row) (p : ℕ) (m : ℕ → ℕ) : Prop := m p=r.number ∧ m (p+1)=r.base ∧ m (p+2)=r.canonical

/-- All scratch arithmetic and addressed words of a single row are in the machine range. -/
def Row.Fits (r : Row) (l : Layout) (w p : ℕ) : Prop :=
  p+6 < 2^w ∧ r.start+r.bits.length < 2^w ∧ l.counters+2*r.number+1 < 2^w ∧
  l.tails+r.number < 2^w ∧ r.bits.length=l.scalars*l.digits

/-- Exact values stored before the fresh scalar bits. -/
def Row.counters (r : Row) (l : Layout) (m : ℕ → ℕ) :=
  Function.update (Function.update (Function.update m (l.tails+r.number) r.bits.length)
    (l.counters+2*r.number) 0) (l.counters+2*r.number+1) 0

/-- Full output image for one owned cell. -/
def Row.image (r : Row) (l : Layout) (m : ℕ → ℕ) :=
  Packing.BottomReports.Writer.write (r.counters l m) r.start (r.bits.map Bool.toNat)

/-- Native evaluation of the whole deterministic header and counter fragment. -/
private theorem prefix_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (r : Row) (p : ℕ) (ptr : (s 0).val=p) (loaded : l.Loaded (readings s))
    (stored : r.Stored p (readings m)) (fit : r.Fits l w p) :
    let headCode := Code.seq beginCell publish
    ∃ es t mt, Runs pub mac headCode s m es t mt ∧ TraceOK es [] headCode.slots ∧ traceCost es=headCode.slots ∧
      readings mt=r.counters l (readings m) ∧ (t 0).val=p+6 ∧ (t 18).val=r.bits.length ∧ (t 22).val=r.start := by
  intro headCode
  let z := NatState.ofWords s m
  obtain ⟨hf,hd,hc,ht⟩ := loaded
  obtain ⟨hn,hb,hs⟩ := stored
  obtain ⟨ph,space,counter,tail,length⟩ := fit
  change z.reg 0=p at ptr
  change z.reg 10=l.scalars at hf
  change z.reg 11=l.digits at hd
  change z.reg 13=l.counters at hc
  change z.reg 14=l.tails at ht
  change z.mem p=r.number at hn
  change z.mem (p+1)=r.base at hb
  change z.mem (p+2)=r.canonical at hs
  dsimp only [Row.start] at space
  have wpos : w ≠ 0 := by rintro rfl; simp at ph
  have safe : headCode.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [headCode,beginCell,publish,consume,Code.block,Code.fixedSafe,Code.fixedEval,
      Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,Function.update,ptr,hf,hd,hc,ht,hn,hb,hs,
      Nat.add_assoc,Nat.mul_comm r.number 2]
    omega
  obtain ⟨es,t,mt,run,_,state⟩ := headCode.runFixed pub mac s m safe
  change NatState.ofWords t mt=headCode.fixedEval (readings pub) z at state
  have trace : TraceOK es [] headCode.slots := by
    obtain ⟨rfl,_,_⟩ := run.unique_of_deterministic (by decide) (effect_runs pub mac false s m headCode (by decide))
    simp [headCode,beginCell,publish,consume,Code.block,effect,TraceOK,tick,Code.slots]
  refine ⟨es,t,mt,run,trace,(plain_return headCode (by decide) run).1.trans trace.1,?_⟩
  change (NatState.ofWords t mt).mem=_ ∧ (NatState.ofWords t mt).reg 0=_ ∧ (NatState.ofWords t mt).reg 18=_ ∧
    (NatState.ofWords t mt).reg 22=_
  rw [state]
  simp (config := {decide := true}) [headCode,beginCell,publish,consume,Code.block,Code.fixedEval,Code.evalNat,addressOp,
    Function.update,ptr,hf,hd,hc,ht,hn,hb,hs,Nat.add_assoc,Nat.mul_comm r.number 2,Row.start,Row.counters,length]
  rfl

/-- Every prescribed chronological report stream is an actual native run at
its physical tail address; the only nondeterministic events are those bits. -/
theorem cell_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (r : Row) (p : ℕ) (ptr : (s 0).val=p) (loaded : l.Loaded (readings s))
    (stored : r.Stored p (readings m)) (fit : r.Fits l w p) :
    ∃ es t mt, Runs pub mac cell s m es t mt ∧ TraceOK es r.bits (beginCell.slots+publish.slots+6*r.bits.length+6) ∧
      traceCost es=beginCell.slots+publish.slots+6*r.bits.length+6 ∧ readings mt=r.image l (readings m) ∧
      (t 0).val=p+6 ∧ (t 1).val=(s 1).val ∧ l.Loaded (readings t) := by
  obtain ⟨es,u,mu,rp,tp,cp,mem,pos,num,start⟩ := prefix_run pub mac s m l r p ptr loaded stored fit
  obtain ⟨ts,t,rg,tg,kept⟩ := guessReports_runs pub mac u mu r.start r.bits start num fit.2.1
  have rc : Runs pub mac cell s m (es++ts) t (putBits mu r.start r.bits) := by
    change Runs pub mac (.seq beginCell (.seq publish guessReports)) _ _ _ _ _
    cases rp with
    | seq first second => simpa only [List.append_assoc] using Runs.seq first (Runs.seq second rg)
    | atom h => cases h
  have trace := tp.append tg
  have hk (j : Reg) (h : cell.keeps j=true) : readings t j=readings s j := congrArg Fin.val (rc.keepsReg h)
  refine ⟨_,_,_,rc,?_,?_,?_,(congrArg Fin.val (kept 0 (by decide))).trans pos,hk 1 (by decide),?_⟩
  · simpa only [Code.slots,Nat.add_assoc,List.nil_append] using trace
  · have plain := (plain_return cell (by decide) rc).1
    rw [plain,trace.1]
    simp [Code.slots,Nat.add_assoc]
  · rw [guessed_readings mu r.start r.bits (by have := fit.1; omega)]
    rw [mem]
    rfl
  · exact ⟨(hk 10 (by decide)).trans loaded.1,(hk 11 (by decide)).trans loaded.2.1,
      (hk 13 (by decide)).trans loaded.2.2.1,(hk 14 (by decide)).trans loaded.2.2.2⟩

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
