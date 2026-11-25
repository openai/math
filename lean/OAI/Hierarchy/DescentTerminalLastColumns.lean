import OAI.Hierarchy.DescentCensusRAM
import OAI.Hierarchy.DescentTerminalDenseMask

namespace OAI
/-! # Final bounded RAM operations for every candidate, including malformed ones -/
namespace Hierarchy.DescentTerminalLast
open DescentCensusRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w rows pool bins word : ℕ}

def atZero (b : Bank) : Expr := .lookup b (.lit 0)
def cutoff (word whole tail i : ℕ) := if i<whole then word else if i=whole then min word tail else 0

theorem cutoff_le (word whole tail i : ℕ) : cutoff word whole tail i≤word := by
  unfold cutoff;split_ifs <;>first | exact min_le_left .. | omega

theorem cutoff_valid (word total i : ℕ) (hw : 0<word) :
    cutoff word (total/word) (total%word) i=DescentTerminalDenseMask.valid word total i := by
  have h:=Nat.div_add_mod total word
  have rem:=Nat.mod_lt total hw
  have exactSum : (total/word)*word+total%word=total := by simpa [Nat.mul_comm] using h
  unfold cutoff DescentTerminalDenseMask.valid
  by_cases before : i<total/word
  · have amount:=Nat.mul_le_mul_right word before
    rw [Nat.succ_mul] at amount
    simp [before,min_eq_left (by omega : word≤total-i*word)]
  · by_cases last : i=total/word
    · subst i
      simp [show total-total/word*word=total%word by omega]
    · have beyond : total/word+1≤ i:=by omega
      have amount:=Nat.mul_le_mul_right word beyond
      rw [Nat.succ_mul] at amount
      simp [before,last,Nat.sub_eq_zero_of_le (by omega : total≤ i*word)]

def clipped (whole tail : Bank) (word : ℕ) : Expr :=
  let q:=atZero whole
  let rem:=atZero tail
  let last:=Expr.branch .lt rem (.lit word) rem (.lit word)
  .branch .lt .row q (.lit word) (.branch .eq .row q last (.lit 0))

def safeKey (S : Banks w pool bins) (keys : Bank) : Expr :=
  let x:=Expr.lookup keys .row
  .op .add (.lit S.bins) (.branch .lt x (.lit bins) x (.lit 0))

def stopBit (flags : Fin 4→Bank) : Expr :=
  let ok:=fun i rest=>Expr.branch .eq (atZero (flags i)) (.lit 0) rest (.lit 1)
  ok 0 (ok 1 (ok 2 (ok 3 (.lit 0))))

structure Tape where
  whole : Bank
  tail : Bank
  keys : Bank
  flags : Fin 4→Bank

def Tape.inputs (L : Tape) := [L.whole,L.tail,L.keys,L.flags 0,L.flags 1,L.flags 2,L.flags 3]
structure Ready (L : Tape) (S : Banks w pool bins) (cut stop rows word : ℕ) : Prop where
  inputs : ∀z∈L.inputs,z.Fits w cut
  keyCap : pool≤L.keys.size
  clear : cut+rows≤S.first
  counted : S.bins+bins≤ stop
  final : stop+1<2^w
  bits : word<2^w
  binsPos : 0<bins
  poolFit : pool<2^w

def evalKey (L : Tape) (positive : 0<bins) (mem : Memory w) (i : Fin pool) : Fin bins :=
  let x:=(mem (L.keys.base+i.val)).val
  if h : x<bins then ⟨x,h⟩ else ⟨0,positive⟩

def badBit (L : Tape) (m : Memory w) : ℕ := if ∀i,m (L.flags i).base=0 then 0 else 1

def program (L : Tape) (S : Banks w pool bins) (cut stop rows word : ℕ) :=
  ((scan w cut rows (clipped L.whole L.tail word)).seq
    (tally S (safeKey S L.keys) (.lit 1))).seq (scan w stop 1 (stopBit L.flags))

def ticks (L : Tape) (S : Banks w pool bins) (rows word : ℕ) :=
  (4+rows*(2*(clipped L.whole L.tail word).work+4))+tallyCost S (safeKey S L.keys) (.lit 1)+
    (4+1*(2*(stopBit L.flags).work+4))

theorem cheap (L : Tape) (S : Banks w pool bins) (cut stop rows word : ℕ) :
    CheapCode (program L S cut stop rows word) := by
  let cuts := scan w cut rows (clipped L.whole L.tail word)
  let keys := tally S (safeKey S L.keys) (.lit 1)
  let flag := scan w stop 1 (stopBit L.flags)
  exact @cheap_seq w (cuts.seq keys) flag
    (@cheap_seq w cuts keys
      (@scan_cheap w cut rows (clipped L.whole L.tail word))
      (@tally_cheap w pool bins S (safeKey S L.keys) (.lit 1)))
    (@scan_cheap w stop 1 (stopBit L.flags))

theorem ticks_exact (L : Tape) (S : Banks w pool bins) (rows word : ℕ) :
    ticks L S rows word=(4+rows*(2*35+4))+
      tallyCost S (safeKey S L.keys) (.lit 1)+(4+1*(2*37+4)) := rfl

private theorem low (e : Expr) (m : Memory w) {n base a : ℕ} (h : a<base) :
    ProtocolRAM.image base n e m a=m a := by simp [ProtocolRAM.image,fillSegment,not_le.mpr h]

private theorem rowRead (e : Expr) (m : Memory w) {n base : ℕ} (i : Fin n) :
    ProtocolRAM.image base n e m (base+i.val)=e.eval m (i.val:Word w) := by
  simp [ProtocolRAM.image,fillSegment,show base+i.val<base+n by have:=i.isLt;omega,Nat.cast_add]

private theorem same (b : Bank) (m : Memory w) {n out : ℕ} (h : n<b.size) (safe : b.Fits w out) :
    b.read m (n:Word w)=m (b.base+n) := by
  simp [Bank.read,Fin.val_cast_of_lt (h.trans safe.2.1),Nat.mod_eq_of_lt h]

private theorem cmp {v t : ℕ} (a : v<2^w) (b : t<2^w) : (v:Word w)<(t:Word w) ↔ v<t := by
  change ((v:Word w).val<(t:Word w).val) ↔ _
  rw [Fin.val_cast_of_lt a,Fin.val_cast_of_lt b]

theorem cutoff_read (L : Tape) (S : Banks w pool bins) {cut stop : ℕ}
    (ready : Ready L S cut stop rows word) (m : Memory w) (i : Fin rows) :
    (clipped L.whole L.tail word).eval m (i.val:Word w)=
      (cutoff word (m L.whole.base).val (m L.tail.base).val i.val:Word w) := by
  let q:=(m L.whole.base).val
  let r:=(m L.tail.base).val
  have tailWord : (r:Word w)=m L.tail.base := Fin.cast_val_eq_self _
  have hi : i.val<2^w:=by
    have:=i.isLt;have:=ready.clear;have:=S.scratch;have:=S.beforeTape;have:=S.beforeBins;have:=S.finish;omega
  have before : (i.val:Word w) < m L.whole.base ↔ i.val<q := by
    change (i.val:Word w).val < _ ↔ _
    rw [Fin.val_cast_of_lt hi]
  have eq : (i.val:Word w)=m L.whole.base ↔ i.val=q := by
    rw [Fin.ext_iff, Fin.val_cast_of_lt hi]
  have small : m L.tail.base < (word:Word w) ↔ r<word := by
    change _ < (word:Word w).val ↔ _
    rw [Fin.val_cast_of_lt ready.bits]
  have base (b : Bank) : b.read m 0=m b.base:=by simp [Bank.read]
  simp only [clipped, Expr.eval, atZero, Nat.cast_zero, base, Comparison.test,
    decide_eq_true_eq, beq_iff_eq, before, eq, small]
  change (if i.val<q then (word:Word w) else if i.val=q then
    (if r<word then m L.tail.base else (word:Word w)) else 0)=(cutoff word q r i.val:Word w)
  by_cases earlier : i.val<q
  · simp only [cutoff, ite_eq_left earlier]
  simp only [cutoff, ite_eq_right earlier]
  by_cases here : i.val=q
  · simp only [ite_eq_left here]
    by_cases short : r<word
    · simp only [ite_eq_left short, min_eq_right short.le, tailWord]
    · simp only [ite_eq_right short, min_eq_left (Nat.le_of_not_gt short)]
  · simp only [ite_eq_right here, Nat.cast_zero]

theorem safeKey_read (L : Tape) (S : Banks w pool bins) {cut stop : ℕ} (ready : Ready L S cut stop rows word)
    (m : Memory w) (i : Fin pool) : (safeKey S L.keys).eval m (i.val:Word w)=
      ((S.bins+(evalKey L ready.binsPos m i).val:ℕ):Word w) := by
  have get:=same L.keys m (i.isLt.trans_le ready.keyCap) (ready.inputs _ (by simp [Tape.inputs]))
  have room : bins<2^w:=by have:=S.finish;omega
  let x:=(m (L.keys.base+i.val)).val
  have raw : m (L.keys.base+i.val)=(x:Word w) := (Fin.cast_val_eq_self _).symm
  have hx : x<2^w:=(m _).isLt
  simp only [safeKey,Expr.eval,RowOp.opcode,BinaryOp.eval,get,raw,Comparison.test,decide_eq_true_eq,cmp hx room,evalKey]
  by_cases h : x<bins <;>simp [x,h,Nat.cast_add] at *

theorem stop_read (L : Tape) (m : Memory w) : (stopBit L.flags).eval m 0=(badBit L m:Word w) := by
  have singleton (z : Bank) : z.read m (0:Word w)=m z.base:=by simp [Bank.read]
  have all : (∀i:Fin 4,m (L.flags i).base=0) ↔ m (L.flags 0).base=0 ∧ m (L.flags 1).base=0 ∧
      m (L.flags 2).base=0 ∧ m (L.flags 3).base=0 := by
    constructor
    · intro h;exact ⟨h _,h _,h _,h _⟩
    · rintro ⟨a,b,c,d⟩ i;fin_cases i <;>assumption
  simp only [stopBit,atZero,Expr.eval,Comparison.test,beq_iff_eq,badBit,all]
  split_ifs <;>simp_all

end
end Hierarchy.DescentTerminalLast

end OAI
