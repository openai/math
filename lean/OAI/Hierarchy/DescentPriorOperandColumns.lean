import OAI.Hierarchy.DescentPackedNodeDigit
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Native projection of the previous node's operand fields from its compact archive -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {P K H G a M w : ℕ}

/-- The same `K` digit tables serve every field, operand and host. -/
def expressions (old : Fin P→Bank) (a K M base : ℕ) : List Expr := List.ofFn fun i : Fin (P*K)=>
  let z:=finProdFinEquiv.symm i
  ScalarOperand.project (ScalarOperand.chart base a K M) (.lookup (old z.1) .row) z.2

def program (old : Fin P→Bank) (a K M rows w base out : ℕ) :=
  (ROM.mount (ScalarOperand.pages a K M) ((a*K)*M) w base).seq
    (ProtocolRAM.program w (ProbeStage.Native.columns rows out (expressions old a K M base)))

def image (old : Fin P→Bank) (a K M rows base out : ℕ) (m : Memory w) :=
  ProtocolRAM.result (ProbeStage.Native.columns rows out (expressions old a K M base))
    (ROM.after (ScalarOperand.pages a K M) ((a*K)*M) base m)

theorem cheap (old : Fin P→Bank) (a K M rows w base out : ℕ) : CheapCode (program old a K M rows w base out) :=
  cheap_seq (ROM.cheap (ScalarOperand.pages a K M) ((a*K)*M) w base)
    (program_cheap w (ProbeStage.Native.columns rows out (expressions old a K M base)))

def ticks (old : Fin P→Bank) (a K M rows base out : ℕ) :=
  4+10*(K*2^((a*K)*M))+ProtocolRAM.clock (ProbeStage.Native.columns rows out (expressions old a K M base))

def place (out rows : ℕ) (p : Fin P) (slot : Fin K) := out+(finProdFinEquiv (p,slot)).val*rows

def fieldBank (out rows : ℕ) (p : Fin P) (slot : Fin K) : Bank := ⟨place out rows p slot,Nat.clog 2 (rows+1)⟩

theorem tariff (old : Fin P→Bank) (a K M rows base out : ℕ) :
    ticks old a K M rows base out≤4+10*(K*2^((a*K)*M))+(4+(P*K)*(4+28*rows)) := by
  have bound : ∀e∈expressions old a K M base,e.work≤12 := by
    intro e h;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h;exact le_rfl
  have h:=ProbeStage.Native.columns_clock rows out 12 (expressions old a K M base) bound
  simpa [ticks,expressions,Nat.mul_comm] using Nat.add_le_add_left h (4+10*(K*2^((a*K)*M)))

/-- All inputs, including malformed old books, run for the same clock. -/
theorem exec (old : Fin P→Bank) (a K M rows base out : ℕ) (m : Memory w)
    (low : ∀p,(old p).Fits w base) (spaced : base+K*2^((a*K)*M)≤out) (room : out+(P*K)*rows<2^w) :
    (program old a K M rows w base out).Exec m (image old a K M rows base out m) (ticks old a K M rows base out) := by
  let pages:=ScalarOperand.pages a K M
  let d:=(a*K)*M
  let terms:=expressions old a K M base
  have dst : out<2^w:=(Nat.le_add_right ..).trans_lt room
  have fits : ∀e∈terms,e.Fits w out:=by
    intro e member;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
    let z : Fin P×Fin K:=finProdFinEquiv.symm i
    have h:=low z.1
    exact ⟨ROM.bank_room pages d base out z.2 le_rfl spaced dst,
      ⟨h.1,h.2.1,(h.2.2.trans (Nat.le_add_right ..)).trans spaced⟩,True.intro⟩
  let mid:=ROM.after pages d base m
  have first : (ROM.mount pages d w base).Exec m mid (4+10*(K*2^d)):=(ROM.run pages d base m (spaced.trans_lt dst)).1
  let ps:=ProbeStage.Native.columns rows out terms
  have last : (ProtocolRAM.program w ps).Exec mid (ProtocolRAM.result ps mid) (ProtocolRAM.clock ps):=
    ProbeStage.Native.columns_exec terms mid (ProbeStage.Native.columns_safe terms le_rfl fits
      (by simpa only [terms,expressions,List.length_ofFn] using room))
  intro P₀ R K₀ machine; exact Procedure.Exec.then first last machine

theorem frame {w : ℕ} (old : Fin P→Bank) (a K M rows base out : ℕ) (m : Memory w) (x : ℕ)
    (tables : x<base ∨ base+K*2^((a*K)*M)≤x) (writes : x<out ∨ out+(P*K)*rows≤x) :
    image old a K M rows base out m x=m x := by
  exact (ProbeStage.Native.columns_frame (expressions old a K M base) _
    (by simpa only [expressions,List.length_ofFn] using writes)).trans (ROM.frame _ _ _ _ _ tables)

variable (old : Fin P→Bank) (base out : ℕ) (m : Memory w)
local notation "nrows" => H*chunks G M
local notation "book" => ScalarOperand.pages a K M
local notation "wid" => (a*K)*M
local notation "es" => expressions old a K M base
local notation "mid" => ROM.after book wid base m

/-- Each fixed earlier node index receives a real packed column at the original
field and operand page. Dead node digits in the previous book remain zero. -/
theorem run (values : Fin P→Fin H→Fin G→Cell (a*K)) (low : ∀p,(old p).Fits w base)
    (capacity : ∀p,nrows≤(old p).size) (spaced : base+K*2^wid≤out)
    (room : out+(P*K)*nrows<2^w) (prior : ∀p,Reads (old p) (values p) M m) :
    let state:=image old a K M nrows base out m
    (program old a K M nrows w base out).Exec m state (ticks old a K M nrows base out) ∧
      (∀p slot,Reads (fieldBank out nrows p slot) (fun h g=>ScalarOperand.take slot (values p h g)) M state) ∧
      (∀j,(j<base ∨ base+K*2^wid≤j)→(j<out ∨ out+(P*K)*nrows≤j)→state j=m j) ∧
      CheapCode (program old a K M nrows w base out) := by
  intro state
  have ofit:= (Nat.le_add_right out ((P*K)*nrows)).trans_lt room
  have low' (p : Fin P) : (old p).Fits w out :=
    ⟨(low p).1,(low p).2.1,((low p).2.2.trans (Nat.le_add_right ..)).trans spaced⟩
  have fit (j : Fin K) : (ScalarOperand.chart base a K M j).Fits w out:=
    ROM.bank_room book wid base out j le_rfl spaced ofit
  have len : (es).length=P*K:=by simp [expressions]
  have fits : ∀e∈es,e.Fits w out:=by
    intro e member;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp member
    exact ⟨fit _,low' _,True.intro⟩
  refine ⟨exec old a K M nrows base out m low spaced room,?_,?_,cheap_seq (ROM.cheap book wid w base) (program_cheap w (ProbeStage.Native.columns nrows out es))⟩
  · intro p slot row'
    have kept : Reads (old p) (values p) M mid := by
      intro q
      have addr: (old p).base+(row H G M q).val<base:=
        (Nat.add_lt_add_left ((row H G M q).isLt.trans_le (capacity p)) _).trans_le (low p).2.2
      exact (ROM.frame book wid base m _ (.inl addr)).trans (prior p q)
    have observed:=ScalarOperand.fetched (ScalarOperand.chart base a K M) (.lookup (old p) .row)
      slot out mid (values p) (source_column _ out (low' p) mid _ (capacity p) kept)
      (fit slot) rfl (ScalarOperand.initialized base a K M m slot) row'
    let i : Fin (P*K):=finProdFinEquiv (p,slot)
    have hi:=i.isLt.trans_eq len.symm
    have emitted:=ProbeStage.Native.columns_read es mid le_rfl fits i.val hi (row H G M row')
    have term : (es)[i.val]'hi=ScalarOperand.project (ScalarOperand.chart base a K M) (.lookup (old p) .row) slot := by
      simp only [expressions, List.getElem_ofFn, Fin.eta, i, Equiv.symm_apply_apply]
    rw [term] at emitted
    exact emitted.trans observed
  · intro j away outOf
    exact (ProbeStage.Native.columns_frame es mid (by simpa only [len] using outOf)).trans (ROM.frame book wid base m _ away)

end
end Hierarchy.DescentPriorOperandColumns

end OAI
