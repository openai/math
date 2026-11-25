import OAI.Hierarchy.ProbeStageWordStore
import OAI.Hierarchy.ProbeStagePackedMasks

namespace OAI
/-! # Direct native lookup of a record's first jointly free candidate -/

namespace Hierarchy.ProbeStage.FastField
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- All offsets are physical word addresses. Four entries are private scratch words refreshed
from the current record, while `leastTable` is shared fixed advice for every color string. -/
structure Layout where
  leftMask : ℕ
  rightMask : ℕ
  wordOffset : ℕ
  leastTable : ℕ
  output : ℕ
  width : ℕ
  length : ℕ
  chunks : ℕ

def cell (a : ℕ) : Formula 1 := .load (.lit a)

def wordAt (base offset k : ℕ) : Formula 1 := .load (.op .add (.op .add (cell base) (cell offset)) (.lit k))

def common (s : Layout) (k : ℕ) : Formula 1 :=
  .op .bitAnd (wordAt s.leftMask s.wordOffset k) (wordAt s.rightMask s.wordOffset k)

def first (s : Layout) : List ℕ → Formula 1
  | [] => .lit s.length
  | k::ks => .select .eq (common s k) (.lit 0) (first s ks)
      (.op .add (.lit (k*s.width)) (.load (.op .add (.lit s.leastTable) (common s k))))

def code (s : Layout) := first s (List.range s.chunks)

def procedure (w : ℕ) (s : Layout) := WordStore.put w s.output (code s)

def image {w : ℕ} (s : Layout) (m : Memory w) := Function.update m s.output (WordStore.value s.output (code s) m)

theorem execute {w : ℕ} (s : Layout) (m : Memory w) (fit : s.output+1<2^w) :
    (procedure w s).Exec m (image s m) (2*(code s).work+8) := by
  exact WordStore.execute s.output (code s) m fit

theorem work (s : Layout) : (code s).work=1+41*s.chunks := by
  have aux (ks : List ℕ) : (first s ks).work=1+41*ks.length := by
    induction ks with
    | nil => rfl
    | cons k ks ih => simp [first,Formula.work,common,wordAt,cell,ih];omega
  simpa [code] using aux (List.range s.chunks)

def availableWord {w : ℕ} (s : Layout) (m : Memory w) (k : ℕ) : Word w :=
  let readAt := fun base : ℕ => m (m (base:Word w).val+m (s.wordOffset:Word w).val+(k:Word w)).val
  BinaryOp.bitAnd.eval (readAt s.leftMask) (readAt s.rightMask)

def lookup {w : ℕ} (s : Layout) (m : Memory w) : List ℕ → Word w
  | [] => (s.length:Word w)
  | k::ks => let v := availableWord s m k
             if v=0 then lookup s m ks else ((k*s.width:ℕ):Word w)+m ((s.leastTable:Word w)+v).val

theorem first_eval {w : ℕ} (s : Layout) (m : Memory w) (ks : List ℕ) :
    WordStore.value s.output (first s ks) m=lookup s m ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [WordStore.value,first,Formula.value,wordAt,common,cell,BinaryOp.eval,Comparison.test,
      lookup,availableWord,beq_iff_eq] at ih ⊢
    rw [ih]
    rfl

end Hierarchy.ProbeStage.FastField

end OAI
