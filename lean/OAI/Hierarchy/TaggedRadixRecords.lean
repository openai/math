import OAI.Hierarchy.TaggedData
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace OAI
/-! # Fixed record layout for the initial flagged list and final scan

The two flags distinguish real entries and sort dummies last. The type bit is
the least significant bit of the sorting key. A fixed zero field supplies
missing bits in the most significant partial radix digit.
-/

namespace Hierarchy.Tagged.RadixRecord
open scoped Classical
noncomputable section

def width (h : ℕ) := 2*h+4
abbrev Field (h : ℕ) := Fin 4 ⊕ (Fin h ⊕ Fin h)

def fieldIndex (h : ℕ) : Field h ≃ Fin (width h) :=
  ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by dsimp [width]; omega))

def real (h : ℕ) := fieldIndex h (.inl 0)
def dummy (h : ℕ) := fieldIndex h (.inl 1)
def kind (h : ℕ) := fieldIndex h (.inl 2)
def zero (h : ℕ) := fieldIndex h (.inl 3)
def keyField (h : ℕ) (i : Fin h) := fieldIndex h (.inr (.inl i))
def dataField (h : ℕ) (i : Fin h) := fieldIndex h (.inr (.inr i))

def blank (h : ℕ) (j : Fin (width h)) : Bool := decide (j = dummy h)

def rowIndex (h : ℕ) : Row h ⊕ Row h ≃ Fin (2^(h+1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ]; omega))

def feedField {h : ℕ} (r : Row h ⊕ Row h) : Field h → Fin (pins h h) ⊕ Bool
  | .inl b => .inr (if b=0 then true else if b=2 then r.isRight else false)
  | .inr (.inl j) => r.elim (fun i => .inr (Computability.VPVNP.RAMSerialization.wordBits h i j))
      (fun i => .inl (portIndex h h (.inr (.inl (i,j)))))
  | .inr (.inr j) => r.elim (fun i => .inl (portIndex h h (.inl (i,j))))
      (fun i => .inl (portIndex h h (.inr (.inr (i,j)))))

def feed (h : ℕ) (p : Fin (2^(h+1)) × Fin (width h)) :=
  feedField ((rowIndex h).symm p.1) ((fieldIndex h).symm p.2)

def readFeed {h : ℕ} (x : Fin (pins h h) → Bool) (i : Fin (2^(h+1))) (j : Fin (width h)) :=
  Sum.elim x id (feed h (i,j))

@[simp] theorem feed_real {h : ℕ} (x : Fin (pins h h) → Bool) (i : Fin (2^(h+1))) :
    readFeed x i (real h) = true := by simp [readFeed, feed, feedField, real]
@[simp] theorem feed_dummy {h : ℕ} (x : Fin (pins h h) → Bool) (i : Fin (2^(h+1))) :
    readFeed x i (dummy h) = false := by simp [readFeed, feed, feedField, dummy]
@[simp] theorem feed_zero {h : ℕ} (x : Fin (pins h h) → Bool) (i : Fin (2^(h+1))) :
    readFeed x i (zero h) = false := by simp [readFeed, feed, feedField, zero]
@[simp] theorem feed_kind {h : ℕ} (x : Fin (pins h h) → Bool) (i : Row h ⊕ Row h) :
    readFeed x (rowIndex _ i) (kind h) = i.isRight := by simp [readFeed,feed,feedField,kind]
@[simp] theorem feed_source_key {h : ℕ} (x : Fin (pins h h) → Bool) (i : Row h) (j : Fin h) :
    readFeed x (rowIndex _ (.inl i)) (keyField h j) = Computability.VPVNP.RAMSerialization.wordBits h i j := by
  simp [readFeed,feed,feedField,keyField]
@[simp] theorem feed_target_key {h : ℕ} (x : Fin (pins h h) → Bool) (i : Row h) (j : Fin h) :
    readFeed x (rowIndex _ (.inr i)) (keyField h j) = Computability.VPVNP.RAMSerialization.wordBits h (tag x i) j := by
  simp [readFeed,feed,feedField,keyField, Tagged.tag]
@[simp] theorem feed_source_data {h : ℕ} (x : Fin (pins h h) → Bool) (i : Row h) (j : Fin h) :
    readFeed x (rowIndex _ (.inl i)) (dataField h j) = source x i j := by simp [readFeed,feed,feedField,dataField, Tagged.source]
@[simp] theorem feed_target_data {h : ℕ} (x : Fin (pins h h) → Bool) (i : Row h) (j : Fin h) :
    readFeed x (rowIndex _ (.inr i)) (dataField h j) = target x i j := by simp [readFeed,feed,feedField,dataField, Tagged.target]

/-- Return the fixed bit index for a digit of the integer `2*tag+kind`. -/
def atBit (h b : ℕ) : Fin (width h) := if b=0 then kind h else if hb : b-1<h then keyField h ⟨b-1,hb⟩ else zero h

def digit (h k pass : ℕ) (i : Fin k) := atBit h (pass*k+i.val)

def packValue {h : ℕ} (p : Row h × Bits h) : Bits (h+h) :=
  Fin.append (Computability.VPVNP.RAMSerialization.wordBits h p.1) p.2

theorem packValue_injective (h : ℕ) : Function.Injective (packValue (h := h)) := by
  intro a b same
  apply Prod.ext
  · apply (Computability.VPVNP.RAMSerialization.wordBits h).injective
    funext i
    simpa [packValue] using congrFun same (i.castAdd h)
  · funext i
    simpa only [packValue,Fin.append_right] using congrFun same (Fin.natAdd h i)

def dataTag {h : ℕ} (z : Fin (width h) → Bool) : Row h × Bits h :=
  ((Computability.VPVNP.RAMSerialization.wordBits h).symm (z ∘ keyField h), z ∘ dataField h)

theorem tag_data_feed {h : ℕ} (x : Fin (pins h h) → Bool) (i : Row h ⊕ Row h) :
    dataTag (readFeed x (rowIndex _ i)) = i.elim (fun a => (a,source x a)) (fun a => (tag x a,target x a)) := by
  cases i <;> simp [dataTag, Function.comp_def]

def realWords (h : ℕ) {n : ℕ} (x : (Fin n × Fin (width h)) → Bool) :
    List (Bits (width h)) :=
  (List.ofFn (fun i => fun j => x (i,j))).filter (fun w => w (real h))

def keyValue {h : ℕ} (w : Bits (width h)) : ℕ :=
  2*(dataTag w).1.val+(w (kind h)).toNat

theorem keyValue_lt {h : ℕ} (w : Bits (width h)) : keyValue w < 2^(h+1) := by
  have bound := (dataTag w).1.isLt
  unfold keyValue
  rw [pow_succ]
  cases e : w (kind h) <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

def Canonical (h : ℕ) (w : Bits (width h)) : Prop :=
  w=blank h ∨ (w (real h)=true ∧ w (dummy h)=false ∧ w (zero h)=false)

theorem canonical_feed {h : ℕ} (x : Fin (pins h h) → Bool) (i : Fin (2^(h+1))) :
    Canonical h (readFeed x i) := Or.inr ⟨feed_real x i,feed_dummy x i,feed_zero x i⟩

theorem realWords_feed {h : ℕ} (x : Fin (pins h h) → Bool) :
    realWords h (Sum.elim x id ∘ feed h) = List.ofFn (readFeed x) := by
  change (List.ofFn (readFeed x)).filter (fun w => w (real h)) = _
  apply List.filter_eq_self.mpr
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  exact feed_real x i

end
end Hierarchy.Tagged.RadixRecord

end OAI
