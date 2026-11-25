import OAI.ThreeFlat.Diagonal.TraceCircuit
import OAI.ThreeFlat.Diagonal.TraceRowMasks

namespace OAI
/-! # Distributing a short, input-dependent instruction table across the CPU rows

Each bit of the program text has a designated input row. A chain of
pairwise equality factors makes that bit available in every physical row.
The extra width per row is the instruction-table length, independently of
the total number of clock rows and of the full advice length.
-/

namespace ThreeFlat.Diagonal.TraceAdvice

variable {F α : Type*} {t b : ℕ}

/-- Each row copies the same text bits to its neighbor. The row owning a
text pin additionally compares its own copy to that input. -/
def Copies (owner : Fin b → Fin t) (text : Fin b → α) (v : Fin t → Fin b → α) : Prop :=
  (∀ i, v (owner i) i = text i) ∧
    ∀ j j' : Fin t, j.val+1 = j'.val → ∀ i, v j i = v j' i

private theorem constant_on_rows (a : Fin t → α)
    (ha : ∀ j j' : Fin t, j.val+1 = j'.val → a j = a j') (u v : Fin t) : a u = a v := by
  have ht : 0 < t := Nat.zero_lt_of_lt u.isLt
  let z : Fin t := ⟨0,ht⟩
  have h0 (v : Fin t) : a z = a v := by
    obtain ⟨v,hv⟩ := v
    induction v with
    | zero => rfl
    | succ v ih => exact (ih (by omega)).trans (ha ⟨v,by omega⟩ ⟨v+1,hv⟩ rfl)
  exact (h0 u).symm.trans (h0 v)

/-- The text copies have exactly one valid assignment for every choice of
the open program pins, including on unused opcode and operand bits. -/
theorem copies_iff (owner : Fin b → Fin t) (text : Fin b → α) (v : Fin t → Fin b → α) :
    Copies owner text v ↔ v = fun _ => text := by
  constructor
  · rintro ⟨hp,he⟩
    funext row i
    exact (constant_on_rows (fun u => v u i) (fun j j' h => he j j' h i) row (owner i)).trans (hp i)
  · rintro rfl
    exact ⟨fun _ => rfl,fun _ _ _ _ => rfl⟩

/-- Equality chains can be inserted into any weighted trace without
changing its value. Every row can then read all program text bits locally. -/
theorem sum_copies [AddCommMonoid F] (owner : Fin b → Fin t) (text : Fin b → Bool)
    (g : (Fin t → Fin b → Bool) → F) :
    letI := Classical.propDecidable
    (∑ v, if Copies owner text v then g v else 0) = g (fun _ => text) := by
  classical
  simp [copies_iff]

/-- A binary equality factor has two active ports; the third is padded. -/
def eqCell [Zero F] [One F] {n p : ℕ} (x y : BitSource n p) : TraceCircuit.Cell F n p :=
  ⟨![x,y,.constant false],fun z => if z 0 = z 1 then 1 else 0⟩

theorem eqCell_at [Zero F] [One F] {n p : ℕ} (x y : BitSource n p)
    (hidden : Fin n → Bool) (pin : Fin p → Bool) :
    (eqCell (F:=F) x y).eval pin hidden = if x.read hidden pin = y.read hidden pin then 1 else 0 := rfl

/-- Every equality link between different rows uses one of the previously
enumerated low-bit carry masks; the bound covers every broadcast bit. -/
theorem copy_offset {d : ℕ} (u v : Fin (2^d)) (h : u.val + 1 = v.val) :
    ∃ i, 0 < i ∧ i ≤ d ∧ (u.val ^^^ v.val) = 2^i-1 := by
  have hb : u.val + 1 < 2^d := h.trans_lt v.isLt
  simpa only [h] using TraceRowMasks.adjacent_mask hb

end ThreeFlat.Diagonal.TraceAdvice

end OAI
