import OAI.ThreeFlat.Diagonal.RefreshDemandChoice
import OAI.ThreeFlat.Diagonal.RefreshSlotRewrite

namespace OAI
/-! # Public width descriptor for each numbered refresh output slot -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows RefreshTies CompressorPacking.Native
open scoped Classical BigOperators
noncomputable section

variable {n : ℕ}

/-- Fixed finite ROM. Every invalid index, including padded graph slots,
produces the zero-width word. -/
def rowAt : (size : ℕ) → (Fin size → Formula n) → Formula n → Formula n
  | 0, _, _ => .lit 0
  | k+1, f, i => .select .eq i (.lit k) (f (Fin.last k)) (rowAt k (fun j => f j.castSucc) i)

section
variable (u : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural u data mem vs

theorem rowAt_hit {k : ℕ} (f : Fin k → Formula n) (i : Formula n) (j : Fin k) (h : V i = j.val) :
    V (rowAt k f i) = V (f j) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    by_cases last : j.val = k
    · have hj : j = Fin.last k := Fin.ext last
      simp [rowAt,Formula.natural,natTest,h,hj]
    · let s : Fin k := ⟨j.val,by omega⟩
      have hj : s.castSucc = j := Fin.ext rfl
      simpa only [rowAt,Formula.natural,natTest,h,decide_eq_true_eq,last,ite_false] using
        ((ih (fun x => f x.castSucc) s h).trans (congrArg (fun x => V (f x)) hj))

theorem rowAt_miss {k : ℕ} (f : Fin k → Formula n) (i : Formula n) (h : k ≤ V i) :
    V (rowAt k f i) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ne : V i ≠ k := by omega
    simp only [rowAt,Formula.natural,natTest,decide_eq_true_eq,ne,ite_false]
    exact ih (fun j => f j.castSucc) (by omega)

end

structure Cursor (A : Type) where
  block : A
  port : A
  slot : A

def cursor (m d : ℕ) (remaining idx : Formula n) : Cursor (Formula n) :=
  let lane := Formula.op .mod idx remaining
  let atSlot := Formula.op .div idx remaining
  let atSite := Formula.op .div atSlot (.lit d)
  ⟨.op .add (.op .mul (.op .div atSite (.lit m)) remaining) lane,
    .op .mod atSite (.lit m), .op .mod atSlot (.lit d)⟩

def nextIndex {v t m d : ℕ} (e : LiveSlot (Fin v) (BitWord t) m d) : ℕ :=
  ((e.1.1.1.val*m+e.1.1.2.val)*d+e.1.2.val)*2^t+(tagOrdinal t e.2).val

private theorem div_row (r : ℕ) {j k : ℕ} (hj : j<k) : (r*k+j)/k = r := by
  rw [Nat.mul_comm r,Nat.mul_add_div (Nat.zero_lt_of_lt hj),Nat.div_eq_of_lt hj,Nat.add_zero]

private theorem mod_row (r : ℕ) {j k : ℕ} (hj : j<k) : (r*k+j)%k = j := by
  rw [Nat.mul_comm r,Nat.mul_add_mod,Nat.mod_eq_of_lt hj]

theorem cursor_read {v t m d : ℕ} (e : LiveSlot (Fin v) (BitWord t) m d)
    (u : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ) (remaining idx : Formula n)
    (rem : remaining.natural u data mem vs = 2^t) (atIdx : idx.natural u data mem vs = nextIndex e) :
    let V := Formula.natural u data mem vs
    let p := cursor m d remaining idx
    V p.block = blockId (e.1.1.1,e.2) ∧ V p.port = e.1.1.2.val ∧ V p.slot = e.1.2.val := by
  simp [cursor,Formula.natural,natOp,rem,atIdx,nextIndex,blockId,div_row,
    Nat.mod_eq_of_lt ((tagOrdinal t) e.2).isLt,Nat.mod_eq_of_lt e.1.1.2.isLt,
    Nat.mod_eq_of_lt e.1.2.isLt]

variable {a h k : ℕ}

def externalWidth (C : Columns (Formula n)) (remaining block : Formula n) (s : Fin (mPort a)) :=
  totals ((List.finRange (mPort a)).map (fun j => demand (mPort a) C remaining block false j.val s.val))

/-- A fixed public row of the width-generation loop. The histogram is
already unpacked into the common dense table at `countsOrigin+block*stride`. -/
def generateWidth (C : Columns (Formula n)) (remaining idx countsOrigin : Formula n) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) : Formula n :=
  let p := cursor (mPort a) (1+h+pad) remaining idx
  let selected := refreshChoice C remaining p.block base
  let counts := plus countsOrigin (.op .mul p.block (.lit stride))
  rowAt (mPort a) (fun port =>
    .select .eq p.slot (.lit 0) (externalWidth C remaining p.block port)
      (rowAt h (fun s => rowAt (k+1) (fun j =>
        outputWidth (fun t => pool j t port s) counts selected.1 (bits j)) selected.2)
        (.cut p.slot (.lit 1)))) p.port

theorem nextIndex_lt {v t m d : ℕ} (e : LiveSlot (Fin v) (BitWord t) m d) :
    nextIndex e < v*m*d*2^t := by
  apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left (tagOrdinal t e.2).isLt _)
  rw [← Nat.succ_mul]
  apply Nat.mul_le_mul_right
  apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left e.1.2.isLt _)
  rw [← Nat.succ_mul]
  apply Nat.mul_le_mul_right
  apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left e.1.1.2.isLt _)
  rw [← Nat.succ_mul]
  exact Nat.mul_le_mul_right _ e.1.1.1.isLt

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
