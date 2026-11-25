import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.Lattice.ProjectionTable

/-! Dense finite rational packets for the residual projector, including zero dimension. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Projector

open Matrix

abbrev Row := List ℚ
abbrev Table := List Row
abbrev Arg := ℕ × IntMatrix
abbrev Work := IntMatrix × Table

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

def rowCode := listCode ratCode
def tableCode := listCode rowCode
def argCode := prodCode unaryCode intMatrixCode
def workCode := prodCode intMatrixCode tableCode

def pack {p : ℕ} (A : Matrix (Fin p) (Fin p) ℚ) : Table := List.ofFn fun i => List.ofFn (A i)

def cell (A : Table) (i j : ℕ) : ℚ := readAt 0 (readAt [] A i) j

def tab (p : ℕ) (f : ℕ → ℕ → ℚ) : Table := (List.range p).map fun i => (List.range p).map (f i)

def dot (a b : Row) : ℚ := ((List.range a.length).map fun k => readAt 0 a k * readAt 0 b k).sum

def act (A : Table) (a : Row) : Row :=
  (List.range A.length).map fun i => dot (readAt [] A i) a

def trans (A : Table) : Table := tab A.length fun i j => cell A j i

def ident (p : ℕ) : Table := tab p fun i j => if i = j then 1 else 0

def image (P : Table) (z : List ℤ) : Row := act P (z.map (fun x : ℤ => (x : ℚ)))

def corrected (P : Table) (u r : Row) (d : ℚ) : Table :=
  tab P.length fun i j => cell P i j - readAt 0 u i / d * readAt 0 r j

def step (P : Table) (z : List ℤ) : Table :=
  let u := image P z
  let d := dot u u
  if d = 0 then P else corrected P u (act (trans P) u) d

def start (x : Arg) : Work := (x.2.reverse,ident x.1)

def next : Work → Work
  | ([],P) => ([],P)
  | (z :: zs,P) => (zs,step P z)

@[simp] theorem pack_length {p : ℕ} (A : Matrix (Fin p) (Fin p) ℚ) : (pack A).length = p := by
  simp [pack]

@[simp] theorem pack_cell {p : ℕ} (A : Matrix (Fin p) (Fin p) ℚ) (i j : Fin p) :
    cell (pack A) i.val j.val = A i j := by simp [cell,pack]

private theorem mapRange_eq_ofFn {α : Type} {n : ℕ} (f : ℕ → α) (v : Fin n → α)
    (h : ∀ i, f i.val = v i) : (List.range n).map f = List.ofFn v := by
  apply List.ext_getElem
  · simp
  · intro z hz _
    have hz' : z < n := by simpa using hz
    simpa using h ⟨z,hz'⟩

private theorem tab_pack {p : ℕ} (f : ℕ → ℕ → ℚ) (A : Matrix (Fin p) (Fin p) ℚ)
    (h : ∀ i j, f i.val j.val = A i j) : tab p f = pack A := by
  apply mapRange_eq_ofFn
  intro i
  exact mapRange_eq_ofFn _ _ (h i)

theorem ident_pack (p : ℕ) : ident p = pack (1 : Matrix (Fin p) (Fin p) ℚ) := by
  apply tab_pack
  intro i j
  simp [Matrix.one_apply, Fin.ext_iff]

private theorem fin_sum_eq_range (n : ℕ) (f : ℕ → ℚ) :
    (∑ i : Fin n, f i.val) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Fin.sum_univ_castSucc, List.range_succ]; simp [ih]

theorem dot_pack {p : ℕ} (a b : Fin p → ℚ) : dot (List.ofFn a) (List.ofFn b) = a ⬝ᵥ b := by
  unfold dot dotProduct
  rw [List.length_ofFn, ← fin_sum_eq_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [readAt_ofFn,readAt_ofFn]

theorem act_pack {p : ℕ} (A : Matrix (Fin p) (Fin p) ℚ) (x : Fin p → ℚ) :
    act (pack A) (List.ofFn x) = List.ofFn (A *ᵥ x) := by
  unfold act
  rw [pack_length]
  apply mapRange_eq_ofFn
  intro i
  rw [pack,readAt_ofFn,dot_pack]
  rfl

theorem trans_pack {p : ℕ} (A : Matrix (Fin p) (Fin p) ℚ) : trans (pack A) = pack A.transpose := by
  unfold trans
  rw [pack_length]
  apply tab_pack
  intro i j
  exact pack_cell _ _ _

theorem step_pack {p : ℕ} (A : Matrix (Fin p) (Fin p) ℚ) (z : Fin p → ℤ) :
    step (pack A) (List.ofFn z) =
      pack (rationalLineComplement (A *ᵥ fun i => (z i : ℚ)) * A) := by
  let u := A *ᵥ fun i => (z i : ℚ)
  have hu : image (pack A) (List.ofFn z) = List.ofFn u := by
    unfold image
    rw [List.map_ofFn]
    exact act_pack A _
  unfold step
  dsimp only
  rw [hu,dot_pack,trans_pack,act_pack]
  by_cases h : u ⬝ᵥ u = 0
  · rw [ite_eq_left h]
    apply congrArg pack
    ext i j
    rw [rationalLineComplement_mul_entry]
    simp [h,u]
  · rw [ite_eq_right h]
    unfold corrected
    rw [pack_length]
    apply tab_pack
    intro i j
    rw [pack_cell,readAt_ofFn,readAt_ofFn,rationalLineComplement_mul_entry]
    change A i j - u i / (u ⬝ᵥ u) * (A.transpose *ᵥ u) j =
      A i j - u i / (u ⬝ᵥ u) * (u ᵥ* A) j
    rw [Matrix.mulVec_transpose]

end Projector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
