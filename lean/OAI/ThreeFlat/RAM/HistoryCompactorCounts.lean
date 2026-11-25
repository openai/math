import OAI.ThreeFlat.RAM.StableCompactROMNative
import OAI.ThreeFlat.RAM.HistoryUniversalArchive

namespace OAI
/-! # Exact compacted leaf sizes from one constant-size header per exponent -/

namespace ThreeFlat.RAM.HistoryCompactorCounts

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Routing.StableCompactNative Routing.StableCompaction
open scoped Fin.CommRing Classical
noncomputable section

variable (F : Type*) [Zero F] [One F] {w k B : ℕ}

def size (B : ℕ) := 2*(B+1)

def base (B maxArity n start : ℕ) := start+StableCompactROMNative.size B+HistoryStaticArchive.size n maxArity

def words (m : Fin (B+1)) (j : Fin 2) : ℕ := if j=0 then (template F m).cells else registerCount F m

def data (B : ℕ) (i : Fin (size B)) : Word w :=
  let m : Fin (B+1) := ⟨i.val/2,by have bound := i.isLt; unfold size at bound; omega⟩
  let lane : Fin 2 := ⟨i.val%2,Nat.mod_lt _ (by decide)⟩
  (words F m lane : Word w)

theorem data_at (m : Fin (B+1)) (j : Fin 2) :
    let x : Fin (size B) := ⟨2*m.val+j.val,by have := m.isLt; have := j.isLt; unfold size; omega⟩
    data (w:=w) F B x = (words F m j : Word w) := by
  dsimp only [data]
  have hj := j.isLt
  have a : (⟨(2*m.val+j.val)/2,by have := m.isLt; omega⟩ : Fin (B+1))=m := Fin.ext (by change (2*m.val+j.val)/2=m.val; omega)
  have b : (⟨(2*m.val+j.val)%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)=j := Fin.ext (by change (2*m.val+j.val)%2=j.val; omega)
  rw [a,b]

/-- Exact dimensions of the cropped semantic network, including when all
three variable-length pin banks have length zero. -/
theorem shape (m : Fin (B+1)) (n : ℕ) :
    (restrictRows (network F m) n).cells = words F m 0*2^m.val ∧
    (restrictRows (network F m) n).internal = words F m 1*2^m.val := by
  constructor <;> rfl

def program (w k : ℕ) : Term w k 4 :=
  let index := Term.binary .add (Term.binary .mul (.literal 2) (.result 1)) (.result 2)
  Term.binary .mul (Term.binary .add (.result 0) index).load (.result 3)

theorem cost (w k : ℕ) : (program w k).binds=6 := by
  simp [program,Term.binary,Term.load,Term.literal,Term.binds]

/-- The four input words are the shape-bank base, exponent, column (row or
hidden count), and `2^m`. The execution returns the true unstretched size. -/
theorem eval (m : Fin (B+1)) (j : Fin 2) (start : ℕ) (pub : Fin k → Word w) (mem : Memory w)
    (stored : ∀ i : Fin (size B), mem (start+i.val) = data F B i) (room : start+size B ≤ 2^w) :
    (program w k).eval pub mem ![(start : Word w),(m.val : Word w),(j.val : Word w),((2^m.val : ℕ) : Word w)] =
      ((words F m j*2^m.val : ℕ) : Word w) := by
  let x : Fin (size B) := ⟨2*m.val+j.val,by have := m.isLt; have := j.isLt; unfold size; omega⟩
  have bound : start+(2*m.val+j.val)<2^w := by have := x.isLt; dsimp only [x] at this; omega
  have read : mem (start+(2*m.val+j.val))=(words F m j : Word w) := (stored x).trans (data_at F m j)
  simp only [program,Term.eval_load,Term.eval_binary,Term.eval_literal,Term.eval,BinaryOp.eval]
  change mem ((start:Word w)+(2*(m.val:Word w)+(j.val:Word w))).val * _ = _
  have address : (start:Word w)+(2*(m.val:Word w)+(j.val:Word w))=((start+(2*m.val+j.val):ℕ):Word w) := by push_cast; rfl
  rw [address,Fin.val_cast_of_lt bound,read,Nat.cast_mul]; rfl

end
end ThreeFlat.RAM.HistoryCompactorCounts

end OAI
