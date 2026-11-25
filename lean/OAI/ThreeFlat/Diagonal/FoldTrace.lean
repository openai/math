import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Exposing the independent inputs of a folded evaluator's native trace -/

namespace ThreeFlat.Diagonal.FoldTrace
open RAM RAM.BitLayout
variable {F : Type*} {n S k : ℕ}

/-- The native evaluator starts with the constant words zero and one, the
folded entry in row-major order, and a fixed public suffix. -/
def header (x : Fin k → Bool) (suffix : ℕ → Bool) (a : ℕ) : Bool :=
  if low : a<2 then decide (a=1) else if h : a<2+k then x ⟨a-2,by omega⟩
  else suffix (a-(2+k))

def mask (k : ℕ) (suffix : ℕ → Bool) : BitSource n S → BitSource n k
  | .hidden i => .hidden i
  | .constant b => .constant b
  | .pin i => if low : i.val<2 then .constant (decide (i.val=1))
    else if h : i.val<2+k then .pin ⟨i.val-2,by omega⟩
    else .constant (suffix (i.val-(2+k)))

def network (N : BitNetwork F S) (k : ℕ) (suffix : ℕ → Bool) : BitNetwork F k where
  internal := N.internal
  cells := N.cells
  source i j := mask k suffix (N.source i j)
  table := N.table

theorem read_mask (s : BitSource n S) (suffix : ℕ → Bool) (x : Fin k → Bool) (h : Fin n → Bool) :
    (mask k suffix s).read h x=s.read h (fun i=>header x suffix i.val) := by
  cases s with
  | constant b => rfl
  | hidden j => rfl
  | pin i =>
    by_cases lo : i.val<2 <;> by_cases hi : i.val<2+k <;> simp [header,mask,BitSource.read,lo,hi]

theorem eval [CommSemiring F] (N : BitNetwork F S) (suffix : ℕ → Bool) (x : Fin k → Bool) :
    (network N k suffix).eval x=N.eval (fun i=>header x suffix i.val) := by
  unfold BitNetwork.eval BitNetwork.weight
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (N.table i)
  funext j
  exact read_mask (N.source i j) suffix x h

/-- Numeric source-word transformation in an eleven-word trivalent record. -/
def remap (S k : ℕ) (suffix : ℕ → Bool) (x : ℕ) :=
  if x<2 then x else if x<4+k then x-2 else if x<2+S then
    (suffix (x-(4+k))).toNat else x-(S-k)

theorem remap_address (fit : 2+k≤S) (suffix : ℕ → Bool) (s : BitSource n S) :
    remap S k suffix (sourceAddress s)=sourceAddress (mask k suffix s) := by
  cases s with
  | hidden j =>
    have a : ¬2+S+j.val<2 := by omega
    have b : ¬2+S+j.val<4+k := by omega
    have c : ¬2+S+j.val<2+S := by omega
    change remap S k suffix (2+S+j.val)=2+k+j.val
    unfold remap
    rw [ite_eq_right a,ite_eq_right b,ite_eq_right c]
    omega
  | constant b => cases b <;> rfl
  | pin i =>
    have cap := i.isLt
    by_cases lo : i.val<2
    · have a : ¬2+i.val<2 := by omega
      have b : 2+i.val<4+k := by omega
      simp only [sourceAddress,mask,dite_eq_left lo,remap]
      rcases (by omega : i.val=0 ∨ i.val=1) with h | h <;> simp [h] <;> omega
    · by_cases hi : i.val<2+k
      · have a : ¬2+i.val<2 := by omega
        have b : 2+i.val<4+k := by omega
        simp [sourceAddress,mask,remap,lo,hi,a,b]
       ; omega
      · have a : ¬2+i.val<2 := by omega
        have b : ¬2+i.val<4+k := by omega
        have c : 2+i.val<2+S := by omega
        have e : 2+i.val-(4+k)=i.val-(2+k) := by omega
        simp [sourceAddress,mask,remap,lo,hi,a,b,c,e]

end ThreeFlat.Diagonal.FoldTrace

end OAI
