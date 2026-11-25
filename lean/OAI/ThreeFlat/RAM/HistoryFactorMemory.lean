import OAI.ThreeFlat.RAM.HistoryInterpreter
import OAI.ThreeFlat.RAM.ExpressionRowWords

namespace OAI
/-! # Packing the compact factor and coefficient arrays in interpreter memory -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM BitLayout Contraction GeneratedContraction Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}

/-- The two compact arrays occupy contiguous words in the source area. -/
noncomputable def compactSuffix (N : BitNetwork F p) (L : Library N) (code : FieldCode F w)
    (tail : Memory w) (a : ℕ) : Word w :=
  if hm : a < 4*N.cells then
    let i : Fin N.cells := ⟨a/4, by omega⟩
    if hj : a%4 < 3 then Fin.ofNat _ (sourceAddress (N.source i ⟨a%4,hj⟩))
    else ((L.id i).val : Word w)
  else
    let z := a - 4*N.cells
    if hl : z < 8*L.count then
      code.encode (L.table ⟨z/8,by omega⟩ (bits (z%8)))
    else tail (z-8*L.count)

/-- The input image stores compact factor metadata above the evaluator footprint.
The expanded eleven-word records all start at zero. -/
noncomputable def compactInput (N : BitNetwork F p) (L : Library N) (code : FieldCode F w)
    (pin : Fin p → Bool) (tail : Memory w) : Memory w :=
  inputMemory p N.internal N.cells code pin (compactSuffix N L code tail)

theorem compactInput_stores (N : BitNetwork F p) (L : Library N) (code : FieldCode F w)
    (pin : Fin p → Bool) (tail : Memory w) : Stores N L code (footprint N)
      (footprint N+4*N.cells) (compactInput N L code pin tail) := by
  constructor
  · intro i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Nat.add_assoc, compactInput, inputMemory_source N]
    simp [compactSuffix, show 4*i.val+j.val < 4*N.cells by omega,
      show (4*i.val+j.val)/4 = i.val by omega, show (4*i.val+j.val)%4 = j.val by omega, hj]
  · intro i
    have hi := i.isLt
    rw [Nat.add_assoc, compactInput, inputMemory_source N]
    simp [compactSuffix, show 4*i.val+3 < 4*N.cells by omega,
      show (4*i.val+3)/4 = i.val by omega, show (4*i.val+3)%4 = 3 by omega]
  · intro t j
    have ht := t.isLt
    have hj := j.isLt
    rw [Nat.add_assoc, Nat.add_assoc, compactInput, inputMemory_source N]
    simp [compactSuffix, show 8*t.val+j.val < 8*L.count by omega,
      show (8*t.val+j.val)/8 = t.val by omega, show (8*t.val+j.val)%8 = j.val by omega]

/-- An explicit input using four metadata words per factor and eight per library table
has native mass equal to the weighted sum. The initial memory outside those arrays is free. -/
theorem value_compactInput (N : BitNetwork F p) (fit : Fits N w) (L : Library N)
    (space : footprint N+4*N.cells+8*L.count ≤ 2^w) (pin : Fin p → Bool)
    (tail : Memory w) (state : Word w) (extra : ℕ) :
    value (codec N fit) (interpreter p N.internal N.cells (footprint N) (footprint N+4*N.cells)
      (F := F) fit) (extra+13+5*N.internal+550*N.cells) state
        (compactInput N L (codec N fit) pin tail) = N.eval pin := by
  have hfoot : mulBase p N.internal N.cells ≤ footprint N := Nat.le_add_right _ _
  exact value_interpreter N fit L _ _ hfoot (by omega) (by omega) space _
    (compactInput_stores N L _ pin tail) pin (fun _ => false)
    (fun _ ha away => inputMemory_outside N _ pin _ ha away) state extra

end ThreeFlat.RAM.HistoryFactors

end OAI
