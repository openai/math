import OAI.ThreeFlat.RAM.TickReadFields
import OAI.ThreeFlat.RAM.ProgramBits
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # A shared physical pin segment for the native tick and its contraction -/

namespace ThreeFlat.RAM.TickMountedPins

open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Diagonal.ApproximateImage

variable {w p d nt ns np a : ℕ}

/-- Header bit one is the true literal. The physical tick pins follow these
two cells in exactly the order consumed by the final slot's trivalent network. -/
def raw (pins : Fin p → Bool) (j : ℕ) : Bool :=
  if j = 1 then true else if h : 2 ≤ j ∧ j-2 < p then pins ⟨j-2,h.2⟩ else false

def word (pins : Fin p → Bool) (j : ℕ) : Word w := BitLayout.bitWord w (raw pins j)

def memory (pins : Fin p → Bool) : Memory w := initialMemory (2+p) (word pins)

theorem raw_at (pins : Fin p → Bool) (i : Fin p) : raw pins (2+i.val) = pins i := by
  simp [raw,show 2+i.val ≠ 1 by omega,i.isLt]

@[simp] theorem memory_at (pins : Fin p → Bool) (i : Fin p) :
    memory (w:=w) pins (2+i.val) = BitLayout.bitWord w (pins i) := by
  simp [memory,initialMemory,word,raw_at,i.isLt]

theorem memory_constants (pins : Fin p → Bool) :
    memory (w:=w) pins 0 = 0 ∧ memory (w:=w) pins 1 = 1 := by
  simp [memory,initialMemory,word,raw,BitLayout.bitWord,show 1 < 2+p by omega]
  exact Fin.ext rfl

theorem memory_hidden (pins : Fin p → Bool) (i : ℕ) :
    memory (w:=w) pins (BitLayout.hiddenBase p+i) = 0 := by
  simp [memory,initialMemory,BitLayout.hiddenBase]

theorem advice_agrees {q : ℕ} (D : Fin q → Bool) (base : ℕ) (m : Memory w)
    (stored : ∀ i : Fin q, m (base+i.val) = if D i then 1 else 0) :
    memoryWithAdvice base D m = m := by
  funext j
  unfold memoryWithAdvice
  split
  next h =>
    let i : Fin q := ⟨j-base,h.2⟩
    have q := stored i
    have addr : base+i.val = j := by dsimp [i]; omega
    rw [addr] at q
    exact q.symm
  next => rfl

/-- The installed program bits are exactly the prefix of the physical pin
vector. Reloading the advice tape leaves this mounted input unchanged. -/
theorem mounted_advice (D : Fin d → Bool) (team : Fin nt → Bool) (step : Fin ns → Bool)
    (params : Fin np → Bool) (oa na oc nc : Fin a → Bool) :
    let pins := fields D team step params oa na oc nc
    memoryWithAdvice 2 D (memory (w:=w) pins) = memory pins := by
  apply advice_agrees
  intro i
  let j : Fin (pinCount d nt ns np a) := i.castAdd _
  have hj : fields D team step params oa na oc nc j = D i := by simp [fields,j]
  change memory (w:=w) (fields D team step params oa na oc nc) (2+j.val) = _
  rw [memory_at,hj]
  cases D i <;> rfl

theorem has_fields (D : Fin d → Bool) (params : Fin np → Bool) (oa na oc nc : Fin a → Bool)
    (team step : ℕ) :
    let pins := fields D (digits team nt) (digits step ns) params oa na oc nc
    TickReadFields.HasFields (w:=w) (nt:=nt) (ns:=ns) D params oa na oc nc team step (word pins) 2 := by
  intro pins j
  simp only [word,raw_at,BitLayout.bitWord,pins]

end ThreeFlat.RAM.TickMountedPins

end OAI
