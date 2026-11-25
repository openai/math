import OAI.ThreeFlat.RAM.TraceSuffixParameterMount
import OAI.ThreeFlat.RAM.TickParameterWords

namespace OAI
/-! # The native navigation directory and H suffix table share the same tick parameters -/

namespace ThreeFlat.RAM.TraceMountedParameters
open Computability.VPVNP.BurstRAM PhysicalPrelude Diagonal.ApproximateImage TraceSuffixOracle
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w W nt ns a : ℕ} (I : Image F w)

/-- The native directory occupies `W*len` bits. The H table follows it in the same vector. -/
def parameters (offset len : ℕ) (word : ℕ→Word W) (initial : Fin I.parameters→Bool) :=
  withTable I (offset+W*len) (TickParameterWords.mount offset len word initial)

theorem outside (offset len : ℕ) (word : ℕ→Word W) (initial : Fin I.parameters→Bool)
    (i : Fin I.parameters) (h : i.val<offset ∨ offset+W*len+w*FixedTraceImage.count I.G≤ i.val) :
    parameters I offset len word initial i = initial i := by
  rw [parameters,withTable_outside _ _ _ _ (by omega),TickParameterWords.outside _ _ _ _ _ (by omega)]

theorem nav_coordinate (offset len : ℕ) (word : ℕ→Word W) (initial : Fin I.parameters→Bool)
    (fit : offset+W*len≤I.parameters) (i j : ℕ) (hi : i<len) (hj : j<W) :
    let index := offset+W*i+j
    let inside : index<I.parameters := by
      have h := Nat.mul_le_mul_left W hi; rw [Nat.mul_succ] at h; dsimp [index]; omega
    parameters I offset len word initial ⟨index,inside⟩=(word i).val.testBit (W-1-j) := by
  intro index inside
  have h := Nat.mul_le_mul_left W hi
  rw [Nat.mul_succ] at h
  rw [parameters,withTable_outside _ _ _ _ (Or.inl (by change index<offset+W*len; dsimp [index]; omega))]
  exact TickParameterWords.coordinate offset len i j word initial fit hi hj

theorem physical (D : Fin I.advice→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool)
    (initial : Fin I.parameters→Bool) (oa na oc nc : Fin a→Bool)
    (offset len codeBase textStart textLength : ℕ) (word : ℕ→Word W) (hW : 0<W)
    (fit : offset+W*len+w*FixedTraceImage.count I.G≤I.parameters) :
    let par := parameters I offset len word initial
    let pins := fields D team step par oa na oc nc
    let base := 2+I.advice+nt+ns
    Mounted I ⟨2,base,base+(offset+W*len),codeBase,textStart,textLength⟩
      (fun j => (TickMountedPins.memory (w:=W) pins j).val) D par ∧
      ∀ i, i<len → ∀ j, j<W →
        TickMountedPins.memory (w:=W) pins (base+offset+W*i+j) =
          (((word i).val.testBit (W-1-j)).toNat : Word W) := by
  intro par pins base
  refine ⟨table_mount I D team step (TickParameterWords.mount offset len word initial)
    oa na oc nc (offset+W*len) codeBase textStart textLength hW fit,?_⟩
  intro i hi j hj
  have h := Nat.mul_le_mul_left W hi
  rw [Nat.mul_succ] at h
  let addr : Fin I.parameters := ⟨offset+W*i+j,by omega⟩
  have atAddr : base+offset+W*i+j = 2+I.advice+nt+ns+addr.val := by dsimp [addr,base]; omega
  rw [atAddr,TickParameterWords.memory_at]
  have bit : par addr = (word i).val.testBit (W-1-j) :=
    nav_coordinate I offset len word initial (by omega) i j hi hj
  rw [bit]
  rfl


end ThreeFlat.RAM.TraceMountedParameters

end OAI
