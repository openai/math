import OAI.ThreeFlat.RAM.TraceMountedParameters
import OAI.ThreeFlat.RAM.EffectSeedProcedure

namespace OAI
/-! # Packing the trace seed directly from the native navigation parameter vector -/

namespace ThreeFlat.RAM.TraceMountedParameters
open Computability.VPVNP.BurstRAM PhysicalPrelude Diagonal.ApproximateImage TraceSuffixOracle EffectStream
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [Field F] {w W nt ns a : ℕ} (I : Image F w)

/-- The immutable public word vector is the native navigation prefix and all address/value
pairs for the three locally accessed trace banks. Its H-table bits follow immediately. -/
def seedWords (len tmp : ℕ) (word : ℕ→Word W) (es : List (Record W)) (i : ℕ) :=
  if i<len then word i else packedWord tmp es (tmp+(i-len))

theorem physical_seed (D : Fin I.advice→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool)
    (initial : Fin I.parameters→Bool) (oa na oc nc : Fin a→Bool)
    (offset len tmp codeBase textStart textLength : ℕ) (word : ℕ→Word W)
    (es : List (Record W)) (hW : 0<W)
    (fit : offset+W*(len+2*es.length)+w*FixedTraceImage.count I.G≤I.parameters) :
    let n := len+2*es.length
    let par := parameters I offset n (seedWords len tmp word es) initial
    let pins := fields D team step par oa na oc nc
    let base := 2+I.advice+nt+ns
    let m := TickMountedPins.memory (w:=W) pins
    Mounted I ⟨2,base,base+(offset+W*n),codeBase,textStart,textLength⟩ (fun j => (m j).val) D par ∧
      (∀ i, i<len → ∀ j, j<W → m (base+offset+W*i+j) =
        (((word i).val.testBit (W-1-j)).toNat : Word W)) ∧
      EffectSeed.Input (base+offset+W*len) tmp es m := by
  intro n par pins base m
  obtain ⟨mounted,allWords⟩ := physical I D team step initial oa na oc nc
    offset n codeBase textStart textLength (seedWords len tmp word es) hW fit
  refine ⟨mounted,?_,?_⟩
  · intro i hi j hj
    simpa [seedWords,hi] using allWords i (show i<n by dsimp [n]; omega) j hj
  · intro i hi j hj
    have value :=  allWords (len+i) (show len+i<n by dsimp [n]; omega) j hj
    change m _ = _ at value
    simpa only [seedWords,show ¬len+i<len by omega,ite_false,Nat.add_sub_cancel_left,
      base, Nat.mul_add, Nat.add_assoc] using value


end ThreeFlat.RAM.TraceMountedParameters

end OAI
