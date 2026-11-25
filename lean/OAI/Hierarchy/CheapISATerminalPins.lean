import OAI.Hierarchy.CheapISAPinImage
import OAI.Hierarchy.DescentTerminalNativeContraction

namespace OAI
/-! # The fixed translated machine provides the same observed terminal factor pins -/
namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM ThreeFlat.Diagonal
open scoped Fin.CommRing
open DescentTerminalRAM TaggedShorterControlHistory
noncomputable section
variable {A : Type} {w u rows word bins W arity dest : ℕ} {sizes : Fin arity→ℕ}

private theorem observation_at {n t : ℕ} (words : Fin n → Word t) (i : Fin n) (j : Fin t) :
    observationBits n t words (i,j) = TraceWords.bits (words i) j := rfl

theorem resultPins_translated (p r : ℕ) (addr : Fin u→ Word w)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→
      (Catalyst.Port dest sizes⊕Choice A rows word)⊕Observed u w)
    (x : Catalyst.Port dest sizes→ Bool) (b : Choice A rows word→ Bool) (old : Memory w) (new : Memory (width w))
    (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1)) (read : ∀a : Word w,new (dataAddr p r a)=wide (old a.val)) :
    resultPins (translatedAddr p r addr) (translatedPin dataPin) x b new=resultPins addr dataPin x b old := by
  funext a
  cases h : dataPin a with
  | inl leaf=>simp [resultPins,translatedPin,h]
  | inr obs=>
    obtain ⟨i,j⟩:=obs
    simpa only [resultPins,translatedPin,Function.comp_apply,h,Sum.map_inr,Sum.elim_inr,observation_at] using
      translated_bit r addr old new hp hr read i j

end
end Hierarchy.CheapISA

end OAI
