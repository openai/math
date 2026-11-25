import OAI.Computability.NearSquareRoot.KernelEffectiveMixBankPacket

/-! # Live storage and timing for a generated bank mix

The local clock bounds growth on every parked register and every return stack.
On well-formed row packets, the charged input size includes the control header,
the address and width rulers, the marked bit words, and the row delimiters.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveMixBank

open IntegerMultiplication Code Space KernelPassMix MixBankLayout

variable {H : Type} [Codec H]

theorem Sound.bounded {cmd : Cmd} {key : H → Rulers} {i o : ℕ} {f : RowFunction}
    (h : Sound cmd key i o f) : ∃ C, ∀ z env r base, (∀ j, (letters r j).length ≤ base) →
    BoundedFits env cmd (pile 0 (send z) r) (pile 0 (send (answer key i o f z)) r)
      (C*(expense key z+1)) (base + C*(expense key z+1)) (C*(expense key z+1)) := by
  obtain ⟨C,h⟩ := h
  refine ⟨C+1,fun z env r base hr => ?_⟩
  have hz : size z ≤ expense key z := Nat.le_add_right _ _
  have Ht := h z env r
  have extend := BoundedFits.of_fits Ht (cap := base+(C+1)*(expense key z+1))
    (depth := (C+1)*(expense key z+1)) (fun j => ?_) (by rw [Nat.succ_mul]; omega)
  · exact extend.mono (Nat.mul_le_mul_right _ (by omega)) le_rfl le_rfl
  · by_cases hj : j=0
    · subst j
      rw [letters_here,List.length_append,Tree.spell_length,Nat.succ_mul]
      have rf := hr 0
      change _ + _ ≤ _ at *
      change (send z).count ≤ _ at hz
      omega
    · rw [pile_far _ _ (Ne.symm hj),Nat.succ_mul]
      have rf := hr j
      omega

theorem expense_marked {α : Type} {i : ℕ} (key : H → Rulers) (header : H)
    (l : List α) (w : ℕ) (x : α → Fin i → Dusk.Grain w)
    (hk : key header = (tally l.length,tally (w+1))) :
    expense key (header,markedBank l x) ≤ size header + (8*i+6)*((l.length+1)*(w+1)) := by
  have sz := size_bank_le l (fun a j => Dusk.mark (x a j)) (7*(w+1))
    (fun a _ j => by rw [Dusk.volume]; omega)
  simp only [expense,size_prod,hk,tally_length,size_tally,markedBank]
  ring_nf at sz ⊢
  omega

end KernelEffectiveMixBank

end NearSquareRoot
end Computability
end OAI
