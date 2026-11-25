import OAI.Computability.NearSquareRoot.SynchronizedPermutationBatchHeader
import OAI.Computability.NearSquareRoot.PermutationLayoutConjugate

/-! # Reading the switch bit from the actual relocated physical prefix -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Adic Controlled Controlled.PermutationLayout

variable {p b G low c d : ℕ}

private theorem listBit {n : ℕ} (v : Fin n → Bool) (i : Fin n) :
    Benes.prefixBit (List.ofFn v,tally i.val) = v i := by
  have h : (List.ofFn v)[i.val]?.getD false = v i := by simp
  rw [← List.head?_drop] at h
  unfold Benes.prefixBit
  rw [tally_length]
  cases eq : (List.ofFn v).drop i.val <;> simpa only [eq,List.head?,List.headD,Option.getD] using h

private theorem relative_read (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
    (π : Equiv.Perm (Fin (maskWidth p b G low))) (w : Block 2 (maskWidth p b G low))
    (i : Fin c) :
    Benes.prefixBit (List.ofFn (Controlled.prefixBit (prefixWord (PositionProgram.permuteNative π w))),
      tally (offset π G low b (π (controlPos fit i)))) =
        Controlled.prefixBit w (π (controlPos fit i)) := by
  have e : offset π G low b (π (controlPos fit i)) = (prefixIndex pos fit i).val := by
    simp [PermutationLayout.offset,controlPos,controlOffset,prefixIndex]
  rw [e,listBit,prefix_source]

/-- A whole local switch query can use a dummy bit at its target. Every other
input to the switch is read from its assigned location in the prefix. -/
theorem relocated_query (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ maskWidth p b G low)
    (π : Equiv.Perm (Fin (maskWidth p b G low))) (port : Fin d → Fin (maskWidth p b G low))
    {f : Equiv.Perm (Word d)} {t : RawTable} (rep : RawRepresents f t)
    (side : Bool) (j : Fin d)
    (cover : ∀ i : Fin d, i ≠ j → ∃ a : Fin c, π (controlPos fit a) = port i)
    (w : Block 2 (maskWidth p b G low)) :
    let codes := List.ofFn (Controlled.prefixBit (prefixWord (PositionProgram.permuteNative π w)))
    let read := prefixWordAt (fun i => offset π G low b (port i)) codes
    let v := fun i => Controlled.prefixBit w (port i)
    let flag := rawSetting t j.val (List.ofFn v)
    queryBit (query d t side j.val read) = (if side then flag.2 else flag.1) := by
  intro codes read v flag
  have eq : read = Function.update v j (read j) := by
    funext i
    by_cases he : i=j
    · subst i; simp
    obtain ⟨a,ha⟩ := cover i he
    rw [Function.update_of_ne he]
    change Benes.prefixBit (_,tally (offset π G low b (port i))) = Controlled.prefixBit w (port i)
    rw [← ha]
    exact relative_read pos fit π w a
  change switchBit (generateTables (tally d,t),side,tally j.val,List.ofFn read) = _
  rw [switchBit_generated rep,ite_eq_left_of_eq_true _ _ (eq_true j.isLt),eq,rawSetting_update]

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
