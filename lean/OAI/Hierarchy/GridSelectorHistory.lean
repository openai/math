import OAI.Hierarchy.GridSelector
import OAI.Hierarchy.GridSelectorPadding

namespace OAI
/-! # Identifying the admitted short history with the selected full grid summand -/

namespace Hierarchy.GridSelector
open ThreeFlat.Diagonal.HistoryContraction
open scoped Classical
noncomputable section
variable {F : Type*} [CommSemiring F] {S : Shape} (P : Plan F S) (C : P.Codes)
  (bits : P.History→ℕ) (cap : ℕ)

/-- A legal simulation tag and the complete physical encoder determine both
the history recovered from its shorter prefix and its zero-padded wire bits. -/
theorem selected_history (s : Fin (cap+1)→Bool) (cut : ℕ)
    (fits : ∀ h,(P.write C h).length≤cut) (v : Trace P bits)
    (full : decode P C bits cap s=some (some v)) :
    let raw:=List.ofFn (Fin.tail s)
    s 0=true ∧ raw=body P C bits cap v ∧
    P.read C (raw.take cut) = some (v.1,(raw.take cut).drop (P.write C v.1).length) := by
  intro raw
  cases flag : s 0 with
  | false =>
    by_cases zero : ∀ i,Fin.tail s i=false <;> simp [decode,flag,zero] at full
  | true =>
    have read : GridSelector.read P C bits cap raw=some v := by
      simpa [decode,flag,raw] using full
    have bodyEq := (body_read P C bits cap raw v read).symm
    refine ⟨rfl,bodyEq,?_⟩
    let tail:=List.ofFn v.2 ++ List.replicate (cap-((P.write C v.1).length+bits v.1)) false
    have decompose : raw.take cut=P.write C v.1++tail.take (cut-(P.write C v.1).length) := by
      rw [bodyEq]
      unfold body
      rw [List.append_assoc,List.take_append,List.take_of_length_le (fits v.1)]
    rw [decompose,P.read_write,List.drop_left]

/-- An independently recovered native history from the short register has
exactly the terminal sites and coordinates of the full decoded grid setting. -/
theorem recovered_eq (s : Fin (cap+1)→Bool) (cut : ℕ)
    (fits : ∀ h,(P.write C h).length≤cut) (v : Trace P bits)
    (full : decode P C bits cap s=some (some v)) (h : P.History) (tail : List Bool)
    (parsed : P.read C ((List.ofFn (Fin.tail s)).take cut)=some (h,tail)) : h=v.1 := by
  have eqn := (selected_history P C bits cap s cut fits v full).2.2
  rw [parsed] at eqn
  exact congrArg Prod.fst (Option.some.inj eqn)

end
end Hierarchy.GridSelector

end OAI
