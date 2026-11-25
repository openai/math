import OAI.Computability.NearSquareRoot.ScheduleGeneratorPresentation
import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabetDigits
import OAI.Computability.NearSquareRoot.ScheduleGeneratorBounds

/-! # Computable representations of the finite arrays in a serialized controller -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open CommonAlphabet

variable {X R S : Type} [Primcodable X] [Primcodable R] [Primcodable S]

/-- Enumerate a variable number of computed entries in order. -/
theorem computable_rangeMap {n : X → ℕ} {f : X → ℕ → S} (hn : Computable n) (hf : Computable₂ f) :
    Computable fun x => (List.range (n x)).map (f x) := by
  have h := Computable.nat_rec hn (Computable.const ([] : List S))
    (Computable.list_concat.comp (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))).to₂
  apply h.of_eq
  intro x
  induction n x with
  | zero => rfl
  | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,ih]

/-- Apply an indexed computable operation to a variable array. -/
theorem computable_map {xs : X → List R} {f : X → R → S} {fallback : X → R}
    (hx : Computable xs) (hf : Computable₂ f) (he : Computable fallback) :
    Computable fun x => (xs x).map (f x) := by
  have entries := Computable.option_getD
    (Computable.list_getElem?.comp (hx.comp (Computable.fst (α := X) (β := ℕ))) Computable.snd)
    (he.comp Computable.fst)
  have h := computable_rangeMap (Computable.list_length.comp hx) (hf.comp Computable.fst entries).to₂
  apply h.of_eq
  intro x
  apply List.ext_getElem <;> simp
  intro i hi
  simp [hi]

namespace Presentation
variable {T U : ℕ → Type} {N : ∀ j, Numbering (T j)} {M : ∀ j, Numbering (U j)}

/-- The function table is stored as an array in argument-number order. -/
def arrow (hsize : Computable fun j => (N j).size) (b : Presentation M S) :
    Presentation (fun j => (N j).arrow (M j)) (List S) where
  view j f := (N j).all.map (fun x => b.view j (f x))
  size_eff := primrecNatPow.to_comp.comp b.size_eff hsize
  encode j xs := Numbering.encodeBase (M j).size (xs.map (b.encode j))
  encode_eff := Numbering.primrec_encodeBase.to_comp.comp (b.size_eff.comp Computable.fst)
    (computable_map Computable.snd (b.encode_eff.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
      (b.decode_eff.comp Computable.fst (Computable.const 0)))
  decode j c := (Numbering.decodeBase (M j).size c (N j).size).map (b.decode j)
  decode_eff := by
    apply computable_map (fallback := fun _ => 0) _ _ (Computable.const 0)
    · have core : Primrec (fun x : ℕ × ℕ × ℕ => Numbering.decodeBase x.1 x.2.1 x.2.2) :=
        Numbering.primrec_decodeBase Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      exact core.to_comp.comp ((b.size_eff.comp Computable.fst).pair
        (Computable.snd.pair (hsize.comp Computable.fst)))
    · exact (b.decode_eff.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  encode_view j f := by
    simpa [List.map_map,Function.comp_def,b.encode_view] using Numbering.encodeBase_arrow (N j) (M j) f
  decode_rank j f := by
    rw [Numbering.decodeBase_arrow_symm (N j) (M j) ((N j).arrow (M j) |>.equiv f)]
    simp [List.map_map,Function.comp_def,b.decode_rank]

end Presentation
end Generator

end NearSquareRoot
end Computability
end OAI
