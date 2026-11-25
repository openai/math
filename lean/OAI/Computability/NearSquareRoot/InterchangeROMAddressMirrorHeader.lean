import OAI.Computability.NearSquareRoot.InterchangeROMAddress

/-! # Projecting a native layout header onto a single field -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic

abbrev Shape3 := List Tally × List Tally × List Tally
abbrev Location := Bool × Tally × Tally × Tally × Tally

/-- Side, radix, number of fields per side, and numbers to the left and right. -/
def location {J : Type} {n : ℕ} (ord : J ≃ Fin n) (b : ℕ) (s : Spot J) : Location :=
  (s.1,tally b,tally n,tally (ord s.2).val,tally (n-(ord s.2).val-1))

private def word (v : Location × Header) := v.2.1.map (fun _ => v.1.2.1)

private theorem word_poly : Poly word :=
  (show Poly (fun v : Location × Header => (v.2.1,v.1.2.1)) from by fun_prop).compose
    Packed.chamber

private theorem repeat_poly {X : Type} [Codec X] {u : X → Tally} {v : X → List Tally}
    (a : Poly u) (b : Poly v) : Poly (fun i => copies (u i,v i)) :=
  (a.pair b).compose copies_poly

/-- The chosen field is always contiguous in the resulting physical layout. -/
def projection (u : Location × Header) : Shape3 :=
  let whole := copies (u.1.2.2.1,word u)
  let left := copies (u.1.2.2.2.1,word u)
  let right := copies (u.1.2.2.2.2,word u)
  let P := u.2.2.1
  let G := u.2.2.2.1
  let S := u.2.2.2.2
  bif u.1.1 then (P ++ (whole ++ (G ++ left)),word u,right ++ S)
  else (P ++ left,word u,right ++ (G ++ (whole ++ S)))

attribute [local fun_prop] repeat_poly word_poly in
theorem projection_poly : Poly projection := by
  unfold projection
  fun_prop

theorem projection_correct {J : Type} {n : ℕ} (ord : J ≃ Fin n) (b f : ℕ)
    (p g s : Tape) (slot : Spot J) :
    projection (location ord b slot,header f p g s) =
      (shape (preamble ord p g (field b f) slot),shape (field b f),
        shape (appendix ord g s (field b f) slot)) := by
  obtain ⟨a,j⟩ := slot
  cases a <;>
    simp only [projection,location,header,word,shape_field,copy_shape,
      preamble_false,preamble_true,appendix_false,appendix_true,leftF,rightF,ranking] <;>
    simp [shape]

end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
