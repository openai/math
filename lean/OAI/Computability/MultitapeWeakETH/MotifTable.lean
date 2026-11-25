import OAI.Computability.MultitapeWeakETH.MotifSelectors

/-! # Finite dependent tables for a fixed motif -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code StackInterpreter
open scoped Classical
noncomputable section

variable {X I Q : Type} [Codec X]

/-- A conjunction over a fixed finite set of ports compiles even when the operand
strings and the offsets tested at each port depend on the input. -/
theorem all_poly [Fintype I] (test : I → X → Bool) (p : ∀ i, Poly (test i)) :
    Poly (fun x => decide (∀ i, test i x = true)) := by
  have list (is : List I) : Poly (fun x => decide (∀ i ∈ is, test i x = true)) := by
    induction is with
    | nil => simpa only [List.not_mem_nil,Bool.false_eq_true,false_implies,implies_true,decide_true] using
        (Code.Poly.const (X:=X) true)
    | cons i is ih =>
      convert Poly.choose (p i) ih (Code.Poly.const false) using 1
      funext x
      cases eq : test i x <;> simp [eq]
  simpa using list Finset.univ.toList

/-- To produce an index in a fixed finite parameter table it suffices to test
equality against each of its entries in polynomial time. -/
theorem index_poly [Fintype Q] [Nonempty Q] (index : X → Q)
    (test : ∀ j, Poly (fun x => decide (index x = j))) : Poly (fun x => Label.mk (index x)) := by
  let none : Q := Classical.arbitrary Q
  have scan (js : List Q) : Poly (fun x => Label.mk (if index x ∈ js then index x else none)) := by
    induction js with
    | nil => simpa using (Code.Poly.const (X:=X) (Label.mk none))
    | cons j js ih =>
      convert Poly.choose (test j) (Code.Poly.const (Label.mk j)) ih using 1
      funext x
      by_cases eq : index x=j <;> simp [eq]
  simpa using scan Finset.univ.toList

end
end OAI.Computability.MultitapeWeakETH.MotifFields
