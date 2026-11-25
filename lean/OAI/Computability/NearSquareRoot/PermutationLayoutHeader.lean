import OAI.Computability.NearSquareRoot.PermutationLayoutSlots
import OAI.Computability.NearSquareRoot.CRTTableInputRows

/-! # Polynomial generation of the prescribed sparse position pairs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PermutationLayout
open IntegerMultiplication IntegerMultiplication.Code

abbrev Assignments := List (Tally × Tally)
abbrev Inputs := (Tally × Tally) × List Tally × List Tally

@[local fun_prop] private theorem ruler_poly {X : Type} [Codec X] : Poly (@ruler X) :=
  (Easy.ruler Easy.identity).poly

private def times (p : Tally × Tally) : Tally := (p.1.map (fun _ => p.2)).flatten

@[fun_prop] private theorem times_poly : Poly times :=
  (Packed.chamber (X := Tally)).compose Easy.flatten.poly

@[simp] private theorem times_length (x y : Tally) : (times (x,y)).length = x.length*y.length := by
  simp [times,List.map_const',List.length_flatten]

private def advanceBy (z : (Tally × Tally) × Tally) : Tally :=
  z.1.1 ++ times (z.2,z.1.2)

@[fun_prop] private theorem advanceBy_poly : Poly advanceBy := by unfold advanceBy; fun_prop

private def scaled (p : (Tally × Tally) × List Tally) : List Tally :=
  polyPush advanceBy p

@[fun_prop] private theorem scaled_poly : Poly scaled :=
  Poly.push ([],[]) [] advanceBy_poly

private def span (x : Inputs) := times (ruler x.2.1 ++ tally 1,x.1.2)

@[fun_prop] private theorem span_poly : Poly span := by unfold span; fun_prop

private def slots (x : Inputs) := scaled ((x.1.1 ++ span x,x.1.2),(Iter.lineup (ruler x.2.1)).reverse)

@[fun_prop] private theorem slots_poly : Poly slots := by unfold slots; fun_prop

def prefixStart (x : Inputs) : Tally := x.1.1 ++ span x ++ span x

@[fun_prop] theorem prefixStart_poly : Poly prefixStart := by unfold prefixStart; fun_prop

private def prefixSlots (x : Inputs) :=
  scaled ((prefixStart x,tally 1),Iter.lineup (ruler x.2.2))

@[fun_prop] private theorem prefixSlots_poly : Poly prefixSlots := by unfold prefixSlots; fun_prop

/-- Given low reserve, stride, actual targets, and controls in prefix order,
emit the prescribed pairs (prepared address, natural address). All lists and
arithmetic, including construction of the two sparse chunks, are charged. -/
def assigned (x : Inputs) : Assignments :=
  zipFair [] [] (slots x,x.2.1) ++ zipFair [] [] (prefixSlots x,x.2.2)

theorem assigned_poly : Poly assigned := by
  have h₁ := (slots_poly.pair (show Poly (fun x : Inputs => x.2.1) by fun_prop)).compose
    (easy_zip ([] : Tally) ([] : Tally)).poly
  have h₂ := (prefixSlots_poly.pair (show Poly (fun x : Inputs => x.2.2) by fun_prop)).compose
    (easy_zip ([] : Tally) ([] : Tally)).poly
  exact (h₁.pair h₂).compose (easy_append Easy.fst Easy.snd).poly

variable {k b c G low : ℕ}

def inputs (targets : Fin b → Fin k) (controls : Fin c → Fin k) (G low : ℕ) : Inputs :=
  ((tally low,tally G),List.ofFn (fun i => tally (targets i).val),List.ofFn (fun i => tally (controls i).val))

theorem prefixStart_inputs (targets : Fin b → Fin k) (controls : Fin c → Fin k) :
    (prefixStart (inputs targets controls G low)).length = low + 2*((b+1)*G) := by
  simp [prefixStart,span,inputs,Nat.two_mul]

/-- The unary table producer outputs these exact finite coordinates, in directory order. -/
theorem assigned_inputs (targets : Fin b → Fin k) (controls : Fin c → Fin k)
    (pos : 0<G) (fit : low+2*((b+1)*G)+c ≤ k) :
    assigned (inputs targets controls G low) =
      (pairs targets controls pos fit).map (fun z => (tally z.1.val,tally z.2.val)) := by
  let t := List.ofFn (fun i => tally (targets i).val)
  let u := List.ofFn (fun i => tally (controls i).val)
  let x := inputs targets controls G low
  have ht : (slots x).length = t.length := by simp [slots,scaled,polyPush,x,t,inputs]
  have hu : (prefixSlots x).length = u.length := by simp [prefixSlots,scaled,polyPush,x,u,inputs]
  change zipFair [] [] (slots x,t) ++ zipFair [] [] (prefixSlots x,u) = _
  rw [CRTTable.zipFair_eq_zip _ _ _ _ ht,CRTTable.zipFair_eq_zip _ _ _ _ hu]
  simp only [pairs,List.map_append,List.map_ofFn,Function.comp_def,targetPos,controlPos]
  congr 1
  · apply List.ext_getElem
    · simp [ht,t]
    · intro j h₁ h₂
      simp only [List.getElem_zip,List.getElem_ofFn]
      apply Prod.ext
      · apply List.ext_getElem
        · simp [slots,scaled,polyPush,Iter.lineup,List.getElem_reverse,advanceBy,span,
            x,inputs,targetOffset,← Nat.add_assoc]
          exact Or.inl rfl
        · intros; rfl
      · simp [t]
  · apply List.ext_getElem
    · simp [hu,u]
    · intro j h₁ h₂
      simp only [List.getElem_zip,List.getElem_ofFn]
      apply Prod.ext
      · apply List.ext_getElem
        · simp [prefixSlots,prefixStart,scaled,polyPush,Iter.lineup,advanceBy,span,x,inputs,controlOffset,
            Nat.two_mul,Nat.add_assoc]
          rfl
        · intros; rfl
      · simp [u]

end Controlled.PermutationLayout

end NearSquareRoot
end Computability
end OAI
