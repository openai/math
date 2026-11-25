import OAI.Computability.MultitapeWeakETH.MotifAdmission

/-! # Choosing the same finite demand-grid point as the VP/VNP kernel -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter MotifSelector MotifBlocks MotifGrid MotifConversion
open private covers_poly from OAI.Computability.MultitapeWeakETH.MotifAdmission
open scoped Classical
noncomputable section

variable {k J D E : Type} [Field k] [Fintype J] [Fintype D] [Fintype E]
  {a b : D → J} {P : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
  (B : FixedBlock k a b P (realWidths p) (realWidths q) H H') (hp : ∀ i, 0 < p i)

/-- Scanning the fixed demand grid in its original order preserves the chosen table
entry even if several grid points cover the current demand vector. -/
theorem grid_poly : Poly (fun xs : Widths => Label.mk (demandGrid B hp (raw xs))) := by
  let good (xs : Widths) (z : D → ℚ) := decide (∀ i, MotifAdmission.coversCoordinate p (raw xs) i (z i) = true)
  let t := B.grid.demands
  let points : List t := t.toList.attach.map fun z => ⟨z.val, Finset.mem_toList.mp z.prop⟩
  have order : points.map Subtype.val = t.toList := by simp [points,List.map_map,Function.comp_def]
  let zero : t := ⟨_,B.grid.zero_mem_demands⟩
  have scan (zs : List t) : Poly (fun xs => Label.mk ((zs.find? (fun z => good xs z.val)).getD zero)) := by
    induction zs with
    | nil => exact Code.Poly.const (X:=Widths) (Label.mk zero)
    | cons z zs ih =>
      convert Poly.choose (covers_poly p z.val) (Code.Poly.const (Label.mk z)) ih using 1
      funext xs
      change Label.mk (((z::zs).find? (fun y => good xs y.val)).getD zero) = bif good xs z.val then _ else _
      cases ok : good xs z.val <;> simp [List.find?,ok]
  convert scan points using 1
  funext xs
  apply Label.ext
  have chosen := selectGrid_eq B hp (raw xs)
  change t.toList.find? (good xs) = some (demandGrid B hp (raw xs)).val at chosen
  rw [← order,List.find?_map] at chosen
  cases cell : points.find? (fun z => good xs z.val) with
  | none =>
    change (points.find? (fun z => good xs z.val)).map Subtype.val = _ at chosen
    rw [cell] at chosen
    cases chosen
  | some z =>
    change (points.find? (fun z => good xs z.val)).map Subtype.val = _ at chosen
    rw [cell] at chosen
    exact Subtype.ext (Option.some.inj chosen).symm

end
end OAI.Computability.MultitapeWeakETH.MotifFields
