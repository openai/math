import OAI.Computability.BorderVNP.PackedInheritedWorkDirectory
import OAI.Computability.BorderVNP.PackedHistoryNormalizedTransport

/-! # Returning the root's work and extent at the scheduled row indices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.PublicCapacity PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] {k oldV rootV newV w : ℕ}

/-- A public site state together with its work and extent words. -/
abbrev WithWidths (Geo : Type) (V w : ℕ) := Geo ⊕ (Fin V × Bool × Fin w)

/-- Read an assigned work or extent word without any gates. -/
noncomputable def assignedColumn {Geo : Type} [Fintype Geo] {V w : ℕ} (extent : Bool) :
    Frame (WithWidths Geo V w) (Fin V × Fin w) := Frame.initial fun z => .inr (z.1,extent,z.2)

private def geometryPin : (Fin k × X) ⊕ Y → (Fin k × WithWidths X oldV w) ⊕ WithWidths Y rootV w :=
  Sum.map (fun z => (z.1,.inl z.2)) Sum.inl

variable (geom : Frame ((Fin k × X) ⊕ Y) Z) (h : newV = rootV)

/-- Execute the terminal placement on the geometric inputs. Both width columns of its root
are returned at their scheduled row numbers by aliasing the root inputs. -/
noncomputable def returnFrame :
    Frame ((Fin k × WithWidths X oldV w) ⊕ WithWidths Y rootV w) (WithWidths Z newV w) :=
  (geom.subst (Frame.initial geometryPin)).withInput.select
    (Sum.elim Sum.inr (fun z => .inl (.inr (.inr (Fin.cast h z.1,z.2)))))

/-- Passing the two arrays through the post-frame has zero additional gate cost. -/
theorem returnFrame_size : (returnFrame (oldV := oldV) (w := w) geom h).size = geom.size := by simp [returnFrame]

variable (x : Fin k × WithWidths X oldV w → Bool) (y : WithWidths Y rootV w → Bool)

/-- The geometric columns use exactly the original terminal placement. -/
theorem returnFrame_geom (j : Z) : (returnFrame geom h).eval (Sum.elim x y) (.inl j) =
    geom.eval (Sum.elim (fun a => x (a.1,.inl a.2)) (y ∘ Sum.inl)) j := by
  have wire : (Frame.initial geometryPin).eval (Sum.elim x y) =
      Sum.elim (fun a : Fin k × X => x (a.1,.inl a.2)) (y ∘ Sum.inl) := by
    funext z; cases z <;> simp [geometryPin]
  simp only [returnFrame,Frame.select_eval,Sum.elim_inl,Frame.withInput_eval_inr,Frame.subst_eval,wire]

/-- The literal root bits are available at the successor's physical row number. -/
theorem returnFrame_width (i : Fin newV) (b : Bool) (j : Fin w) :
    (returnFrame geom h).eval (Sum.elim x y) (.inr (i,b,j)) = y (.inr (Fin.cast h i,b,j)) := by
  simp [returnFrame]

/-- Every occupied or vacant successor row carries the word from the identical terminal
directory row, after transporting the rectangle. -/
theorem returnFrame_covers {D : ℕ} {P : Type} {K : Type*} {bits : P → ℕ} {p : Pack D P bits K}
    {s : Shape} {E : ℕ} (hs : s = ⟨rootV,E⟩) (rows : Rows ⟨rootV,E⟩ p.layout)
    (n : p.layout.Site → ℕ) (b : Bool) (read : Covers rows.site n (assignedColumn b) y) :
    Covers (returnedRows (p := p) hs rows).site n (assignedColumn b)
      ((returnFrame geom (congrArg Shape.sites hs)).eval (Sum.elim x y)) := by
  subst s
  constructor
  · intro v
    simpa only [returnedRows,assignedColumn,Frame.initial_eval,returnFrame_width,Fin.cast_refl,id_eq] using read.live v
  · intro i hi
    simpa only [returnedRows,assignedColumn,Frame.initial_eval,returnFrame_width,Fin.cast_refl,id_eq] using read.hole i hi

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
