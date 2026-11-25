import OAI.Computability.BorderVNP.FiniteDiagonalBranches
import OAI.Computability.BorderVNP.DiagonalLayoutFieldContraction

/-! # Counting the complete tuple of native team traces

Each team contributes one accepting RAM trace on its true mutable memory.
The decoder acts on individual tuples of such traces. It preserves the actual
products of field outputs and counts the unit separately from the weighted
expansion terms, without comparing aggregate values as an input hypothesis.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP TeamContraction Routing FieldTeam Diagonal
open scoped BigOperators Classical

variable {F : Type*} [Field F] {R r w : ℕ} {S : Type*}

/-- One accepted chronological native RAM path per physical team. -/
abbrev NativeTuple (M : Fin (R+1) → MachineInput w S) (b : ∀ u, Bounds r (M u).inputSize) :=
  ∀ u, NativePath (M u) (b u).ticks (b u).burst (b u).privateClock

/-- Multiply the field outputs of the actual team traces. A team's output may
depend on its entire chronological run, including the private routine selected at each step. -/
noncomputable def tuplePathWeight {M : Fin (R+1) → MachineInput w S} {b : ∀ u, Bounds r (M u).inputSize}
    (weight : ∀ u, NativePath (M u) (b u).ticks (b u).burst (b u).privateClock → F)
    (p : NativeTuple M b) : F := ∏ u : Fin (R+1), weight u (p u)

/-- Specialization to field outputs obtained by multiplying weights attached to
individual events. -/
noncomputable def tupleWeight {M : Fin (R+1) → MachineInput w S} {b : ∀ u, Bounds r (M u).inputSize}
    (weight : Fin (R+1) → TeamRAM.Event w → F) (p : NativeTuple M b) : F :=
  tuplePathWeight (M := M) (b := b) (fun u trace => (trace.val.map (weight u)).prod) p

/-- The finite native trace enumeration used in the individual team sum. -/
noncomputable scoped instance nativeTraceFintype (M : MachineInput w S) (ticks burst privateClock : ℕ) :
    Fintype (NativePath M ticks burst privateClock) := Fintype.ofFinite _

/-- The independently summed native teams enumerate one tuple of accepting runs. -/
theorem prod_nativeValue (M : Fin (R+1) → MachineInput w S) (b : ∀ u, Bounds r (M u).inputSize)
    (weight : Fin (R+1) → TeamRAM.Event w → F) :
    (∏ u, FieldTeam.nativeValue (M u) (b u) (weight u)) = ∑ p, tupleWeight (M := M) (b := b) weight p := by
  exact Fintype.prod_sum (fun u (p : NativePath (M u) (b u).ticks (b u).burst (b u).privateClock) =>
    (p.val.map (weight u)).prod)

variable [Fintype F] {t d link inner n : ℕ} {Edge : Type} [Fintype Edge]
  (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)

/-- Weight-preserving decoding of individual accepted native tuples evaluates the
whole live contraction. The decoder ignores zero-output runs, can depend on the
exterior assignment, and must distinguish all contributing expansion terms. -/
theorem field_contraction_eq_one_add_paths {ι : Type*} [Fintype ι]
    (M : (Exterior R r link → Bool) → Fin (R+1) → MachineInput w S)
    (bnd : ∀ ext u, Bounds r (M ext u).inputSize)
    (weight : ∀ ext u, NativePath (M ext u) (bnd ext u).ticks (bnd ext u).burst (bnd ext u).privateClock → F)
    (localNative : ∀ ext u, fieldValue G F pin ext u = ∑ trace, weight ext u trace)
    (hw : 0 < w) (layout : ι → WireLayout (R+1) r link)
    (banks : ∀ i ext, WireSnapshots G pin ext (layout i) w)
    (fixed : ι → Block (R+1)) (header : ∀ i, Fin (layout i).header → Bool)
    (high payload : ι → Fin (R+1) → Fin (R+1) → ℕ → Bool) (value : ι → F)
    (decode : ∀ ext, {p : NativeTuple (M ext) (bnd ext) // tuplePathWeight (M := M ext) (b := bnd ext) (weight ext) p ≠ 0} ≃
      {tag : Option ι // branchPasses layout banks fixed header high payload ext tag ∧ branchWeight value tag ≠ 0})
    (output : ∀ ext p, tuplePathWeight (M := M ext) (b := bnd ext) (weight ext) p.val =
      branchWeight value (decode ext p).val) :
    fieldContraction G F pin = 1 + ∑ i, value i := by
  rw [fieldContraction_eq]
  refine (Finset.sum_congr rfl ?_).trans (sum_branches hw layout banks fixed header high payload value)
  intro ext _
  have expanded : (∏ u, fieldValue G F pin ext u) = ∑ p, tuplePathWeight (M := M ext) (b := bnd ext) (weight ext) p :=
    (Finset.prod_congr rfl fun u _ => localNative ext u).trans (Fintype.prod_sum (weight ext))
  exact expanded.trans (sum_of_branch_decode _ _ _ (decode ext) (output ext))

/-- The event-product and checked-history version of the native branch count. -/
theorem field_contraction_eq_one_add {ι : Type*} [Fintype ι]
    (M : (Exterior R r link → Bool) → Fin (R+1) → MachineInput w S)
    (bnd : ∀ ext u, Bounds r (M ext u).inputSize) (place : ∀ ext u, Placement (bnd ext u) w)
    (weight : (Exterior R r link → Bool) → Fin (R+1) → TeamRAM.Event w → F)
    (localHistories : ∀ ext u, fieldValue G F pin ext u =
      FieldTeam.historyValue (M ext u) (bnd ext u) (place ext u) (weight ext u))
    (hw : 0 < w) (layout : ι → WireLayout (R+1) r link)
    (banks : ∀ i ext, WireSnapshots G pin ext (layout i) w)
    (fixed : ι → Block (R+1)) (header : ∀ i, Fin (layout i).header → Bool)
    (high payload : ι → Fin (R+1) → Fin (R+1) → ℕ → Bool) (value : ι → F)
    (decode : ∀ ext, {p : NativeTuple (M ext) (bnd ext) // tupleWeight (M := M ext) (b := bnd ext) (weight ext) p ≠ 0} ≃
      {tag : Option ι // branchPasses layout banks fixed header high payload ext tag ∧ branchWeight value tag ≠ 0})
    (output : ∀ ext p, tupleWeight (M := M ext) (b := bnd ext) (weight ext) p.val =
      branchWeight value (decode ext p).val) :
    fieldContraction G F pin = 1 + ∑ i, value i := by
  apply field_contraction_eq_one_add_paths G pin M bnd
    (fun ext u p => (p.val.map (weight ext u)).prod) _ hw layout banks fixed header high payload value decode output
  intro ext u
  exact (localHistories ext u).trans (FieldTeam.historyValue_eq_native ..)

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
