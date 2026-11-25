import OAI.Computability.BorderVNP.PackedSewnFragmentSource
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.ParseBatchRowFrame

/-! # Public gates for the retained wire intervals of exterior sewing

Every old cable has two potential sparse rows. A live, positive-width cable
contributes at each incident site, with a single source row for a self-loop.
The two singleton scans supply its local start before and after sewing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.WireFragments

open Crossing PackedHistogram CellAddressCircuit CellAddressViews Inherited ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open scoped Classical

/-- Stable raw slot of an old row and its endpoint selector. The true selector denotes the source. -/
def ordinal {m : ℕ} : (Fin m × Bool) ≃ Fin (2*m) :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv).trans (finCongr (Nat.mul_comm m 2))

variable {s m n M N C k w : ℕ} {σ τ : Type} [Fintype σ] [Fintype τ]
variable (before : Fields s m n C w k w σ) (after : Fields s M N C w k w τ)
variable (old : σ → τ) (present : Fin m → σ) (retained : Fin m → Fin M)

private abbrev Pins (τ : Type) (s m n M N w : ℕ) :=
  τ ⊕ ((View s m n s × Fin w) ⊕ (View s M N s × Fin w))

private noncomputable def starts : Frame τ (Pins τ s m n M N w) :=
  (parallelFrame ((Views.frame before).subst (Frame.initial old)) (Views.frame after)).withInput

private def ptr (i : Fin m) (src : Bool) (j : Fin w) : Expr (Pins τ s m n M N w) :=
  .input (.inl (old (before.ptr (Layer.edgeEnd i src) j)))

private def width (i : Fin m) (j : Fin w) : Expr (Pins τ s m n M N w) :=
  .input (.inl (old (before.edgeWidth i j)))

private def live (i : Fin m) (src : Bool) : Expr (Pins τ s m n M N w) :=
  let nonzero := .not (eqWord (width before old i) (fun _ => .const false))
  let keep := if src then .const true else .not (eqWord (ptr before old i true) (ptr before old i false))
  .and (.input (.inl (old (present i)))) (.and nonzero keep)

private def select (i : Fin m) (src : Bool) : Fragment.Column w → Expr (Pins τ s m n M N w)
  | .inl false => live before old present i src
  | .inl true => .const true
  | .inr (field,j) =>
    match field.val with
    | 0 => ptr before old i src j
    | 1 => .input (.inr (.inl (.inl (Layer.edgeEnd i src),j)))
    | 2 => width before old i j
    | _ => .input (.inr (.inr (.inl (Layer.edgeEnd (retained i) src),j)))

/-- Executable four-word rows on the actual old and sewn cable tables. -/
noncomputable def frame : Frame τ (Fragment.Pin (2*m) w) :=
  (starts before after old).step fun z => select before old present retained (ordinal.symm z.1).1 (ordinal.symm z.1).2 z.2

private theorem raw {x : τ → Bool} (z : τ) : (starts before after old).eval x (.inl z) = x z :=
  Frame.withInput_eval_inl ..

/-- The flags test actual occupancy, positive width and distinct endpoint pointers. -/
theorem frame_active (x : τ → Bool) (i : Fin m) (src : Bool) :
    Fragment.active ((frame before after old present retained).eval x) (ordinal (i,src)) = true ↔
    x (old (present i)) = true ∧ 0 < value (x ∘ old ∘ before.edgeWidth i) ∧
    (src=true ∨ value (x ∘ old ∘ before.ptr (Layer.edgeEnd i true)) ≠ value (x ∘ old ∘ before.ptr (Layer.edgeEnd i false))) := by
  let z := (starts before after old).eval x
  have ptrEq : (eqWord (ptr (M := M) (N := N) before old i true) (ptr before old i false)).eval z = true ↔
      value (x ∘ old ∘ before.ptr (Layer.edgeEnd i true)) = value (x ∘ old ∘ before.ptr (Layer.edgeEnd i false)) := by
    rw [eqWord_eval]
    simp only [wordValue,ptr,StatementCircuit.Expr.eval,z,raw,Function.comp_def]
  have zeroEq : (eqWord (width (M := M) (N := N) before old i) (fun _ => .const false)).eval z = true ↔
      value (x ∘ old ∘ before.edgeWidth i) = 0 := by
    rw [eqWord_eval]
    simp only [wordValue,width,StatementCircuit.Expr.eval,z,raw,Function.comp_def,zero_value]
  cases src <;> simp [Fragment.active,frame,select,live,StatementCircuit.Expr.eval,raw,z,←Bool.not_eq_true,ptrEq,zeroEq,Nat.pos_iff_ne_zero]

/-- The four decoded scalar fields use the raw owner pointer, the old and new
singleton incidence starts, and the live old word width. -/
theorem frame_parse (x : τ → Bool) (i : Fin m) (src : Bool) :
    Fragment.parse ((frame before after old present retained).eval x) (ordinal (i,src)) =
      ⟨value (x ∘ old ∘ before.ptr (Layer.edgeEnd i src)),
        ⟨value (fun j => (Views.frame before).eval (x ∘ old) (.inl (Layer.edgeEnd i src),j)),
         value (x ∘ old ∘ before.edgeWidth i),
         some (value (fun j => (Views.frame after).eval x (.inl (Layer.edgeEnd (retained i) src),j)))⟩⟩ := by
  have projection : (Frame.initial old).eval x = x ∘ old := funext (Frame.initial_eval old x)
  simp [Fragment.parse,Fragment.parseRow,Fragment.word,frame,select,ptr,width,starts,StatementCircuit.Expr.eval,projection,Function.comp_def]

/-- The only additional gates after the two scans are the word comparisons and sparse output pins. -/
theorem frame_size :
    (frame before after old present retained).size ≤ (Views.frame before).size+(Views.frame after).size+
      (2*m)*(2+4*w)*(60*w+20) := by
  have cmp {u v : Fin w → Expr (Pins τ s m n M N w)} (hu : ∀ j, (u j).size ≤ 1) (hv : ∀ j, (v j).size ≤ 1) :=
    eqWord_size u v hu hv
  have bound (i : Fin m) (b : Bool) : (live (M := M) (N := N) before old present i b).size ≤ 60*w+20 := by
    have p := cmp (u := ptr before old i true) (v := ptr before old i false) (fun _ => le_rfl) (fun _ => le_rfl)
    have z := cmp (u := width before old i) (v := fun _ => .const false) (fun _ => le_rfl) (fun _ => le_rfl)
    cases b <;> simp only [live,Bool.false_eq_true,ite_false,ite_true,StatementCircuit.Expr.size] <;> omega
  have all (z : Fragment.Pin (2*m) w) :
      (select before old present retained (ordinal.symm z.1).1 (ordinal.symm z.1).2 z.2 :
        Expr (Pins τ s m n M N w)).size ≤ 60*w+20 := by
    rcases z with ⟨i,b|⟨f,j⟩⟩
    · cases b
      · exact bound _ _
      · simp [select,StatementCircuit.Expr.size]
    · fin_cases f <;> simp [select,ptr,width,StatementCircuit.Expr.size]
  have h := Frame.step_size_le (starts before after old) _ (60*w+20) all
  simpa only [frame,starts,Frame.withInput_size,parallelFrame_size,Frame.subst_size,Frame.initial_size,zero_add,
    Fragment.Pin,Fragment.Column,Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,Fintype.card_fin,Nat.mul_assoc] using h

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
