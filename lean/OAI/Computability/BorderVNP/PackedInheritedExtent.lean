import OAI.Computability.BorderVNP.PackedInheritedWorkWords

/-! # Exact staged site extent from the live endpoints

The virtual scan groups incoming bits by their actual site row and the binary
addition includes its old private work. A hole receives zero from both inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical ParseBatchSort VPVNP.VerifierNetwork Word
open private virtual_rep from OAI.Computability.BorderVNP.PackedInheritedEndpointViews
open private literals capacity from OAI.Computability.BorderVNP.PackedInheritedAddress
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- No live endpoints touch a row outside the image of the physical site table.
The virtual scan returns a zero incidence sum there. -/
theorem incoming_hole {x : σ → Bool} (h : Views.EndpointData N F siteID edgeID portID x)
    (fit : ∀ v, incoming N v < 2^w) (i : Fin s) (hi : i ∉ Set.range siteID) :
    value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j)) = 0 := by
  have hv := CellAddressViews.marker_value N siteID (fun _ => 0) siteID edgeID portID (Views.fields F)
    (virtual_rep N F siteID edgeID portID h) (capacity N siteID fit) i 2
  have outside (v : N.Site) : siteID v ≠ i := fun he => hi ⟨v,he⟩
  let : IsEmpty (N.InsideEdge siteID i) := ⟨fun z => outside _ z.property.1⟩
  let : IsEmpty (Supplied N siteID i) := ⟨fun z => by
    rcases z with e | p
    · exact e.property.elim (outside _) (outside _)
    · exact outside _ p.property⟩
  simpa [Views.frame,guessedSize,siteSize,suppliedSize] using hv

variable (work : Frame σ (Fin s × Fin w))

private noncomputable def operands : Frame σ (Fin s × Bool × Fin w) :=
  (parallelFrame work (Views.frame F)).select fun z =>
    if z.2.1 then .inr (.inr (.inr (2,z.1)),z.2.2) else .inl (z.1,z.2.2)

/-- Fixed arithmetic circuit producing every work-plus-incoming width at once.
Endpoint pins suffice to determine the incidence area before any staging
columns or owning cells have been assigned. -/
theorem exists_extent : ∃ f : Frame σ (Fin s × Fin w),
    f.size ≤ work.size + (Views.frame F).size + 1 + s*3*(100*(w+1)^2) ∧
    ∀ x i, let a := value (fun j => work.eval x (i,j))
      let b := value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j))
      a+b < 2^w → value (fun j => f.eval x (i,j)) = a+b := by
  let expr : WidthExpr Bool := .binary .add (.field false) (.field true)
  obtain ⟨f,hs,hf⟩ := exists_words (operands F work) id (fun _ => expr)
  refine ⟨f,?_,?_⟩
  · simpa [operands,expr,WidthExpr.nodes] using hs
  · intro x i a b fit
    let args := fun t => value (fun j => (operands F work).eval x (i,t,j))
    have ha : args false = a := by simp [args,a,operands]
    have hb : args true = b := by simp [args,b,operands]
    have hev : expr.eval args = a+b := by simp [expr,WidthExpr.eval,Op.apply,ha,hb]
    rw [← hev]
    apply hf x i
    exact ⟨value_lt _,value_lt _,(show expr.eval args < 2^w from hev.trans_lt fit)⟩

/-- The incidence scan and extent addition produce a hole-free row image of
the full current site bank, including self-loops and external ports. -/
theorem extent_covers {x : σ → Bool} (rep : Views.EndpointData N F siteID edgeID portID x)
    (state : N.Site → Site) (hin : ∀ v, (state v).incoming = incoming N v)
    (old : Covers siteID (fun v => (state v).work) work x) (room : ∀ v, (state v).size < 2^w)
    (f : Frame σ (Fin s × Fin w))
    (hf : ∀ i, let a := value (fun j => work.eval x (i,j))
      let b := value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j))
      a+b < 2^w → value (fun j => f.eval x (i,j)) = a+b) :
    Covers siteID (fun v => (state v).size) f x := by
  have fit (v : N.Site) : incoming N v < 2^w := by
    rw [← hin v]
    exact (Nat.le_add_left _ _).trans_lt (room v)
  constructor
  · intro v
    have h := hf (siteID v)
    dsimp only at h
    rw [old.live,Views.input_size N F siteID edgeID portID rep fit,← hin v] at h
    exact h (room v)
  · intro i hi
    have h := hf i
    dsimp only at h
    rw [old.hole i hi,incoming_hole N F siteID edgeID portID rep fit i hi,Nat.zero_add] at h
    exact h (Nat.two_pow_pos _)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
