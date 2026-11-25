import OAI.Computability.BorderVNP.ShortenPublicEndpointIndex
import OAI.Computability.BorderVNP.ShortenPublicEndpointSemantics
import OAI.Computability.BorderVNP.PackedBankPhysical

/-! # Merging the old-band and seed-bank cable circuits in stable row order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints.Successor

open Crossing StaticRows VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] {B σ : Type*} [Fintype B] [Fintype σ]
variable {n nSeeds s w : ℕ} (seed : A ≃ Fin nSeeds)

/-- A next-stage input table together with the occupancy bit of every cable candidate. -/
abbrev Next (B : Type*) (s n w : ℕ) := Inputs B s n w w ⊕ Fin n

private abbrev Wires (B A : Type*) (s n w : ℕ) :=
  (Fin s × B) ⊕ (Serializer.Row n D × Serializer.Output w) ⊕
    (A × TemplateEdge e × Packing.BankCircuit.Column × Fin w) ⊕ Unit

/-- Bank serializer column read by the corresponding field of the complete cable table. -/
def bankColumn : Serializer.Column → Packing.BankCircuit.Column
  | .src => .source | .dst => .destination | .width => .width

private def columnPin (r : Serializer.Row n D ⊕ (A × TemplateEdge e)) (col : Serializer.Column) (j : Fin w) :
    Wires e B A s n w :=
  r.elim (fun t => .inr (.inl (t,.inr (col,j)))) (fun t => .inr (.inr (.inl (t.1,t.2,bankColumn col,j))))

private noncomputable def pin : Next B s (edgeCapacity e n nSeeds) w → Wires e B A s n w
  | .inl (.inl t) => .inl t
  | .inl (.inr (i,.inl j)) => columnPin e ((candidateEquiv e n seed).symm i) .width j
  | .inl (.inr (i,.inr (true,j))) => columnPin e ((candidateEquiv e n seed).symm i) .src j
  | .inl (.inr (i,.inr (false,j))) => columnPin e ((candidateEquiv e n seed).symm i) .dst j
  | .inr i => ((candidateEquiv e n seed).symm i).elim (fun r => .inr (.inl (r,.inl ()))) (fun _ => .inr (.inr (.inr ())))

variable (sites : Frame σ (Fin s × B))
variable (old : Frame σ (Serializer.Row n D × Serializer.Output w))
variable (bank : Frame σ (A × TemplateEdge e × Packing.BankCircuit.Column × Fin w))

private noncomputable def present (σ : Type*) [Fintype σ] : Frame σ Unit :=
  (Frame.initial (Empty.elim : Empty → σ)).step fun _ => .const true

/-- Emit the site table, padded source and target IDs, widths, and occupancy as one Boolean frame.
All fully populated seed rectangles share a single constant occupancy gate. -/
noncomputable def merge : Frame σ (Next B s (edgeCapacity e n nSeeds) w) :=
  (parallelFrame sites (parallelFrame old (parallelFrame bank (present σ)))).select (pin e seed)

/-- Fixed permutation and field wiring charge at most one gate beyond the producing frames. -/
theorem merge_size : (merge e seed sites old bank).size ≤ sites.size + old.size + bank.size + 1 := by
  have hp : (present σ).size ≤ 1 := by
    simpa [present] using Frame.step_size_le (Frame.initial (Empty.elim : Empty → σ))
      (fun _ : Unit => .const true) 1 (fun _ => le_rfl)
  simp only [merge,Frame.select_size,parallelFrame_size]
  omega

variable (x : σ → Bool)

/-- Site payloads are forwarded without changes to their public names or bits. -/
theorem merge_site (i : Fin s) (j : B) :
    (merge e seed sites old bank).eval x (.inl (.inl (i,j))) = sites.eval x (i,j) := by
  simp [merge,pin]

/-- An old band's occupancy remains the computed enable bit, even for a zero-width live hook. -/
theorem merge_present_old (r : Serializer.Row n D) :
    (merge e seed sites old bank).eval x (.inr (candidateEquiv e n seed (.inl r))) = old.eval x (r,.inl ()) := by
  simp [merge,pin]

/-- Every cable in the fixed seed template is present on every accepted histogram branch. -/
theorem merge_present_bank (a : A) (u : TemplateEdge e) :
    (merge e seed sites old bank).eval x (.inr (candidateEquiv e n seed (.inr (a,u)))) = true := by
  simp [merge,pin,present,StatementCircuit.Expr.eval]

/-- Pin of a width or endpoint ID in a complete public table. -/
def fieldPin {B : Type*} {s n w : ℕ} (i : Fin n) (col : Serializer.Column) (j : Fin w) : Inputs B s n w w :=
  match col with
  | .width => .inr (i,.inl j)
  | .src => .inr (i,.inr (true,j))
  | .dst => .inr (i,.inr (false,j))

/-- The three numeric fields in an old-band row are the outputs of that band serializer. -/
theorem merge_field_old (r : Serializer.Row n D) (col : Serializer.Column) :
    value (fun j => (merge e seed sites old bank).eval x (.inl (fieldPin (candidateEquiv e n seed (.inl r)) col j))) =
      value (fun j => old.eval x (r,.inr (col,j))) := by
  apply congrArg value
  funext j
  cases col <;> simp [merge,pin,fieldPin,columnPin]

/-- The source, target and width words in a seed row are the actual compiled bank fields. -/
theorem merge_field_bank (a : A) (u : TemplateEdge e) (col : Serializer.Column) :
    value (fun j => (merge e seed sites old bank).eval x (.inl (fieldPin (candidateEquiv e n seed (.inr (a,u))) col j))) =
      value (fun j => bank.eval x (a,u,bankColumn col,j)) := by
  apply congrArg value
  funext j
  cases col <;> simp [merge,pin,fieldPin,columnPin]

end Shortening.PublicEndpoints.Successor

end BorderVNP
end Computability
end OAI
