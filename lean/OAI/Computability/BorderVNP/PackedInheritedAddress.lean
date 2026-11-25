import OAI.Computability.BorderVNP.PackedInheritedRelabel
import OAI.Computability.BorderVNP.PackedCellAddressOutputs

/-! # Executable site-local incidence address columns

Run the cell address circuit with the public site row as its own cell and with
zero staging widths. This reuses the actual endpoint pointers and width
registers and assigns only two additional constant gates.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Views

open Crossing CellAddresses ParseBatchCounts ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open CellAddressCircuit CellAddressPhysical CellAddressViews
open private zero_value from OAI.Computability.BorderVNP.PackedCellAddressCircuit
open scoped Classical

variable {s m n C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

private noncomputable def literals : Frame σ (σ ⊕ Bool) :=
  ((Frame.initial id).step fun b : Bool => .const b).withInput

/-- Reuse the true physical width and pointer fields, setting each virtual cell to its public site. -/
noncomputable def fields : Fields s m n s d d w (σ ⊕ Bool) where
  sites := F.sites
  cells := F.sites
  owner r j := .inr ((numberWords d).symm (F.sites r) j)
  ptr e j := .inl (F.ptr e j)
  edgeWidth e j := .inl (F.edgeWidth e j)
  auxWidth _ _ := .inr false
  portWidth p j := .inl (F.portWidth p j)

/-- Fixed circuit returning both wire ends, all ports and incoming totals in site-local coordinates. -/
noncomputable def frame : Frame σ (View s m n s × Fin w) :=
  (CellAddressViews.frame (fields F)).subst literals

/-- Two shared constant wires suffice in addition to the one-site-per-cell address pass. -/
theorem frame_size : (frame F).size ≤ 2 + gateBound s m n s d d w + labelBound s m n d d +
    Fintype.card (View s m n s)*w*(60*d+16) := by
  have hl := Frame.step_size_le (Frame.initial (id : σ → σ)) (fun b : Bool => .const b) 1 (fun _ => le_rfl)
  simp only [Frame.initial_size,Fintype.card_bool,zero_add,mul_one] at hl
  have hs := CellAddressViews.frame_size (fields F)
  simp only [frame,Frame.subst_size,literals,Frame.withInput_size]
  omega

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {x : σ → Bool} (h : Represents N cell aux siteID edgeID portID F x)
variable (fit : ∀ v, incoming N v < 2^w)

private theorem eval_literals (x : σ → Bool) (i : σ ⊕ Bool) :
    literals.eval x i = i.elim x id := by
  rcases i with a | b <;> simp [literals,StatementCircuit.Expr.eval]

include h in
omit [Fintype P] in
private theorem represents :
    Represents N siteID (fun _ => 0) siteID edgeID portID (fields F) (literals.eval x) := by
  constructor
  · intro v
    simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inr,id_eq] using value_encode (F.sites (siteID v))
  · intro e; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.src e
  · intro e; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.dst e
  · intro p; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.attach p
  · intro e; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.edge e
  · intro v; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inr,id_eq] using zero_value w
  · intro p; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.port p
  · intro i hi; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.edgeHole i hi
  · intro i _; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inr,id_eq] using zero_value w
  · intro i hi; simpa only [Function.comp_def,fields,eval_literals,Sum.elim_inl] using h.portHole i hi

include fit in
private theorem capacity (c : Fin s) :
    guessedSize N siteID c + siteSize N siteID c (fun _ => 0) + suppliedSize N siteID c < 2^w := by
  simp only [siteSize,Finset.sum_const_zero,Nat.add_zero]
  by_cases hc : c ∈ Set.range siteID
  · rcases hc with ⟨v,rfl⟩
    rw [guessed_relabel,supplied_relabel]
    exact fit v
  · have hsite (v : N.Site) : siteID v ≠ c := fun h => hc ⟨v,h⟩
    let : IsEmpty (N.InsideEdge siteID c) := ⟨fun e => hsite _ e.property.1⟩
    let : IsEmpty (Supplied N siteID c) := ⟨fun u => by
      rcases u with e | p
      · exact e.property.elim (hsite _) (hsite _)
      · exact hsite _ p.property⟩
    simp [guessedSize,suppliedSize]

include h fit

/-- A source column reads the actual beginning of its incident word in the site's own slab. -/
theorem source_value (e : N.Edge) :
    value (fun j => (frame F).eval x (.inl (.inl (.inl (edgeID e))),j)) =
    wireStart N edgeID portID (N.src e) ⟨e,.inl rfl⟩ := by
  simp only [frame,Frame.subst_eval]
  exact (CellAddressViews.source_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (represents F N cell aux siteID edgeID portID h) (capacity N siteID fit) e).trans
    (wire_relabel N siteID edgeID portID _ _)

/-- A destination column uses the same slot as the source on a self-loop. -/
theorem dest_value (e : N.Edge) :
    value (fun j => (frame F).eval x (.inl (.inl (.inr (edgeID e))),j)) =
    wireStart N edgeID portID (N.dst e) ⟨e,.inr rfl⟩ := by
  simp only [frame,Frame.subst_eval]
  exact (CellAddressViews.dest_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (represents F N cell aux siteID edgeID portID h) (capacity N siteID fit) e).trans
    (wire_relabel N siteID edgeID portID _ _)

/-- Each exterior port has the stable start in its site's one-copy incidence array. -/
theorem port_value (p : P) :
    value (fun j => (frame F).eval x (.inl (.inr (portID p)),j)) =
    portStart N edgeID portID (N.attach p) ⟨p,rfl⟩ := by
  simp only [frame,Frame.subst_eval]
  exact (CellAddressViews.port_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (represents F N cell aux siteID edgeID portID h) (capacity N siteID fit) p).trans
    (port_relabel N siteID edgeID portID _ _)

/-- Region two is the exact incident storage for a real site, including its attached ports. -/
theorem incoming_value (v : N.Site) :
    value (fun j => (frame F).eval x (.inr (.inr (2,siteID v)),j)) = incoming N v := by
  have hv := CellAddressViews.marker_value N siteID (fun _ => 0) siteID edgeID portID (fields F)
    (represents F N cell aux siteID edgeID portID h) (capacity N siteID fit) (siteID v) 2
  simpa [frame,incoming,siteSize,guessed_relabel,supplied_relabel] using hv

end Packing.Inherited.Views

end BorderVNP
end Computability
end OAI
