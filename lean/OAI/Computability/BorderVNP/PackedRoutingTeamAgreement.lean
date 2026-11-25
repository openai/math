import OAI.Computability.BorderVNP.PackedRoutingTraffic

/-! # Agreement of the positive delivery directories reconstructed on different teams

The current-team RAM can contain arbitrary unrelated words. Only actual
occupied private/live placement keys are relevant to the populated directory.
Their owners and within-cell offsets come from the same numbered network.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open private slot_exists width_eq from OAI.Computability.BorderVNP.TransmissionDataKeys

/-- The original processor, field, source offset and width of a candidate are
independent of the RAM values read by the placement tables. -/
private theorem source_parts (d : Layout) (p l p' l' : ℕ → ℕ × ℕ) (i : ℕ) :
    let a := d.row p l i
    let b := d.row p' l' i
    (a.team,a.processor,a.field,a.offset,a.width) = (b.team,b.processor,b.field,b.offset,b.width) := by
  simp only [Layout.row]
  split <;> rfl

/-- The ordered compact row lists agree as soon as all genuine destination
keys agree, including runs where unused final-slice reads differ. -/
theorem Layout.directory_congr_keys (d : Layout) (p l p' l' : ℕ → ℕ × ℕ) (bounds : d.DestinationBounds)
    (keys : ∀ k, d.keyPlacement p l k = d.keyPlacement p' l' k) :
    d.directory p l = d.directory p' l' := by
  let z : ℕ → ℕ × ℕ := fun _ => (0,0)
  let positive (i : ℕ) := decide (0 < (d.row z z i).width)
  have same (pp lp : ℕ → ℕ × ℕ) : (fun (r : Row) => decide (0 < r.width)) ∘ d.row pp lp = positive := by
    funext j
    exact congrArg (fun w => decide (0<w)) (width_eq d pp lp j)
  simp only [Layout.directory,List.filter_map,same]
  apply List.map_congr_left
  intro i hi
  obtain ⟨range,h⟩ := List.mem_filter.mp hi
  have inRange := List.mem_range.mp range
  have nonzero : 0 < (d.row z z i).width := of_decide_eq_true h
  obtain ⟨k,_,occ⟩ := slot_exists d bounds ⟨i,inRange⟩ 0 nonzero
  obtain ⟨hc,hs⟩ := occ p l
  obtain ⟨hc',hs'⟩ := occ p' l'
  have cell : (d.row p l i).cell = (d.row p' l' i).cell := hc.trans ((congrArg Prod.fst (keys k.1)).trans hc'.symm)
  have slot : (d.row p l i).slot = (d.row p' l' i).slot := by
    simpa only [Nat.add_zero] using hs.trans ((congrArg (fun v : ℕ × ℕ => v.2+k.2.val) (keys k.1)).trans hs'.symm)
  have src := source_parts d p l p' l' i
  generalize d.row p l i = a at src cell slot ⊢
  generalize d.row p' l' i = b at src cell slot ⊢
  cases a
  cases b
  simpa only [Row.mk.injEq,Prod.mk.injEq] using
    (show _ from by simp only [Prod.mk.injEq] at src; exact ⟨src.1,src.2.1,src.2.2.1,src.2.2.2.1,cell,slot,src.2.2.2.2⟩)

end Packing.Directory

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA VPVNP.BurstRAM
open scoped Classical

variable {D s m n C d k w W : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable {σ : Type*} [Fintype σ]

/-- Two actual private placement returns yield the same seven-word directory
at the same selected external network, irrespective of their physical origins. -/
theorem common_directory (dir : Directory.Layout) (bounds : dir.DestinationBounds)
    (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n C d k w σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (width : ∀ i, bits (live i) = dir.block) (gap : ℕ) (head origin : Bool → ℕ) (before after : Bool → ℕ → ℕ)
    (image : ∀ i, Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x (origin i) (before i))
    (run : ∀ i, (privateLayout (head i) (origin i) m C dir.entries dir.description gap).Image
      (before i) dir.entries (after i))
    (room : ∀ i, (privateLayout (head i) (origin i) m C dir.entries dir.description gap).Fits W (before i)) :
    let p i := Directory.ISA.placement (after i) (bases (origin i) m C dir.entries).privatePairs
    let l i := Directory.ISA.placement (after i) (bases (origin i) m C dir.entries).livePairs
    dir.directory (p false) (l false) = dir.directory (p true) (l true) := by
  intro p l
  let place (i : Bool) := (image i).networkPlacement N cell aux siteID edgeID portID F net code fit dir original live
    width (head i) (origin i) gap (before i) (after i) (run i) (room i)
  exact dir.directory_congr_keys (p false) (l false) (p true) (l true) bounds
    (fun a => ((place false).entry a).trans ((place true).entry a).symm)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
