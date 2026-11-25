import OAI.Computability.BorderVNP.PackedCellAddressCircuit
import OAI.Computability.BorderVNP.PackedCellAddressRead

/-! # The batched address scan on the actual adaptive network

A positive-width row in the scan is either a real internal cable, one real site
staging slab, one crossing incidence, or one external port. Zero-width holes
and markers contribute no slots. Site ownership is read through the actual
sparse pointers of the public input, including pointers that change between epochs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressPhysical

open Crossing CellAddressCircuit CellAddresses ParseBatchSort Function
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open scoped Classical

variable {D s m n C d k w : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- Sparse raw input fields for the given branch, with zero widths in all unused rows. -/
structure Represents (x : σ → Bool) : Prop where
  /-- A placed site stores its current cell. -/
  owner : ∀ v, value (x ∘ F.owner (siteID v)) = (F.cells (cell v)).val
  /-- Each live source pointer names the actual source. -/
  src : ∀ e, value (x ∘ F.ptr (.inl (.inl (edgeID e)))) = (F.sites (siteID (N.src e))).val
  /-- Each live destination pointer names the actual destination. -/
  dst : ∀ e, value (x ∘ F.ptr (.inl (.inr (edgeID e)))) = (F.sites (siteID (N.dst e))).val
  /-- A live port names the site to which it is attached. -/
  attach : ∀ p, value (x ∘ F.ptr (.inr (portID p))) = (F.sites (siteID (N.attach p))).val
  /-- The physical cable width register. -/
  edge : ∀ e, value (x ∘ F.edgeWidth (edgeID e)) = N.width e
  /-- The per-site staging width. -/
  stage : ∀ v, value (x ∘ F.auxWidth (siteID v)) = aux v
  /-- The port width register. -/
  port : ∀ p, value (x ∘ F.portWidth (portID p)) = bits p
  /-- Reserved cable holes have no live lanes. -/
  edgeHole : ∀ i, i ∉ Set.range edgeID → value (x ∘ F.edgeWidth i) = 0
  /-- Reserved site holes have no staging words. -/
  stageHole : ∀ i, i ∉ Set.range siteID → value (x ∘ F.auxWidth i) = 0
  /-- Reserved port holes have no supplied bits. -/
  portHole : ∀ i, i ∉ Set.range portID → value (x ∘ F.portWidth i) = 0

variable {x : σ → Bool}

private theorem srcKey (h : Represents N cell aux siteID edgeID portID F x) (e : N.Edge) :
    (data F x).loc (.inl (.inl (edgeID e))) = (F.cells (cell (N.src e))).val :=
  (labels_value F x _ _ (h.src e)).trans (h.owner _)

private theorem dstKey (h : Represents N cell aux siteID edgeID portID F x) (e : N.Edge) :
    (data F x).loc (.inl (.inr (edgeID e))) = (F.cells (cell (N.dst e))).val :=
  (labels_value F x _ _ (h.dst e)).trans (h.owner _)

private theorem portKey (h : Represents N cell aux siteID edgeID portID F x) (p : P) :
    (data F x).loc (.inr (portID p)) = (F.cells (cell (N.attach p))).val :=
  (labels_value F x _ _ (h.attach p)).trans (h.owner _)

variable (c : Fin C)

/-- The three kinds of live local word, ordered by their region in the bank. -/
abbrev Local := (N.InsideEdge cell c ⊕ {v : N.Site // cell v = c}) ⊕ Supplied N cell c

/-- The physical bit width of a local row. -/
def localWidth : Local N cell c → ℕ :=
  Sum.elim (Sum.elim (fun e => N.width e.val) (fun v => aux v.val)) (suppliedWidth N cell c)

/-- Every local row occurs once in the static sparse address circuit. -/
noncomputable def localRow : Local N cell c ↪ Row s m n C :=
  (((((Embedding.subtype _).trans edgeID).trans Embedding.inl).sumMap
    (((Embedding.subtype _).trans siteID).trans Embedding.inl)).sumMap
    (((endRow N cell c edgeID).sumMap ((Embedding.subtype _).trans portID)).trans Embedding.inl))

omit [Fintype σ] in
private theorem code_ne {u v : Fin C} (hn : u ≠ v) : (F.cells u).val ≠ (F.cells v).val :=
  fun h => hn (F.cells.injective (Fin.ext h))

private theorem sourceRow (e : Boundary N cell c) (hs : cell (N.src e.val.val) = c) :
    localRow N cell siteID edgeID portID c (.inr (.inl e)) = .inr (.inl (.inl (.inl (edgeID e.val.val)))) := by
  simp [localRow,endRow,hs]

private theorem destRow (e : Boundary N cell c) (hs : cell (N.src e.val.val) ≠ c) :
    localRow N cell siteID edgeID portID c (.inr (.inl e)) = .inr (.inl (.inl (.inr (edgeID e.val.val)))) := by
  simp [localRow,endRow,hs]

private theorem row_key_width (h : Represents N cell aux siteID edgeID portID F x) (u : Local N cell c) :
    (data F x).address (fun v => (F.cells v).val) (localRow N cell siteID edgeID portID c u) = (F.cells c).val ∧
    (data F x).weight (localRow N cell siteID edgeID portID c u) = localWidth N cell aux c u := by
  rcases u with (e|v) | (e|p)
  · change (data F x).loc (.inl (.inl (edgeID e.val))) = _ ∧
      (if (data F x).loc (.inl (.inl (edgeID e.val))) = (data F x).loc (.inl (.inr (edgeID e.val)))
        then (data F x).edge (edgeID e.val) else 0) = _
    rw [srcKey N cell aux siteID edgeID portID F h, dstKey N cell aux siteID edgeID portID F h,
      e.property.1,e.property.2,ite_eq_left rfl]
    exact ⟨rfl,h.edge _⟩
  · exact ⟨(h.owner _).trans (congrArg (fun t => (F.cells t).val) v.property),h.stage _⟩
  · rcases e.property with hs | hd
    · rw [sourceRow N cell siteID edgeID portID c e hs]
      simp only [Data.address,Data.weight,srcKey N cell aux siteID edgeID portID F h,
        dstKey N cell aux siteID edgeID portID F h,code_ne F e.val.property,ite_false]
      exact ⟨congrArg (fun t => (F.cells t).val) hs,h.edge _⟩
    · have hs : cell (N.src e.val.val) ≠ c := fun eqn => e.val.property (eqn.trans hd.symm)
      rw [destRow N cell siteID edgeID portID c e hs]
      simp only [Data.address,Data.weight,srcKey N cell aux siteID edgeID portID F h,
        dstKey N cell aux siteID edgeID portID F h,code_ne F e.val.property,ite_false]
      exact ⟨congrArg (fun t => (F.cells t).val) hd,h.edge _⟩
  · exact ⟨(portKey N cell aux siteID edgeID portID F h _).trans (congrArg (fun t => (F.cells t).val) p.property), h.port _⟩

private theorem covered (h : Represents N cell aux siteID edgeID portID F x) (t : Row s m n C)
    (ht : (data F x).weight t ≠ 0) : ∃ c, t ∈ Set.range (localRow N cell siteID edgeID portID c) := by
  rcases t with ((i|v)|(u|v)) | (((i|i)|p)|v)
  all_goals try (exact (ht rfl).elim)
  · have hr : i ∈ Set.range edgeID := by
      by_contra hn
      exact ht (by simp [Data.weight,show (data F x).edge i = 0 from h.edgeHole i hn])
    obtain ⟨e,rfl⟩ := hr
    by_cases eqn : cell (N.src e) = cell (N.dst e)
    · exact ⟨cell (N.src e),.inl (.inl ⟨e,rfl,eqn.symm⟩),rfl⟩
    · have hn := code_ne F eqn
      exact (ht (by simp [Data.weight,srcKey N cell aux siteID edgeID portID F h,
        dstKey N cell aux siteID edgeID portID F h,hn])).elim
  · have hr : u ∈ Set.range siteID := by
      by_contra hn
      exact ht (h.stageHole u hn)
    obtain ⟨v,rfl⟩ := hr
    exact ⟨cell v,.inl (.inr ⟨v,rfl⟩),rfl⟩
  · have hr : i ∈ Set.range edgeID := by
      by_contra hn
      exact ht (by simp [Data.weight,show (data F x).edge i = 0 from h.edgeHole i hn])
    obtain ⟨e,rfl⟩ := hr
    by_cases eqn : cell (N.src e) = cell (N.dst e)
    · exact (ht (by simp [Data.weight,srcKey N cell aux siteID edgeID portID F h,
        dstKey N cell aux siteID edgeID portID F h,eqn])).elim
    · refine ⟨cell (N.src e),.inr (.inl ⟨⟨e,eqn⟩,.inl rfl⟩),?_⟩
      simp [localRow,endRow]
  · have hr : i ∈ Set.range edgeID := by
      by_contra hn
      exact ht (by simp [Data.weight,show (data F x).edge i = 0 from h.edgeHole i hn])
    obtain ⟨e,rfl⟩ := hr
    by_cases eqn : cell (N.src e) = cell (N.dst e)
    · exact (ht (by simp [Data.weight,srcKey N cell aux siteID edgeID portID F h,
        dstKey N cell aux siteID edgeID portID F h,eqn])).elim
    · refine ⟨cell (N.dst e),.inr (.inl ⟨⟨e,eqn⟩,.inr rfl⟩),?_⟩
      simp [localRow,endRow,eqn]
  · have hr : p ∈ Set.range portID := by
      by_contra hn
      exact ht (h.portHole p hn)
    obtain ⟨p,rfl⟩ := hr
    exact ⟨cell (N.attach p),.inr (.inr ⟨p,rfl⟩),rfl⟩

variable [Fintype P]

/-- Reindex the circuit's positive-width rows in one cell by the actual network words there. -/
theorem physical_sum (h : Represents N cell aux siteID edgeID portID F x) (pick : Row s m n C → Prop)
    [DecidablePred pick] :
    (∑ r : Row s m n C, if (data F x).address (fun v => (F.cells v).val) r = (F.cells c).val ∧ pick r
      then (data F x).weight r else 0) =
    ∑ u : Local N cell c, if pick (localRow N cell siteID edgeID portID c u) then localWidth N cell aux c u else 0 := by
  symm
  let row := localRow N cell siteID edgeID portID c
  apply Fintype.sum_of_injective row row.injective
  · intro t hnot
    by_cases hz : (data F x).weight t = 0
    · simp [hz]
    obtain ⟨c',u,rfl⟩ := covered N cell aux siteID edgeID portID F h t hz
    have hne : c' ≠ c := fun he => by subst c'; exact hnot ⟨u,rfl⟩
    have hk := (row_key_width N cell aux siteID edgeID portID F c' h u).1
    simp [hk, code_ne F hne]
  · intro u
    obtain ⟨hk,hw⟩ := row_key_width N cell aux siteID edgeID portID F c h u
    simp [row,hk,hw]

/-- Total bit count in the compact cell stack, before any padding. -/
theorem sum_width : (∑ u : Local N cell c, localWidth N cell aux c u) =
    guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c := by
  simp only [guessedSize,siteSize,suppliedSize,Fintype.sum_sum_type,localWidth,Sum.elim_inl,Sum.elim_inr]
  congr 3 <;> exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

/-- The actual scan computes the prefix of the compact physical bits in this cell.
Only the capacity of the actual live cell banks has to fit the machine word. -/
theorem physical_prefix (h : Represents N cell aux siteID edgeID portID F x)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c < 2^w)
    (r : Row s m n C) (hr : (data F x).address (fun v => (F.cells v).val) r = (F.cells c).val) :
    value (fun j => (frame F).eval x (r,j)) =
      ∑ u : Local N cell c, if order s m n C (localRow N cell siteID edgeID portID c u) < order s m n C r
        then localWidth N cell aux c u else 0 := by
  have hf (t : ℕ) : (∑ r : Row s m n C, if (data F x).address (fun v => (F.cells v).val) r = t
      then (data F x).weight r else 0) < 2^w := by
    by_cases hn : ∃ c, (F.cells c).val = t
    · obtain ⟨v,rfl⟩ := hn
      have heq := physical_sum N cell aux siteID edgeID portID F v h (fun _ => True)
      simp only [and_true,ite_true,sum_width] at heq
      rw [heq]
      exact fit v
    · have zero (r : Row s m n C) :
          (if (data F x).address (fun v => (F.cells v).val) r = t then (data F x).weight r else 0) = 0 := by
        by_cases hz : (data F x).weight r = 0
        · simp [hz]
        obtain ⟨v,u,rfl⟩ := covered N cell aux siteID edgeID portID F h r hz
        simp [(row_key_width N cell aux siteID edgeID portID F v h u).1,show (F.cells v).val ≠ t from fun hh => hn ⟨v,hh⟩]
      simp [zero]
  rw [frame_value F x hf,hr]
  exact physical_sum N cell aux siteID edgeID portID F c h (fun t => order s m n C t < order s m n C r)

end Packing.CellAddressPhysical

end BorderVNP
end Computability
end OAI
