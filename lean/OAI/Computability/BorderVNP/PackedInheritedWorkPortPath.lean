import OAI.Computability.BorderVNP.PackedInheritedWorkPorts

/-! # Fixed argument columns on all stages of an epoch

The public port directory at a stage consists of one copy of the previous
directory for every child. Only the static site rectangle size determines
its host displacements. Flattening retains the same integers and changes
their argument labels.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Shortening Shortening.Adaptive
open scoped Classical

/-- A length-only port header with its public argument enumeration. -/
structure PortTable (P : Type) where
  /-- Number of allocated rows in the argument directory, including vacant rows. -/
  count : ℕ
  /-- Assign each argument its distinct public directory row. -/
  row : P ↪ Fin count
  /-- Stored attachment pointer and bit width for every allocated row. -/
  fields : Ports count

/-- Concatenate argument directories in the stage's child order. -/
def PortTable.parallel {P : Type} (p : PortTable P) (fan sites : ℕ) : PortTable (Fin fan × P) :=
  ⟨fan*p.count,Parallel.portRows fan p.row,p.fields.parallel fan sites⟩

/-- Fixed header for each of the recursively nested internal-stage argument types. -/
def PortTable.path {P : Type} (p : PortTable P) (fan : ℕ) (sites : ℕ → ℕ) :
    (j : ℕ) → PortTable (Port fan P j)
  | 0 => p
  | j+1 => (p.path fan sites j).parallel fan (sites j)

/-- Reindex the root's port labels by their row-major leaf, preserving its
physical slot header for the next outer epoch. -/
def PortTable.flatten {P : Type} {k : ℕ} (b : ℕ) (p : PortTable (Port k P b)) : PortTable (Fin (k^b) × P) :=
  ⟨p.count,Flat.portRows b p.row,p.fields⟩

/-- Static width words, including the unique zero width at each unused row. -/
structure PortTable.Widths {P : Type} (p : PortTable P) (bits : P → ℕ) (w : ℕ) : Prop where
  live : ∀ a, p.fields.width (p.row a) = bits a
  holes : ∀ i, i ∉ Set.range p.row → p.fields.width i = 0
  fit : ∀ i, p.fields.width i < 2^w

/-- Repeating argument headers preserves their physical width and all holes. -/
theorem PortTable.Widths.parallel {P : Type} {p : PortTable P} {bits : P → ℕ} {w : ℕ} (h : p.Widths bits w)
    (k V : ℕ) : (p.parallel k V).Widths (fun a => bits a.2) w := by
  constructor
  · rintro ⟨i,a⟩
    change p.fields.width ((finProdFinEquiv.symm (finProdFinEquiv (i,p.row a))).2) = bits a
    simpa only [Equiv.symm_apply_apply] using h.live a
  · intro i hi
    obtain ⟨⟨j,r⟩,rfl⟩ := finProdFinEquiv.surjective i
    have hv : r ∉ Set.range p.row := by rintro ⟨a,rfl⟩; exact hi ⟨(j,a),rfl⟩
    change p.fields.width ((finProdFinEquiv.symm (finProdFinEquiv (j,r))).2) = 0
    simpa only [Equiv.symm_apply_apply] using h.holes r hv
  · exact fun i => h.fit (finProdFinEquiv.symm i).2

/-- All nested width words are therefore known before a child or branch is selected. -/
theorem PortTable.Widths.path {P : Type} {p : PortTable P} {bits : P → ℕ} {w : ℕ} (h : p.Widths bits w)
    (k : ℕ) (V : ℕ → ℕ) (n : ℕ) : (p.path k V n).Widths (width bits k n) w := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.parallel k (V n)

/-- The original widths and all unused slots survive flattening. -/
theorem PortTable.Widths.flatten {P : Type} {k b w : ℕ} {p : PortTable (Port k P b)} {bits : P → ℕ}
    (h : p.Widths (width bits k b) w) : (p.flatten b).Widths (fun a => bits a.2) w := by
  constructor
  · intro a
    change p.fields.width (p.row ((portEquiv k P b).symm a)) = bits a.2
    simpa only [Equiv.apply_symm_apply] using (h.live ((portEquiv k P b).symm a)).trans (width_portEquiv bits k b _)
  · intro i hi
    apply h.holes i
    rintro ⟨v,rfl⟩
    exact hi ⟨portEquiv k P b v,congrArg p.row ((portEquiv k P b).symm_apply_apply _)⟩
  · exact h.fit

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
