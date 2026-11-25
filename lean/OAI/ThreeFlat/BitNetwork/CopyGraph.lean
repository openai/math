import OAI.ThreeFlat.BitNetwork
import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Trivalent incidence graph for addressed tables

All occurrences of one address share a chain of bits. Each occurrence reads
one spoke from the chain. The terminal node also handles an unused hidden
address by leaving its single chain bit free.
-/

namespace ThreeFlat.BitNetwork

open Computability.BorderVNP.Crossing
open scoped Classical

variable {F : Type*} {p : ℕ} (N : BitNetwork F p)

abbrev Socket := Fin N.cells × Fin 3
def address (u : N.Socket) := N.source u.1 u.2
abbrev Source := BitSource N.internal p
abbrev Fiber (s : N.Source) := {u : N.Socket // N.address u = s}
noncomputable abbrev arity (s : N.Source) := Fintype.card (N.Fiber s)

/-- Order a source's occurrences by their row-major socket addresses. -/
noncomputable def socketOrder (s : N.Source) : N.Fiber s ≃ Fin (N.arity s) := by
  let e : N.Socket ≃ Fin (N.cells * 3) := finProdFinEquiv
  let _ : LinearOrder (N.Fiber s) :=
    LinearOrder.lift' (fun u : N.Fiber s => e u.val) (e.injective.comp Subtype.val_injective)
  exact (Fintype.orderIsoFinOfCardEq (N.Fiber s) rfl).toEquiv.symm

abbrev CopySite := Fin N.cells ⊕ ((s : N.Source) × Fin (N.arity s + 2))
abbrev CopyEdge := ((s : N.Source) × Fin (N.arity s + 1)) ⊕ N.Socket

noncomputable def copyPosition (u : N.Socket) : Fin (N.arity (N.address u) + 2) :=
  ((N.socketOrder (N.address u) ⟨u, rfl⟩).succ).castSucc

noncomputable def copySrc : N.CopyEdge → N.CopySite
  | .inl ⟨s, j⟩ => .inr ⟨s, j.castSucc⟩
  | .inr u => .inr ⟨N.address u, N.copyPosition u⟩

noncomputable def copyDst : N.CopyEdge → N.CopySite
  | .inl ⟨s, j⟩ => .inr ⟨s, j.succ⟩
  | .inr u => .inl u.1

/-- For ordinary tensor contraction the spatial positions can all be the origin.
Every bit line has two endpoints, including a final terminal after the last spoke. -/
noncomputable def copyGraph : Network 0 (Fin p) (fun _ => 1) where
  Site := N.CopySite
  Edge := N.CopyEdge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := N.copySrc
  dst := N.copyDst
  width := fun _ => 1
  attach := fun j => .inr ⟨.pin j, 0⟩
  position := fun _ => 0
  in_ball := by simp

end ThreeFlat.BitNetwork

end OAI
