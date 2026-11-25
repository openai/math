import OAI.Hierarchy.DescentTerminalBoard

namespace OAI
/-! # Indexing branch-dependent terminal cables in a single fixed host pool -/

namespace Hierarchy.DescentTerminalPorts
open Computability.BorderVNP.Crossing ThreeFlat.Routing CallPool
open ProtocolStackContraction
open scoped Classical BigOperators
noncomputable section
variable {D w : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits) {G : Type} [Fintype G]

abbrev InPool (owner : Group N ↪ G) (g : G) := {e : N.Edge // owner (group N e)=g}

def poolSize (w : ℕ) (owner : Group N ↪ G) (g : G) :=
  ∑ e : InPool N owner g,poolBatchCount (N.width e.val) w

omit [Fintype G] in
/-- With no active cable at a physical group address, its allocated
prefix is empty in both directions. -/
theorem poolSize_empty (w : ℕ) (owner : Group N ↪ G) (g : G) (absent : g∉Set.range owner) :
    poolSize N w owner g=0 := by
  let : IsEmpty (InPool N owner g) := ⟨fun e=>absent ⟨group N e.val,e.property⟩⟩
  simp [poolSize]

private def inPoolEquiv (w : ℕ) (owner : Group N ↪ G) : Piece N w ≃
    ((g : G) × ((e : InPool N owner g) × Fin (poolBatchCount (N.width e.val) w))) where
  toFun u := ⟨owner (group N u.1),⟨u.1,rfl⟩,u.2⟩
  invFun u := ⟨u.2.1.val,u.2.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨g,⟨⟨e,h⟩,k⟩⟩; subst g; rfl

def poolIndex (w : ℕ) (owner : Group N ↪ G) (code : N.Edge ↪ ℕ) :
    Piece N w ≃ Edge (poolSize N w owner) :=
  (inPoolEquiv N w owner).trans (Equiv.sigmaCongrRight fun g=>ProtocolRAMPortRanks.enumerate
    (fun e : InPool N owner g=>poolBatchCount (N.width e.val) w) (fun e=>code e.val)
    (code.injective.comp Subtype.val_injective))

omit [Fintype G] in
theorem poolIndex_group (w : ℕ) (owner : Group N ↪ G) (code : N.Edge ↪ ℕ) (u : Piece N w) :
    (poolIndex N w owner code u).1=owner (group N u.1) := rfl

omit [Fintype G] in
theorem poolIndex_number (w : ℕ) (owner : Group N ↪ G) (code : N.Edge ↪ ℕ) (u : Piece N w) :
    (poolIndex N w owner code u).2.val =
      ProtocolRAMPortRanks.prefix (fun e : InPool N owner (owner (group N u.1)) =>
        poolBatchCount (N.width e.val) w) (fun e=>code e.val) ⟨u.1,rfl⟩+u.2.val := rfl

theorem poolSize_total (w : ℕ) (owner : Group N ↪ G) (code : N.Edge ↪ ℕ) :
    (∑g,poolSize N w owner g) = Fintype.card (Piece N w) := by
  simpa only [Edge,Fintype.card_sigma,Fintype.card_fin] using (Fintype.card_congr (poolIndex N w owner code)).symm

end
end Hierarchy.DescentTerminalPorts

end OAI
