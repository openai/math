import OAI.Computability.BorderVNP.PackedCellSlabs
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Internal wire and supplied argument addresses of a contracted cell

Internal cables occupy one consecutive guessed word per cable in physical row order.
Supplied words are ordered by crossing source endpoint, crossing destination endpoint,
then external port. Both fine endpoints of a cell-internal cable read the same address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddresses

open Crossing Function
open scoped Classical BigOperators

variable {D m n s : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C)

/-- Cross-cell wires having an endpoint in this cell. -/
abbrev Boundary := {e : N.CrossingEdge cell // cell (N.src e.val) = c ∨ cell (N.dst e.val) = c}

/-- Supplied words consist of crossing cables and attached argument ports. -/
abbrev Supplied := Boundary N cell c ⊕ {p : P // cell (N.attach p) = c}

/-- Live width of each supplied word. -/
def suppliedWidth : Supplied N cell c → ℕ := Sum.elim (fun e => N.width e.val.val) (fun p => bits p.val)

/-- Compact size of the guessed wire block. Each loop is counted once. -/
noncomputable def guessedSize : ℕ := ∑ e : N.InsideEdge cell c, N.width e.val

/-- Compact size of the supplied argument block. -/
noncomputable def suppliedSize [Fintype P] : ℕ := ∑ u : Supplied N cell c, suppliedWidth N cell c u

/-- Compact size of the private per-site staging storage for this cell. -/
noncomputable def siteSize (aux : N.Site → ℕ) : ℕ := ∑ v : {v : N.Site // cell v = c}, aux v.val

variable (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Internal cables use their original sparse public cable number. -/
def guessedRow : N.InsideEdge cell c ↪ ℕ :=
  ((Embedding.subtype _).trans edgeID).trans Fin.valEmbedding

private noncomputable def endRow : Boundary N cell c ↪ Fin m ⊕ Fin m where
  toFun e := if cell (N.src e.val.val) = c then .inl (edgeID e.val.val) else .inr (edgeID e.val.val)
  inj' := by
    intro e f eqn
    apply Subtype.ext
    apply Subtype.ext
    apply edgeID.injective
    have h := congrArg (Sum.elim id id) eqn
    dsimp only at h
    split at h <;> split at h <;> exact h

/-- Supplied rows reserve both endpoint columns and the port column, skipping empty slots. -/
noncomputable def suppliedRow : Supplied N cell c ↪ ℕ :=
  ((((endRow N cell c edgeID).trans finSumFinEquiv.toEmbedding).sumMap
    ((Embedding.subtype _).trans portID)).trans finSumFinEquiv.toEmbedding).trans Fin.valEmbedding

/-- An auxiliary site slab follows the canonical internal words and earlier sites of the cell. -/
noncomputable def siteBase (siteID : N.Site ↪ Fin s) (aux : N.Site → ℕ)
    (v : {v : N.Site // cell v = c}) : ℕ :=
  guessedSize N cell c + CellSlabs.start (((Embedding.subtype _).trans siteID).trans Fin.valEmbedding)
    (fun w => aux w.val) v

/-- Site slab bounds in the complete private part of the assignment stack. -/
theorem siteBase_fits (siteID : N.Site ↪ Fin s) (aux : N.Site → ℕ)
    (v : {v : N.Site // cell v = c}) :
    siteBase N cell c siteID aux v + aux v.val ≤ guessedSize N cell c + siteSize N cell c aux := by
  rw [siteBase, Nat.add_assoc]
  exact Nat.add_le_add_left (CellSlabs.end_le_capacity _ _ _) _

/-- The private bit vector is equivalent to all the cell's internal cable words. -/
noncomputable def guessedWords : (Fin (guessedSize N cell c) → Bool) ≃ N.InsideAssignment cell c :=
  CellSlabs.words (guessedRow N cell c edgeID) (fun e => N.width e.val)

/-- The supplied bit vector is equivalent to all crossing endpoints and argument ports. -/
noncomputable def suppliedWords [Fintype P] :
    (Fin (suppliedSize N cell c) → Bool) ≃ (∀ u : Supplied N cell c, Fin (suppliedWidth N cell c u) → Bool) :=
  CellSlabs.words (suppliedRow N cell c edgeID portID) (suppliedWidth N cell c)

/-- Bijection used to guess one copy of every private site staging slab. -/
noncomputable def siteWords (siteID : N.Site ↪ Fin s) (aux : N.Site → ℕ) :
    (Fin (siteSize N cell c aux) → Bool) ≃ (∀ v : {v : N.Site // cell v = c}, Fin (aux v.val) → Bool) :=
  CellSlabs.words (((Embedding.subtype _).trans siteID).trans Fin.valEmbedding) (fun v => aux v.val)

private theorem ends {v : N.Site} (hv : cell v = c) {e : N.Edge} (he : N.src e = v ∨ N.dst e = v)
    (same : cell (N.src e) = cell (N.dst e)) : cell (N.src e) = c ∧ cell (N.dst e) = c := by
  rcases he with h | h
  · exact ⟨h ▸ hv, same.symm.trans (h ▸ hv)⟩
  · exact ⟨same.trans (h ▸ hv), h ▸ hv⟩

private theorem incidence {v : N.Site} (hv : cell v = c) {e : N.Edge} (he : N.src e = v ∨ N.dst e = v) :
    cell (N.src e) = c ∨ cell (N.dst e) = c := by
  rcases he with h | h
  · exact Or.inl (h ▸ hv)
  · exact Or.inr (h ▸ hv)

variable [Fintype P]

/-- The position of a supplied bit within the compact external vector. -/
noncomputable def suppliedOrdinal (u : Supplied N cell c) (k : Fin (suppliedWidth N cell c u)) :
    Fin (suppliedSize N cell c) := CellSlabs.ordinal (suppliedRow N cell c edgeID portID) _ ⟨u,k⟩

/-- Address of the same shared wire bit as seen by a fine site inside the cell. -/
noncomputable def wire (v : {v : N.Site // cell v = c})
    (e : {e : N.Edge // N.src e = v.val ∨ N.dst e = v.val}) (k : Fin (N.width e.val)) :
    Fin (guessedSize N cell c) ⊕ Fin (suppliedSize N cell c) :=
  if h : cell (N.src e.val) = cell (N.dst e.val) then
    .inl (CellSlabs.ordinal (guessedRow N cell c edgeID) _ ⟨⟨e.val, ends N cell c v.property e.property h⟩, k⟩)
  else .inr (suppliedOrdinal N cell c edgeID portID
    (.inl ⟨⟨e.val,h⟩, incidence N cell c v.property e.property⟩) k)

/-- The external port word is supplied only to its attached fine site's cell. -/
noncomputable def port (v : {v : N.Site // cell v = c}) (p : {p : P // N.attach p = v.val})
    (k : Fin (bits p.val)) : Fin (suppliedSize N cell c) :=
  suppliedOrdinal N cell c edgeID portID (.inr ⟨p.val, (congrArg cell p.property).trans v.property⟩) k

variable {R : Type*} [CommSemiring R]

/-- The product read from two physical bit vectors. -/
noncomputable def factor (table : N.Tables R) (g : Fin (guessedSize N cell c) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) : R :=
  ∏ v : {v : N.Site // cell v = c}, table v.val
    (fun e k => (wire N cell c edgeID portID v e k).elim g x)
    (fun p k => x (port N cell c edgeID portID v p k))

/-- Summing compact internal guesses computes the contracted tensor's actual cell entry. -/
theorem sum_factor [Fintype C] [DecidableEq C]
    (pos : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (table : N.Tables R) (w : ∀ e : Boundary N cell c, Fin (N.width e.val.val) → Bool)
    (args : ∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool) :
    let values : ∀ u : Supplied N cell c, Fin (suppliedWidth N cell c u) → Bool := fun u =>
      match u with | .inl e => w e | .inr p => args p
    let x := (suppliedWords N cell c edgeID portID).symm values
    (∑ g, factor N cell c edgeID portID table g x) = N.cellTables cell pos table c w args := by
  intro values x
  have read (u : Supplied N cell c) (i : Fin (suppliedWidth N cell c u)) :
      x (suppliedOrdinal N cell c edgeID portID u i) = values u i :=
    congrFun (congrFun ((suppliedWords N cell c edgeID portID).apply_symm_apply values) u) i
  unfold Network.cellTables
  apply Fintype.sum_equiv (guessedWords N cell c edgeID)
  intro g
  unfold factor
  apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
  intro v _
  congr 1
  · funext e k
    by_cases h : cell (N.src e.val) = cell (N.dst e.val)
    · simp only [wire,h,dite_true]
      rfl
    · simp only [wire,h,dite_false,Sum.elim_inr]
      apply read
  · funext p k
    apply read

omit [Fintype P] in
/-- A site staging area forced to specified values has exactly one valid assignment,
for each setting of the internal wires. -/
theorem sum_staged (siteID : N.Site ↪ Fin s) (aux : N.Site → ℕ)
    (expected : (Fin (guessedSize N cell c) → Bool) → ∀ v : {v : N.Site // cell v = c}, Fin (aux v.val) → Bool)
    (f : (Fin (guessedSize N cell c) → Bool) → R) :
    (∑ g, ∑ y : Fin (siteSize N cell c aux) → Bool,
      if siteWords N cell c siteID aux y = expected g then f g else 0) = ∑ g, f g := by
  apply Finset.sum_congr rfl
  intro g _
  simp only [← Equiv.eq_symm_apply]
  simp

end Packing.CellAddresses

end BorderVNP
end Computability
end OAI
