import OAI.Computability.BorderVNP.DiagonalTagProgramRead

/-! # Original work predicates along the actual embeddings of retained sites -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Programs

open Crossing Diagonal.CellEntries

/-- A birth work vector in common numerical coordinates, zero after
its physical end. This permits the same original predicate to follow
an old site through changes of its incident-word type. -/
def extendWork {n : ℕ} (bits : Fin n → Bool) (j : ℕ) : Bool := if h : j<n then bits ⟨j,h⟩ else false

/-- A retained site checks the predicate of its own original source.
Sites freshly inserted outside the injection have no original private
choice to compare. -/
def carryPred {A B : Type*} (host : A ↪ B) (p : A → (ℕ → Bool) → Prop) (v : B) (bits : ℕ → Bool) : Prop :=
  ∀ u, host u = v → p u bits

theorem carryPred_old {A B : Type*} (host : A ↪ B) (p : A → (ℕ → Bool) → Prop) (v : A) (bits : ℕ → Bool) :
    carryPred host p (host v) bits ↔ p v bits :=
  ⟨fun h => h v rfl,fun h _ eq => host.injective eq ▸ h⟩

theorem carryPred_new {A B : Type*} (host : A ↪ B) (p : A → (ℕ → Bool) → Prop) {v : B}
    (fresh : ∀ u, host u ≠ v) (bits : ℕ → Bool) : carryPred host p v bits := fun u hu => (fresh u hu).elim

/-- Composing two real site injections carries exactly the same
independent birth choices as the two stages in sequence. -/
theorem carryPred_trans {A B C : Type*} (f : A ↪ B) (g : B ↪ C) (p : A → (ℕ → Bool) → Prop) :
    carryPred g (carryPred f p) = carryPred (f.trans g) p := by
  funext c b
  apply propext
  exact ⟨fun h u e => h (f u) e u rfl,fun h v eq u e => h u ((congrArg g e).trans eq)⟩

variable {D M np : ℕ} {P : Type} [Fintype P] {width : P → ℕ} {Param Gadget : Type*}

/-- The program installed at every site models the full tagged fiber at
all local inputs. The supplied predicates fix precisely the original
bottom-grid private bits. -/
def TagModels (N : Network D P width) (rows : N.Edge ↪ Fin M) (ports : P ↪ Fin np)
    (progs : Site.Programs N) (tags : N.Tables (Entry Param Gadget)) (number : Gadget ↪ ℕ)
    (pred : N.Site → (ℕ → Bool) → Prop) : Prop :=
  ∀ v, Site.Lineage.TagModel N rows ports v (progs v) (fun g => pred v (extendWork g)) tags number

end Packing.Inherited.Site.Programs

end BorderVNP
end Computability
end OAI
