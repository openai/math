import OAI.Hierarchy.DescentPackingOrdinals

namespace OAI
/-! # Finite directories in the order of their actual physical addresses -/

namespace Hierarchy.DescentPhysicalOrder
open scoped Classical BigOperators
noncomputable section

variable {A : Type*} [Fintype A]

private def unitRows (A : Type*) : A ≃ (Σ _ : A, Fin 1) where
  toFun a := ⟨a,0⟩
  invFun u := u.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨a,j⟩
    obtain rfl := Subsingleton.elim j (0 : Fin 1)
    rfl

/-- Compact a sparse occupied directory by counting the earlier occupied words. -/
def physical (rank : A ↪ ℕ) : A ≃ Fin (Fintype.card A) :=
  ((unitRows A).trans (DescentPacking.orderedUnits (fun _ : A => 1) rank rank.injective)).trans
    (finCongr (Fintype.card_congr (unitRows A)).symm)

theorem physical_val (rank : A ↪ ℕ) (x : A) :
    (physical rank x).val = (Finset.univ.filter (fun a => rank a < rank x)).card := by
  change ProtocolRAMPortRanks.«prefix» (fun _ : A => 1) rank x + 0 = _
  simp [ProtocolRAMPortRanks.«prefix»]

theorem physical_lt (rank : A ↪ ℕ) {x y : A} (h : rank x < rank y) :
    physical rank x < physical rank y := by
  change ProtocolRAMPortRanks.«prefix» (fun _ : A => 1) rank x + 0 <
    ProtocolRAMPortRanks.«prefix» (fun _ : A => 1) rank y + 0
  have bound := ProtocolRAMPortRanks.prefix_disjoint (fun _ : A => 1) rank h
  omega

theorem physical_lt_iff (rank : A ↪ ℕ) (x y : A) :
    physical rank x < physical rank y ↔ rank x < rank y := by
  refine ⟨fun h => ?_, physical_lt rank⟩
  rcases lt_trichotomy (rank x) (rank y) with less | eqn | greater
  · exact less
  · exact False.elim (h.ne (congrArg (physical rank) (rank.injective eqn)))
  · exact False.elim (h.not_gt (physical_lt rank greater))

/-- Give a semantic name to each physical ordinal used by the stage.
The allocator only reads the compacted ordinal. -/
def rename (rank : A ↪ ℕ) : Equiv.Perm A :=
  (physical rank).trans (Fintype.equivFin A).symm

@[simp] theorem code_rename (rank : A ↪ ℕ) (x : A) :
    Fintype.equivFin A (rename rank x) = physical rank x :=
  (Fintype.equivFin A).apply_symm_apply _

@[simp] theorem name_at (rank : A ↪ ℕ) (i : Fin (Fintype.card A)) :
    (rename rank).symm ((Fintype.equivFin A).symm i) = (physical rank).symm i := by
  simp [rename]

def home {U : Type*} (rank : A ↪ ℕ) (group : U → A) : U → A :=
  (rename rank) ∘ group

def address {B : Type*} (rank : A ↪ ℕ) (col : A ↪ B) : A ↪ B :=
  (rename rank).symm.toEmbedding.trans col

@[simp] theorem address_home {U B : Type*} (rank : A ↪ ℕ) (group : U → A) (col : A ↪ B) (u : U) :
    address rank col (home rank group u) = col (group u) := by
  change col ((rename rank).symm (rename rank _)) = _
  simp

theorem home_surjective {U : Type*} (rank : A ↪ ℕ) {group : U → A} (h : Function.Surjective group) :
    Function.Surjective (home rank group) :=
  (rename rank).surjective.comp h

theorem home_order (rank : A ↪ ℕ) {U : Type*} (group : U → A) (u : U) :
    (Fintype.equivFin A (home rank group u)).val =
      (Finset.univ.filter (fun a => rank a < rank (group u))).card := by
  rw [home,Function.comp_apply,code_rename,physical_val]

private theorem hasRow {U B : Type*} (row : U ↪ ℕ) (group : U → B)
    (covered : Function.Surjective group) (c : B) : ∃ i : ℕ, ∃ u, group u = c ∧ row u = i := by
  obtain ⟨u,rfl⟩ := covered c
  exact ⟨row u,u,rfl,rfl⟩

/-- First occurrence of each occupied group in the original tape. -/
def first {U B : Type*} (row : U ↪ ℕ) (group : U → B) (covered : Function.Surjective group) :
    B ↪ ℕ where
  toFun c := Nat.find (hasRow row group covered c)
  inj' := by
    intro c d eqn
    obtain ⟨u,hc,hu⟩ := Nat.find_spec (hasRow row group covered c)
    obtain ⟨v,hd,hv⟩ := Nat.find_spec (hasRow row group covered d)
    exact hc.symm.trans ((congrArg group (row.injective (hu.trans (eqn.trans hv.symm)))).trans hd)

theorem first_le {U B : Type*} (row : U ↪ ℕ) (group : U → B) (covered : Function.Surjective group) (u : U) :
    first row group covered (group u) ≤ row u :=
  Nat.find_min' _ ⟨u,rfl,rfl⟩

theorem first_at {U B : Type*} (row : U ↪ ℕ) (group : U → B) (covered : Function.Surjective group) (c : B) :
    ∃ u, group u = c ∧ row u = first row group covered c :=
  Nat.find_spec (hasRow row group covered c)

end
end Hierarchy.DescentPhysicalOrder

end OAI
