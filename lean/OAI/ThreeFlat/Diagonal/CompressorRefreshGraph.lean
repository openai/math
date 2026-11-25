import OAI.Computability.VPVNP.SlotGraph
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

namespace OAI
/-! # The graph in the compressor's degree-restoration step

One outgoing port is used for each old bundle. A loop-free regular graph on
the ports supplies the internal wires. A cyclic permutation on the ports
pads to the requested degree. All three parts have a fixed lane displacement
on each base slot. -/

namespace ThreeFlat.Diagonal.CompressorRefresh

open Computability.VPVNP.Compression

variable {V H L : Type*} {a b D : ℕ}

/-- Separate the two ranges of slots without changing the current vertex. -/
def slotCases (V : Type*) (a b : ℕ) :
    V × Fin (a + b) ≃ (V × Fin a) ⊕ (V × Fin b) :=
  ((Equiv.refl V).prodCongr finSumFinEquiv.symm).trans (Equiv.prodSumDistrib _ _ _)

def unionTarget (A : SlotGraph V a) (B : SlotGraph V b) :
    Equiv.Perm (V × Fin (a + b)) :=
  let e := slotCases V a b
  e.trans ((A.target.sumCongr B.target).trans e.symm)

theorem unionTarget_left (A : SlotGraph V a) (B : SlotGraph V b) (p : V × Fin a) :
    unionTarget A B ((slotCases V a b).symm (.inl p)) =
      (slotCases V a b).symm (.inl (A.target p)) := by
  simp [unionTarget]

theorem unionTarget_right (A : SlotGraph V a) (B : SlotGraph V b) (p : V × Fin b) :
    unionTarget A B ((slotCases V a b).symm (.inr p)) =
      (slotCases V a b).symm (.inr (B.target p)) := by
  simp [unionTarget]

/-- Concatenate the slot ranges of two loop-free regular lifted graphs. -/
def union (A : LiftedSlots V a L) (B : LiftedSlots V b L) : LiftedSlots V (a + b) L where
  base := {
    target := unionTarget A.base B.base
    ends_ne := by
      intro p
      obtain ⟨q, rfl⟩ := (slotCases V a b).symm.surjective p
      cases q with
      | inl p => rw [unionTarget_left]; exact A.base.ends_ne p
      | inr p => rw [unionTarget_right]; exact B.base.ends_ne p
  }
  displacement p := Sum.elim A.displacement B.displacement (slotCases _ _ _ p)

/-- Project the old displacement to the remaining lane. Its base permutation
sends the outgoing port of a bundle to its receiving port. -/
def external (G : LiftedSlots V D (H × L)) : LiftedSlots (V × Fin D) 1 L where
  base := {
    target := G.base.target.prodCongr (Equiv.refl _)
    ends_ne := fun p eq => G.base.ends_ne p.1 (congrArg Prod.fst eq)
  }
  displacement p := (G.displacement p.1).2

@[simp] theorem external_target [AddCommGroup L] (G : LiftedSlots V D (H × L))
    (p : V × Fin D) (g : L) :
    (external G).actualTarget ((p, 0), g) =
      ((G.base.target p, 0), g + (G.displacement p).2) := rfl

/-- Within each block the old target sends the consumed coordinate through
a permutation, independently of the remaining lane. -/
def portPermutation [AddCommGroup H] (G : LiftedSlots V D (H × L)) (p : V × Fin D) :
    Equiv.Perm H where
  toFun h := h + (G.displacement p).1
  invFun h := h - (G.displacement p).1
  left_inv _ := add_sub_cancel_right ..
  right_inv _ := sub_add_cancel ..

theorem old_bundle_target [AddCommGroup H] [AddCommGroup L]
    (G : LiftedSlots V D (H × L)) (p : V × Fin D) (h : H) (g : L) :
    G.actualTarget (p, h, g) =
      (G.base.target p, portPermutation G p h, g + (G.displacement p).2) := rfl

/-- A copy of a port graph within every block. -/
def internal [Zero L] (V : Type*) (E : SlotGraph (Fin D) a) :
    LiftedSlots (V × Fin D) a L where
  base := {
    target := (Equiv.prodAssoc V (Fin D) (Fin a)).trans
      (((Equiv.refl V).prodCongr E.target).trans (Equiv.prodAssoc _ _ _).symm)
    ends_ne := fun p eq => E.ends_ne (p.1.2, p.2) (congrArg Prod.snd eq)
  }
  displacement _ := 0

@[simp] theorem internal_target [AddCommGroup L] (E : SlotGraph (Fin D) a)
    (v : V) (j : Fin D) (s : Fin a) (g : L) :
    (internal (L := L) V E).actualTarget (((v,j),s),g) =
      (((v,(E.target (j,s)).1),(E.target (j,s)).2),g) := by
  change (_, g + 0) = _
  rw [add_zero]
  rfl

private theorem rotate_ne (hD : 2 ≤ D) (j : Fin D) : finRotate D j ≠ j := by
  obtain _ | n := D
  · omega
  obtain ⟨j, hj⟩ := j
  intro eq
  by_cases before : j < n
  · rw [finRotate_of_lt before] at eq
    have h := congrArg Fin.val eq
    change j + 1 = j at h
    omega
  · have last : j = n := by omega
    subst j
    rw [finRotate_last'] at eq
    have h := congrArg Fin.val eq
    change 0 = n at h
    omega

/-- All padding arcs rotate the port. This includes zero padding slots. -/
def padding (hD : 2 ≤ D) (n : ℕ) : SlotGraph (Fin D) n where
  target := (finRotate D).prodCongr (Equiv.refl _)
  ends_ne p := rotate_ne hD p.1

/-- The degree-restored graph. Every port has one external slot, `a`
expander slots and `n` cyclic padding slots in each direction. -/
def graph [Zero L] (G : LiftedSlots V D (H × L)) (E : SlotGraph (Fin D) a)
    (hD : 2 ≤ D) (n : ℕ) : LiftedSlots (V × Fin D) (1 + a + n) L :=
  union (union (external G) (internal V E)) (internal V (padding hD n))

end ThreeFlat.Diagonal.CompressorRefresh

end OAI
