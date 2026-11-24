import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.Card

/-!
# Indexed directed regular wire graphs

In Section 7 of *VP and VNP differ over every field* each vertex has `d`
outgoing and `d` incoming slots. A permutation sends each outgoing slot to
the unique incoming slot of its arc. The two numberings are independent.
An arc translates its source lane by its own displacement.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

/-- A directed multigraph with separate incoming and outgoing slot numberings. -/
structure SlotGraph (V : Type*) (d : ℕ) where
  /-- The permutation matching each outgoing base slot to the incoming base slot at the other
  end of its directed arc. -/
  target : Equiv.Perm (V × Fin d)
  ends_ne : ∀ p, (target p).1 ≠ p.1

/-- A base slot graph equipped with its lane displacements. -/
structure LiftedSlots (V : Type*) (d : ℕ) (L : Type*) where
  /-- The directed slot graph whose arcs are lifted over the lane group. -/
  base : SlotGraph V d
  /-- The lane increment assigned to each outgoing base slot, added to the source lane to
  obtain the target lane. -/
  displacement : V × Fin d → L

namespace LiftedSlots

variable {V L : Type*} {d : ℕ} [AddCommGroup L] (G : LiftedSlots V d L)

/-- Match each actual outgoing slot to its actual incoming slot. The inverse
recovers the source base arc and subtracts its displacement. -/
def actualTarget : Equiv.Perm ((V × Fin d) × L) where
  toFun p := (G.base.target p.1, p.2 + G.displacement p.1)
  invFun q := (G.base.target.symm q.1, q.2 - G.displacement (G.base.target.symm q.1))
  left_inv := by rintro ⟨p, g⟩; simp
  right_inv := by rintro ⟨q, g⟩; simp

@[simp] theorem actualTarget_apply (p : V × Fin d) (g : L) :
    G.actualTarget (p, g) = (G.base.target p, g + G.displacement p) := rfl

@[simp] theorem actualTarget_symm_apply (q : V × Fin d) (g : L) :
    G.actualTarget.symm (q, g) =
      (G.base.target.symm q, g - G.displacement (G.base.target.symm q)) := rfl

/-- Slot endpoints move together when all lanes translate by a common offset. -/
theorem actualTarget_translate (p : V × Fin d) (g a : L) :
    G.actualTarget (p, g + a) = ((G.actualTarget (p,g)).1, (G.actualTarget (p,g)).2 + a) := by
  simp [add_right_comm]

/-- Forget the lane structure, retaining the full directed regular graph. -/
def actualGraph : SlotGraph (V × L) d where
  target :=
    let e := Equiv.prodAssoc V L (Fin d) |>.trans
      ((Equiv.refl V).prodCongr (Equiv.prodComm L (Fin d))) |>.trans
      (Equiv.prodAssoc V (Fin d) L).symm
    e.trans (G.actualTarget.trans e.symm)
  ends_ne := by
    rintro ⟨⟨x, g⟩, i⟩ h
    exact G.base.ends_ne (x,i) (congrArg (fun z : V × L => z.1) h)

@[simp] theorem actualGraph_target (x : V) (g : L) (i : Fin d) :
    G.actualGraph.target ((x,g),i) =
      (((G.base.target (x,i)).1, g + G.displacement (x,i)), (G.base.target (x,i)).2) := rfl

@[simp] theorem actualGraph_target_symm (y : V) (g : L) (i : Fin d) :
    G.actualGraph.target.symm ((y,g),i) =
      (((G.base.target.symm (y,i)).1, g - G.displacement (G.base.target.symm (y,i))),
        (G.base.target.symm (y,i)).2) := rfl

end LiftedSlots

end Compression

end VPVNP
end Computability
end OAI
