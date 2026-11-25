import OAI.Computability.IntegerMultiplication.Packed.Column

/-! # Eight shifts with an external control word

Only the two target/auxiliary chunks occupy dimensions of the row. The first argument of
the P192 eight-shift gadget is held fixed as part of the row program's input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Packed
noncomputable section

variable {A B : Type}

/-- Restrict a permutation that preserves the first coordinate to one prescribed row. -/
def onRow (p : Equiv.Perm (A × B)) (h : ∀ x, (p x).1 = x.1) (c : A) : Equiv.Perm B where
  toFun yz := (p (c,yz)).2
  invFun yz := (p.symm (c,yz)).2
  left_inv yz := by
    change (p.symm (c, (p (c,yz)).2)).2 = yz
    rw [show (c, (p (c,yz)).2) = p (c,yz) from Prod.ext (h (c,yz)).symm rfl, Equiv.symm_apply_apply]
  right_inv yz := by
    have e := h (p.symm (c,yz))
    rw [Equiv.apply_symm_apply] at e
    change (p (c, (p.symm (c,yz)).2)).2 = yz
    rw [show (c, (p.symm (c,yz)).2) = p.symm (c,yz) from Prod.ext e rfl, Equiv.apply_symm_apply]

variable {H L i : ℕ}
abbrev Row (H L i : ℕ) := Queue H L i × Queue H L i

theorem walk_first (t : Turn) (p : Plate H L i) : (walk t p).1 = p.1 := by
  cases h : t.wing <;> simp [walk,h]

theorem cruise_first (o : List Turn) (p : Plate H L i) : (cruise o p).1 = p.1 := by
  induction o generalizing p with
  | nil => rfl
  | cons t o ih => exact (ih _).trans (walk_first _ _)

private theorem ideal_first (p : Plate H L i) : (ideal p).1 = p.1 := rfl

attribute [local irreducible] Packed.order

theorem repair_first (p : Plate H L i) : (repair p).1 = p.1 := by
  have e := cruise_first Packed.order ((cruise Packed.order).symm p)
  rw [Equiv.apply_symm_apply] at e
  rw [repair, Equiv.trans_apply, ideal_first]
  exact e.symm

def rowWalk (c : Queue H L i) (t : Turn) := onRow (walk t) (walk_first t) c

theorem rowWalk_symm_apply (c : Queue H L i) (t : Turn) (yz : Row H L i) :
    (rowWalk c t).symm yz = ((walk t).symm (c,yz)).2 := rfl

def rowCruise (c : Queue H L i) (o : List Turn) := onRow (cruise o) (cruise_first o) c

theorem rowCruise_nil (c : Queue H L i) : rowCruise c [] = Equiv.refl _ := rfl

theorem rowCruise_cons (c : Queue H L i) (t : Turn) (o : List Turn) :
    rowCruise c (t :: o) = (rowWalk c t).trans (rowCruise c o) := by
  apply Equiv.ext
  intro yz
  change (cruise o (walk t (c,yz))).2 = (cruise o (c,(walk t (c,yz)).2)).2
  rw [show (c, (walk t (c,yz)).2) = walk t (c,yz) from Prod.ext (walk_first t (c,yz)).symm rfl]

def rowRepair (c : Queue H L i) := onRow repair repair_first c

theorem rowRepair_packed (c : Queue H L i) (yz : Row H L i) :
    (c, rowRepair c yz) = repair (c,yz) := by
  apply Prod.ext
  · exact (repair_first (c,yz)).symm
  · rfl

theorem rowRepair_fixed (c : Queue H L i) (yz : Row H L i)
    (h : spotted (c,yz) = false) : rowRepair c yz = yz :=
  congrArg Prod.snd (valid_repair (c,yz) h)

def rowIdeal (c : Queue H L i) := onRow ideal (fun _ => rfl) c

theorem rowRepaired (c : Queue H L i) :
    (rowCruise c Packed.order).trans (rowRepair c) = rowIdeal c := by
  apply Equiv.ext
  intro yz
  change (repair (c,(cruise Packed.order (c,yz)).2)).2 = (ideal (c,yz)).2
  rw [show (c, (cruise Packed.order (c,yz)).2) = cruise Packed.order (c,yz) from
    Prod.ext (cruise_first Packed.order (c,yz)).symm rfl]
  simp [repair]

/-- The sparse-sort density bound holds for each external setting separately. -/
theorem row_spotted_rate (c : Queue H L i) :
    2^width H L * (Finset.univ.filter (fun yz : Row H L i => spotted (c,yz))).card ≤
      32*i * Fintype.card (Row H L i) := by
  classical
  have p := @spotted_rate H L i
  have he : Finset.univ.filter (fun x : Plate H L i => spotted x) =
      (Finset.univ : Finset (Queue H L i)) ×ˢ
        (Finset.univ.filter (fun yz : Row H L i => spotted (c,yz))) := by
    ext x
    simp [spotted]
  have cardPlate : Fintype.card (Plate H L i) = Fintype.card (Queue H L i) * Fintype.card (Row H L i) := Fintype.card_prod ..
  rw [he, Finset.card_product, Finset.card_univ, cardPlate] at p
  let : Nonempty (Queue H L i) := ⟨c⟩
  have hp : 0 < Fintype.card (Queue H L i) := Fintype.card_pos
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card (Queue H L i)) _ hp
  simpa only [Nat.mul_left_comm, Nat.mul_assoc, Nat.mul_comm] using p

end
end Controlled

end NearSquareRoot
end Computability
end OAI
