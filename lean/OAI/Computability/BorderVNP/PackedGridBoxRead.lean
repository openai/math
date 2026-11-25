import OAI.Computability.BorderVNP.PackedGridBoxBudget

/-! # Exact contraction of the sparse one-copy private box

The supplied bank places all guessed and boundary bits at their canonical offsets.
Bits for the unary reports can follow them or be supplied elsewhere by the enclosing
bundle. A passing assignment contributes one in the guard contraction, including
characteristic two. Summing all private wire assignments computes the actual cell entry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse CellAddresses
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} [Fintype C] (cell : N.Site → C) (c : C)
variable {m n s : ℕ} (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable (rules : ∀ v : N.Site, Rule N v)
variable {R : Type*} [CommSemiring R]

omit [Fintype C] in
/-- On the exact physical cell bank, the Boolean success of the sparse directory
is the semiring-valued product of all the actual local guards. -/
theorem oneCopy_product (use : Port → Bool) (g : Fin (guessedSize N cell c) → Bool)
    (x : Fin (suppliedSize N cell c) → Bool) (bank : ℕ → Bool)
    (hread : ∀ i : Fin (stride N cell c), bank i.val = copyBits N cell c g x i)
    (huse : ∀ v : {v : N.Site // cell v = c}, ∀ l p, rules v.val = .unary l p →
      bank (p.atBit 0 0) = use p) :
    (if ((directory N cell c siteID edgeID portID (fun v => rules v.val) 1).observations bank).isSome
      then (1:R) else 0) =
      CellAddresses.factor N cell c edgeID portID (guardedTable N rules use) g x := by
  unfold CellAddresses.factor guardedTable
  rw [Fintype.prod_boole]
  apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
  apply propext
  rw [directory_accepts]
  have atSite (v : {v : N.Site // cell v = c}) :
      accepts N cell c edgeID portID v bank 0 0 (rules v.val) =
      (rules v.val).passes (fun
        | .inl ⟨e,k⟩ => (wire N cell c edgeID portID v e k).elim g x
        | .inr ⟨p,k⟩ => x (port N cell c edgeID portID v p k)) use := by
    rw [accepts_passes]
    have hl : (fun l => bank (0+(lane N cell c edgeID portID v l).val)) = (fun
        | .inl ⟨e,k⟩ => (wire N cell c edgeID portID v e k).elim g x
        | .inr ⟨p,k⟩ => x (port N cell c edgeID portID v p k)) := by
      funext l
      rw [Nat.zero_add, hread]
      rcases l with ⟨e,k⟩ | ⟨p,k⟩ <;> simp only [lane,copyBits,Equiv.symm_apply_apply,Sum.elim_inr]
    rw [hl]
    cases hv : rules v.val with
    | truth => rfl
    | unary l p => rw [Rule.passes,Rule.passes,huse v l p hv]
  constructor
  · intro h v
    convert! (atSite v).symm.trans (by simpa using h 0 (by decide) v) using 2
    funext l
    rcases l with ⟨e,k⟩ | ⟨p,k⟩ <;> rfl
  · intro h i hi v
    have he : i = 0 := by omega
    subst i
    simp only [Nat.zero_mul]
    apply (atSite v).trans
    convert! h v using 2
    funext l
    rcases l with ⟨e,k⟩ | ⟨p,k⟩ <;> rfl

/-- The private directory with one guessed vector per cell gives exactly the
`cellTables` entry on the exposed cable and external words, for any commutative semiring. -/
theorem sum_privateBox (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (use : Port → Bool) (w : ∀ e : Boundary N cell c, Fin (N.width e.val.val) → Bool)
    (args : ∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool)
    (bank : (Fin (guessedSize N cell c) → Bool) → ℕ → Bool)
    (hread : ∀ g i, bank g i.val = copyBits N cell c g
      ((suppliedWords N cell c edgeID portID).symm (fun u =>
        match u with | .inl e => w e | .inr p => args p)) i)
    (huse : ∀ g (v : {v : N.Site // cell v = c}) l p,
      rules v.val = .unary l p → bank g (p.atBit 0 0) = use p) :
    (∑ g, if ((directory N cell c siteID edgeID portID (fun v => rules v.val) 1).observations (bank g)).isSome
      then (1:R) else 0) =
      N.cellTables cell position (guardedTable N rules use) c w args := by
  rw [← CellAddresses.sum_factor N cell c edgeID portID position (guardedTable N rules use) w args]
  exact Finset.sum_congr rfl fun g _ => oneCopy_product N cell c siteID edgeID portID rules
    use g _ (bank g) (hread g) (huse g)

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
