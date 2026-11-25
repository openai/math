import OAI.Computability.NearSquareRoot.CRTTableFullLevel

/-! # Natural port permutations of a padded CRT axis -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

private def addInside {m L : ℕ} [NeZero m] (hm : m ≤ L)
    (δ : ZMod m) (j : Fin L) : Fin L :=
  if j.val < m then ⟨((j.val : ZMod m) + δ).val,(ZMod.val_lt _).trans_le hm⟩ else j

private theorem addInside_val {m L : ℕ} [NeZero m] (hm : m ≤ L)
    (δ : ZMod m) (j : Fin L) :
    (addInside hm δ j).val = if j.val < m then ((j.val : ZMod m) + δ).val else j.val := by
  by_cases h : j.val < m <;> simp [addInside,h]

private theorem addInside_inverse {m L : ℕ} [NeZero m] (hm : m ≤ L)
    (δ : ZMod m) (j : Fin L) : addInside hm (-δ) (addInside hm δ j) = j := by
  apply Fin.ext
  by_cases h : j.val < m
  · simp only [addInside_val, ite_eq_left h, ite_eq_left (ZMod.val_lt _), ZMod.natCast_zmod_val,
      add_neg_cancel_right, ZMod.val_natCast, Nat.mod_eq_of_lt h]
  · simp [addInside_val,h]

/-- A controlled modular translation with all unused binary ports fixed. -/
def portPerm {m L : ℕ} [NeZero m] (hm : m ≤ L) (δ : ZMod m) : Equiv.Perm (Fin L) where
  toFun := addInside hm δ
  invFun := addInside hm (-δ)
  left_inv := addInside_inverse hm δ
  right_inv j := by simpa using addInside_inverse hm (-δ) j

variable {d : ℕ} (a w : Fin d → ℕ) {E : Fin d → Type}
  (pad : ∀ g, E g → Fin (2^w g - a g)) [∀ j, NeZero (a j)]

/-- The complete content of a single target's table, as a permutation of
all fixed-width binary ports, for the gate indexed by the serial schedule. -/
theorem levelTables_portPerm (hwidth : ∀ j, a j ≤ 2^w j)
    (hdense : ∀ j, 2^w j ≤ 2*a j) (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (n : ℕ) (hn : n < Nat.clog 2 d) (j : Fin (CRTTree.level n (List.finRange d)).length)
    (y : CRT.Address a E) (inv : Bool) :
    let s := Stage.atLevel d n hn j
    ∀ i : Fin (CRTTree.right s.node).length,
      let g := (CRTTree.right s.node)[i.val]
      let δ := CRT.mergeOffset (s.left a E) y g
      let π := portPerm (hwidth g) (bif inv then -δ else δ)
      let all := levelTables (levelQuery a w pad n y inv)
      let tab := ((all[j.val]?.getD [])[i.val]?).getD []
      tab.length = 2^w g ∧ ∀ u : Fin (2^w g), (tab[u.val]?.getD []).length = (π u).val := by
  intro s i
  obtain ⟨base,hpos⟩ := level_node_consecutive (List.getElem_mem j.isLt)
  have h := (nodeTables_paddedMerge a w pad hwidth hdense hcop base _ _ hpos
    (s.left a E) (s.left_computes a E) (s.left_preservesTags a E) (s.right a E)
    (CRT.build_preservesTags _ _ _ _) s.disjoint y inv).2 i
  dsimp only
  rw [levelTables_lookup a w pad n hn.le j y inv]
  refine ⟨h.1, fun u => ?_⟩
  exact (h.2 u).trans (addInside_val (hwidth _) _ u).symm

end CRTTable

end NearSquareRoot
end Computability
end OAI
