import OAI.Computability.NearSquareRoot.CRTTableMerge

/-! # Reading a physical CRT table at the current target coordinate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

private theorem coordinate_translated {m L : ℕ} [NeZero m] {V : Type}
    (pad : V → Fin (L-m)) (v : ZMod m ⊕ V) (δ : ZMod m) (inv : Bool) :
    coordinate pad ((bif inv then (CRT.translate δ).symm else CRT.translate δ) v) =
      if coordinate pad v < m then
        ((coordinate pad v : ZMod m) + (bif inv then -δ else δ)).val
      else coordinate pad v := by
  cases inv <;> cases v with
  | inl r => simp [CRT.translate, coordinate, ZMod.val_lt]
  | inr e => simp [CRT.translate, coordinate]

variable {d : ℕ} (a : Fin d → ℕ) {E : Fin d → Type}

/-- Reading the stored unary output index at the current padded target
coordinate implements the actual forward or reverse shear of the CRT circuit. -/
theorem nodeTables_apply_shear [∀ j, NeZero (a j)] (w : Fin d → ℕ)
    (pad : ∀ j, E j → Fin (2^w j - a j))
    (hwidth : ∀ j, a j ≤ 2^w j) (hdense : ∀ j, 2^w j ≤ 2*a j)
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (base : ℕ)
    (js rs : List (Fin d)) (hpos : ∀ (u : ℕ) (hu : u < (js ++ rs).length),
      (js ++ rs)[u].val = base + u)
    (p : CRT.BlockPerm a E js.toFinset) (hp : CRT.Computes p) (tp : CRT.PreservesTags p)
    (q : CRT.BlockPerm a E rs.toFinset) (tq : CRT.PreservesTags q)
    (hd : Disjoint js.toFinset rs.toFinset) (y : CRT.Address a E) (inv : Bool)
    (i : Fin rs.length) :
    let tables := nodeTables (paddedMergeQuery a w pad js rs y inv)
    let cross := CRT.shear hd (CRT.mergeOffset p) (CRT.mergeOffset_reads p)
    let g := rs[i.val]
    let v := coordinate (pad g) (y g)
    let tab := tables[i.val]?.getD []
    (tab[v]?.getD []).length =
      coordinate (pad g) (((bif inv then cross.perm.symm else cross.perm) y) g) := by
  let g := rs[i.val]
  have hg : g ∈ rs.toFinset := List.mem_toFinset.mpr (List.getElem_mem i.isLt)
  let val := coordinate (pad g) (y g)
  have hv : val < 2^w g := by
    dsimp only [val]
    cases hy : y g with
    | inl v => exact (ZMod.val_lt _).trans_le (hwidth g)
    | inr e =>
      change a g + (pad g e).val < 2^w g
      have := (pad g e).isLt
      omega
  let j : Fin (2^w g) := ⟨val,hv⟩
  have entry := (((nodeTables_paddedMerge a w pad hwidth hdense hcop base js rs hpos
    p hp tp q tq hd y inv).2 i).2 j)
  have trans := coordinate_translated (pad g) (y g) (CRT.mergeOffset p y g) inv
  refine entry.trans (trans.symm.trans ?_)
  cases inv <;> simp [CRT.shear, hg, g] at *

end CRTTable

end NearSquareRoot
end Computability
end OAI
