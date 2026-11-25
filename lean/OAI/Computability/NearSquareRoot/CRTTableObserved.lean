import OAI.Computability.NearSquareRoot.CRTTableWeights
import OAI.Computability.NearSquareRoot.CRTTableSubstitution
import OAI.Computability.NearSquareRoot.CRTTableAxisList

/-! # Triangular substitution on the observed left-child output

The local row number and the column number are relative to the beginning of
the node. Their moduli and rank weights come from the same positions in the
global axis list. This identifies the substitution equations with the
coordinates actually produced by the left child's CRT permutation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

variable {d : ℕ} (a : Fin d → ℕ)

/-- Every prefix contribution formed by the local coefficient generator is the
weighted rank of exactly that prefix of the control list. The row index may
belong to either child. -/
theorem contribution_eq_partialRank
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (base : ℕ)
    (js rs : List (Fin d)) (hpos : ∀ (u : ℕ) (hu : u < (js ++ rs).length),
      (js ++ rs)[u].val = base + u)
    (t : ∀ j, ZMod (a j)) (i : Fin (js ++ rs).length) (k : ℕ)
    (hk : k ≤ js.length) (hki : k ≤ i.val) (hm : 0 < a (js ++ rs)[i.val]) :
    (contribution (js.map (fun j => tally (t j).val)) ((js ++ rs).map (fun j => tally (a j)))
      i.val k : ZMod (a (js ++ rs)[i.val])) = CRT.weight a (js ++ rs)[i.val] *
        ((CRT.partialRank a (js.take k).toFinset t : ℕ) : ZMod (a (js ++ rs)[i.val])) := by
  let node := js ++ rs
  let block := (js ++ rs).map (fun j => tally (a j))
  have hi : i.val < block.length := by simpa only [block, List.length_map] using i.isLt
  have hb : base + i.val < d := by rw [← hpos _ i.isLt]; exact (js ++ rs)[i.val].isLt
  have he : (js ++ rs)[i.val] = (⟨base + i.val, hb⟩ : Fin d) := Fin.ext (hpos _ _)
  have hp (u : ℕ) (hu : u < (js.take k).length) : (js.take k)[u].val = base + u := by
    have hull : u < js.length := by
      simp only [List.length_take] at hu
      omega
    rw [List.getElem_take]
    exact (congrArg Fin.val (List.getElem_append_left (bs := rs) hull)).symm.trans
      (hpos u (by simp; omega))
  have hdot := rowDot_interval_weight a hcop base node.length i.val i.isLt hb (he ▸ hm)
    (js.take k) (fun j => (t j).val) (by simp; omega) hp
  have hl : block = ((List.ofFn (fun j => tally (a j))).drop base).take node.length :=
    axisSlice a node base hpos
  dsimp only at hdot
  rw [← hl, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some, List.map_take] at hdot
  rw [← rowDot_coefficients_take _ _ _ _ hi (by simpa using hk)]
  rw [he]
  exact hdot

/-- The control field decoder can supply the residues present at any address
`y` agreeing with the child output. Spectator and target axes need no
validity hypotheses. -/
theorem observed_of_computes [∀ j, NeZero (a j)] {E : Fin d → Type}
    (hcop : Pairwise (fun i j => (a i).Coprime (a j))) (base : ℕ)
    (js rs : List (Fin d)) (hpos : ∀ (u : ℕ) (hu : u < (js ++ rs).length),
      (js ++ rs)[u].val = base + u)
    (width : Fin d → Tally) (p : CRT.BlockPerm a E js.toFinset) (hp : CRT.Computes p)
    (x y : CRT.Address a E) (t : ∀ j, ZMod (a j))
    (hvalid : ∀ j ∈ js.toFinset, x j = Sum.inl (t j))
    (hview : CRT.Agrees js.toFinset y (p.perm x)) :
    Observed (js.map (fun j => (width j, tally (a j)))) (rs.map (fun j => (width j, tally (a j))))
      (js.map (fun j => tally ((y j).elim ZMod.val (fun _ => 0))))
      (js.map (fun j => tally (t j).val)) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  have hi : i.val < js.length := by simpa using i.isLt
  let u := js[i.val]
  have hu : u ∈ js.toFinset := List.mem_toFinset.mpr (List.getElem_mem hi)
  have hglobal : ∀ (k : ℕ) (hk : k < js.length), js[k].val = base + k := by
    intro k hk
    exact (congrArg Fin.val (List.getElem_append_left (bs := rs) hk)).symm.trans
      (hpos k (by simp; omega))
  have hy : y u = Sum.inl (t u + CRT.weight a u *
      (CRT.partialRank a (js.toFinset.filter (· < u)) t : ZMod (a u))) :=
    (hview u hu).trans (hp x t hvalid u hu)
  let s : Fin (js ++ rs).length := ⟨i.val, by simp; omega⟩
  have hv : 0 < a u := Nat.pos_of_ne_zero (NeZero.ne _)
  have hc := contribution_eq_partialRank a hcop base js rs hpos t s i.val hi.le le_rfl
    (by simpa only [s, List.getElem_append_left (bs := rs) hi] using hv)
  have hpre := axisPrefix js base hglobal (⟨i.val,hi⟩ : Fin js.length)
  simp only [s, hpre] at hc
  have hueq : (js ++ rs)[i.val] = u := List.getElem_append_left hi
  rw [hueq] at hc
  simp only [List.getElem_map, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    Option.getD_some, tally_length, localAxes, ← List.map_append, List.map_map, Function.comp_def]
  change _ < a u ∧ _ < a u ∧ _ ≡ _ [MOD a u]
  rw [hy]
  simp only [Sum.elim_inl]
  refine ⟨ZMod.val_lt _, ZMod.val_lt _, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  rw [ZMod.natCast_zmod_val, Nat.cast_add, ZMod.natCast_zmod_val]
  exact congrArg (t u + ·) hc.symm

end CRTTable

end NearSquareRoot
end Computability
end OAI
