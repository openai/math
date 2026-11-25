import OAI.Computability.NearSquareRoot.CRTTableSemantics
import OAI.Computability.NearSquareRoot.CRTTableInputRows
import OAI.Computability.NearSquareRoot.CRTTableCoefficients

/-! # CRT offsets from the physically prepared rows

The program below is the row initializer followed by the triangular elimination
program. Its input consists of a descriptor for each axis, the observed residues
on the left child, and the coefficient table calculated from the axis moduli.
The correctness statement specifies each returned right-hand residue modulo
the target modulus.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code
open scoped BigOperators

/-- Contribution of the first `k` digits to the scaled residue on local axis `i`. -/
def contribution (xs : List Tally) (axes : List Tally) (i k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, (xs[j]?.getD []).length * coefficientAt axes i j

private theorem rowDot_get (xs cs : List Tally) :
    rowDot xs cs = ∑ j ∈ Finset.range xs.length,
      (xs[j]?.getD []).length * (cs[j]?.getD []).length := by
  induction xs generalizing cs with
  | nil => simp [rowDot]
  | cons x xs ih =>
    rw [rowDot, List.length_cons, Finset.sum_range_succ', ih]
    cases cs <;> simp [Nat.add_comm]

/-- The coefficient reader and physical coefficient queues agree even if
only a prefix of the queue is consumed at this level of the merge tree. -/
theorem rowDot_coefficients_take (xs axes : List Tally) (i k : ℕ)
    (hi : i < axes.length) (hk : k ≤ xs.length) :
    rowDot (xs.take k) ((coefficients axes)[i]'(by simpa using hi)) =
      contribution xs axes i k := by
  rw [rowDot_get, contribution, List.length_take, Nat.min_eq_left hk]
  apply Finset.sum_congr rfl
  intro j hj
  rw [List.getElem?_take_of_lt (Finset.mem_range.mp hj)]
  simp only [coefficientAt, List.getElem?_eq_getElem (show i < (coefficients axes).length by
    simpa using hi), Option.getD_some]

/-- Standard mixed-radix data for one local node, with the left child first. -/
abbrev localAxes (l r : List (Tally × Tally)) := (l ++ r).map Prod.snd

abbrev initializedRows (l r : List (Tally × Tally)) (v : List Tally) :=
  rawRows (l, r, v, coefficients (localAxes l r))

/-- Conditions on valid original digits `xs` and the left-child output `v`. -/
def Observed (l r : List (Tally × Tally)) (v xs : List Tally) : Prop :=
  v.length = l.length ∧ xs.length = l.length ∧
    ∀ j : Fin l.length,
      let m := l[j.val].2.length
      (v[j.val]?.getD []).length < m ∧ (xs[j.val]?.getD []).length < m ∧
        (v[j.val]?.getD []).length ≡
          (xs[j.val]?.getD []).length + contribution xs (localAxes l r) j.val j.val [MOD m]

theorem encodes_initialized (l r : List (Tally × Tally)) (v xs : List Tally)
    (h : Observed l r v xs) :
    Encodes [] ((initializedRows l r v).take l.length) xs := by
  obtain ⟨hv,hx,hs⟩ := h
  have hc : (coefficients (localAxes l r)).length = l.length + r.length := by simp
  have hl := rawRows_length l r v _ hv hc
  have htake : ((initializedRows l r v).take l.length).length = l.length := by
    simp only [List.length_take, hl, Nat.min_eq_left (Nat.le_add_right ..)]
  apply encodes_of_get _ _ _ (htake.trans hx.symm)
  intro j hj hjx
  have hjl : j < l.length := by omega
  have hja : j < (localAxes l r).length := by simp; omega
  have hq := hs ⟨j,hjl⟩
  simp only [List.getElem?_eq_getElem (show j < v.length by omega),
    List.getElem?_eq_getElem hjx, Option.getD_some] at hq
  simp only [List.getElem_take, rawRows_get_control l r v _ hv hc ⟨j,hjl⟩, List.nil_append,
    rowDot_coefficients_take xs (localAxes l r) j j hja hjx.le]
  exact hq

/-- The actual right-child output after elimination at one complete control
setting. The unary offset is canonical in the target modulus and represents
the negative weighted sum of the recovered left digits. -/
theorem substitution_targets (l r : List (Tally × Tally)) (v xs : List Tally)
    (h : Observed l r v xs) (hm : ∀ i : Fin r.length, 0 < r[i.val].2.length) :
    let out := residuals (ruler l, initializedRows l r v)
    out.length = r.length ∧
      ∀ i : Fin r.length,
        let m := r[i.val].2
        let acc := out[i.val]?.getD ([], [], [])
        acc.1 = m ∧ acc.2.1.length < m.length ∧
          (acc.2.1.length : ZMod m.length) =
            -(contribution xs (localAxes l r) (l.length + i.val) l.length : ℕ) := by
  dsimp only
  have hv := h.1
  have hx := h.2.1
  let rows := initializedRows l r v
  have hc : (coefficients (localAxes l r)).length = l.length + r.length := by simp
  have hl : rows.length = l.length + r.length := rawRows_length _ _ _ _ hv hc
  have hout : residuals (ruler l, rows) = (rows.drop l.length).map (reduceRow xs) := by
    conv_lhs => rw [← List.take_append_drop l.length rows]
    exact residuals_encoded _ (by simpa using hx.symm) (encodes_initialized l r v xs h)
  change (residuals (ruler l, rows)).length = _ ∧ _
  rw [hout]
  refine ⟨by simp [hl], ?_⟩
  intro i
  let pos := l.length + i.val
  have hloc : pos < (localAxes l r).length := by simp [pos]
  have hri : i.val < (rows.drop l.length).length := by simp [hl]
  have hentry := rawRows_get_target l r v (coefficients (localAxes l r)) hv hc i
  change rows[pos]'(by unfold pos; omega) = _ at hentry
  have ho : ((rows.drop l.length).map (reduceRow xs))[i.val]?.getD ([], [], []) =
      reduceRow xs (r[i.val].2, [], (coefficients (localAxes l r))[pos]'(by simpa using hloc)) := by
    simp only [List.getElem?_eq_getElem (by simpa using hri :
      i.val < ((rows.drop l.length).map (reduceRow xs)).length),
      Option.getD_some, List.getElem_map, List.getElem_drop]
    exact congrArg (reduceRow xs) hentry
  rw [ho]
  refine ⟨reduceRow_modulus .., reduceRow_value_lt _ _ (hm i), ?_⟩
  rw [reduceRow_negative _ _ _ (hm i)]
  congr 2
  have he := rowDot_coefficients_take xs (localAxes l r) pos l.length hloc hx.ge
  simpa [show xs.take l.length = xs by simp [← hx]] using he

end CRTTable

end NearSquareRoot
end Computability
end OAI
