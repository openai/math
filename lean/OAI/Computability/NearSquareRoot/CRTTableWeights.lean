import OAI.Computability.NearSquareRoot.CRTTableSemantics
import OAI.Computability.NearSquareRoot.CRTTableInterval
import OAI.Computability.NearSquareRoot.CRTRouting

/-! # CRT offsets read from a generated triangular table

The substitution loop consumes one row coefficient for each left-child
digit. Its row can also contain later coefficients for other axes in the
same node. The sum formed from precisely the consumed entries is the scaled
left-child rank defining the abstract rotation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

variable {d : ℕ} (a : Fin d → ℕ)

/-- A row with the scaled prefix coefficients evaluates to the scaled
partial mixed-radix rank. Only the entries indexed by the control list
affect the result, even if the row has a longer coefficient queue. -/
theorem rowDot_eq_weight (i : Fin d) (t : Fin d → ℕ)
    (js : List (Fin d)) (cs : List Tally) (hj : js.Nodup)
    (hc : ∀ (k : ℕ) (hk : k < js.length),
      (((cs[k]?.getD []).length : ℕ) : ZMod (a i)) =
        CRT.weight a i * (CRT.«prefix» a js[k] : ZMod (a i))) :
    (rowDot (js.map (fun j => tally (t j))) cs : ZMod (a i)) =
      CRT.weight a i * ((∑ j ∈ js.toFinset, CRT.«prefix» a j * t j : ℕ) : ZMod (a i)) := by
  induction js generalizing cs with
  | nil => simp [rowDot]
  | cons j js ih =>
    have hn : j ∉ js.toFinset := by simpa using (List.nodup_cons.mp hj).1
    have h₀ : (((cs.headD []).length : ℕ) : ZMod (a i)) =
        CRT.weight a i * (CRT.«prefix» a j : ZMod (a i)) := by
      have h := hc 0 (by simp)
      cases cs <;> exact h
    have ht := ih cs.tail (List.nodup_cons.mp hj).2 (fun k hk => by
      have h := hc (k + 1) (by simpa using hk)
      cases cs <;> exact h)
    simp only [List.map_cons, rowDot, tally_length, List.toFinset_cons, Finset.sum_insert hn,
      Nat.cast_add, Nat.cast_mul, h₀, ht, mul_add]
    ring

/-- The queue read directly from the full serialized coefficient table
computes the rotation on any duplicate-free selection of earlier axes. -/
theorem rowDot_generated (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (i : Fin d) (hm : 0 < a i) (t : Fin d → ℕ)
    (js : List (Fin d)) (hj : js.Nodup) (horder : ∀ j ∈ js, j < i) :
    let axes := List.ofFn fun j => tally (a j)
    (rowDot (js.map (fun j => tally (t j)))
      (js.map (fun j => ((coefficients axes)[i.val]?.getD [])[j.val]?.getD [])) : ZMod (a i)) =
      CRT.weight a i * ((∑ j ∈ js.toFinset, CRT.«prefix» a j * t j : ℕ) : ZMod (a i)) := by
  dsimp only
  apply rowDot_eq_weight _ _ _ js _ hj
  intro k hk
  rw [List.getElem?_eq_getElem (by simpa using hk), Option.getD_some, List.getElem_map]
  exact coefficientAt_weight a hcop (horder _ (List.getElem_mem hk)) hm

/-- A node builds its table from just the consecutive local moduli. The physical
queue of coefficients for target axis `base + i` starts with precisely the
global coefficients of the control prefix. -/
theorem rowDot_interval_weight (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    (base width i : ℕ) (hrow : i < width) (hi : base + i < d)
    (hm : 0 < a ⟨base + i, hi⟩) (js : List (Fin d)) (t : Fin d → ℕ)
    (hlen : js.length ≤ i) (hpos : ∀ (k : ℕ) (hk : k < js.length), js[k].val = base + k) :
    let block := ((List.ofFn (fun j => tally (a j))).drop base).take width
    (rowDot (js.map (fun j => tally (t j))) ((coefficients block)[i]?.getD []) :
      ZMod (a ⟨base + i, hi⟩)) = CRT.weight a ⟨base + i, hi⟩ *
        ((∑ j ∈ js.toFinset, CRT.«prefix» a j * t j : ℕ) : ZMod (a ⟨base + i, hi⟩)) := by
  dsimp only
  apply rowDot_eq_weight
  · apply List.nodup_iff_injective_getElem.mpr
    intro u v he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change js[u.val].val = js[v.val].val at hv
    rw [hpos u u.isLt, hpos v v.isLt] at hv
    omega
  · intro k hk
    have hki : k < i := hk.trans_le hlen
    have he : js[k] = (⟨base + k, by omega⟩ : Fin d) := Fin.ext (hpos k hk)
    rw [he]
    exact coefficientAt_interval_weight a hcop base width hrow hi hki hm

/-- The value added by the two-child CRT merge is exactly the residue of the
row evaluated on its decoded original control digits. -/
theorem rowDot_eq_mergeOffset [∀ j, NeZero (a j)] {E : Fin d → Type}
    (js : List (Fin d)) {r : Finset (Fin d)}
    (p : CRT.BlockPerm a E js.toFinset) (q : CRT.BlockPerm a E r)
    (hd : Disjoint js.toFinset r) (x : CRT.Address a E) (t : ∀ j, ZMod (a j))
    (hv : ∀ j ∈ js.toFinset, x j = Sum.inl (t j)) (i : Fin d)
    (cs : List Tally) (hj : js.Nodup)
    (hc : ∀ (k : ℕ) (hk : k < js.length),
      (((cs[k]?.getD []).length : ℕ) : ZMod (a i)) =
        CRT.weight a i * (CRT.«prefix» a js[k] : ZMod (a i))) :
    (rowDot (js.map (fun j => tally (t j).val)) cs : ZMod (a i)) =
      CRT.mergeOffset p ((p.parallel q hd).perm x) i := by
  rw [CRT.mergeOffset_eq p q hd x t hv]
  exact rowDot_eq_weight a i (fun j => (t j).val) js cs hj hc

end CRTTable

end NearSquareRoot
end Computability
end OAI
