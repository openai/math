import OAI.Computability.NearSquareRoot.CRTTableArithmetic
import OAI.Computability.NearSquareRoot.CRTIsomorphism

/-! # Bounded setup for the triangular CRT coefficient table

The stack program builds row `i` in ascending column order. A column
uses a modular fold on the radices between its index and `i`. Every
intermediate residue fits in the unary modulus delimiter, including on
malformed input. Prefix place values appear only in the correctness proof.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRT

/-- A product of earlier radices is a unit modulo the current radix. -/
theorem window_coprime (l : List ℕ) (hl : l.Pairwise Nat.Coprime)
    {i j : ℕ} (hi : i < l.length) :
    (((l.take i).drop j).prod).Coprime l[i] := by
  apply Nat.coprime_list_prod_left_iff.mpr
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_drop hx)
  rw [List.getElem_take]
  simp only [List.length_take, min_eq_left hi.le] at hk
  exact List.pairwise_iff_getElem.mp hl k i (hk.trans hi) hi hk

/-- Inverting the intervening radices gives the ratio of the two place values,
even when the place values themselves are much larger than the modulus. -/
theorem window_inverse_prefix (l : List ℕ) {j i u m : ℕ} (hji : j ≤ i)
    (hu : u * ((l.take i).drop j).prod ≡ 1 [MOD m]) :
    u * (l.take i).prod ≡ (l.take j).prod [MOD m] := by
  have h := congrArg List.prod (List.take_append_drop j (l.take i))
  simp only [List.prod_append, List.take_take, min_eq_left hji] at h
  rw [← h]
  simpa only [mul_left_comm, mul_one] using hu.mul_left (l.take j).prod

/-- The serialized radices are in the same order as the CRT coefficient formulas. -/
theorem take_ofFn_prod_prefix {d : ℕ} (a : Fin d → ℕ) (i : Fin d) :
    ((List.ofFn a).take i.val).prod = «prefix» a i := by
  have h : (List.ofFn a).take i.val = List.ofFn (fun j : Fin i.val => a (Fin.castLE i.isLt.le j)) := by
    apply List.ext_getElem
    · simp
    · intro k hk hk'
      simp only [List.getElem_take, List.getElem_ofFn]
      rfl
  rw [h, List.prod_ofFn, «prefix»]
  symm
  exact Finset.prod_bij' (fun (j : Fin d) hj => (⟨j.val, show j < i from Finset.mem_Iio.mp hj⟩ : Fin i.val))
    (fun j _ => Fin.castLE i.isLt.le j)
    (fun _ _ => Finset.mem_univ _) (fun j _ => Finset.mem_Iio.mpr j.isLt)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)


/-- The bounded-window inverse decodes to the scaled coefficient used by the router. -/
theorem window_inverse_eq_weight_mul {d : ℕ} (a : Fin d → ℕ)
    (ha : Pairwise (fun i j => (a i).Coprime (a j))) {i j : Fin d} (hji : j ≤ i)
    {u : ℕ} (hu : u * (((List.ofFn a).take i.val).drop j.val).prod ≡ 1 [MOD a i]) :
    (u : ZMod (a i)) = weight a i * («prefix» a j : ZMod (a i)) := by
  have h := window_inverse_prefix _ (show j.val ≤ i.val from hji) hu
  rw [take_ofFn_prod_prefix a i, take_ofFn_prod_prefix a j] at h
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  rw [Nat.cast_mul] at hc
  rw [← hc, mul_left_comm, weight_mul_prefix a ha, mul_one]

end CRT

namespace CRTTable
open IntegerMultiplication.Code


private def accumulate (v : (Tally × Tally) × Tally) : Tally × Tally :=
  (v.1.1, (cutLists (v.1.1, mulMod (v.1.2, v.2, v.1.1))).1)

private def residue (p : Tally × List Tally) : Tally :=
  (p.2.foldl (fun s y => accumulate (s,y)) (p.1, tally 1)).2

private theorem residue_poly : Poly (residue) := by
  have hm : Poly (fun v : (Tally × Tally) × Tally => mulMod (v.1.2,v.2,v.1.1)) := by
    exact (show Poly (fun v : (Tally × Tally) × Tally => (v.1.2,v.2,v.1.1)) by fun_prop).compose mulMod_poly
  have ha : Poly (accumulate) := by
    have h := (show Easy (cutLists (X := Unit)) from easy_cut Easy.identity).poly
    exact Poly.fstCompose (Poly.fstCompose Poly.identity) |>.pair
      (((Poly.fstCompose (Poly.fstCompose Poly.identity)).pair hm).compose h.fstCompose)
  have hfold := Poly.fold_left ha 2 1 (by
    rintro ⟨z,m,r⟩ l _
    have hb (l : List Tally) (m r : Tally) :
        (l.foldl (fun s y => accumulate (s,y)) (m,r)).1 = m ∧
        (l.foldl (fun s y => accumulate (s,y)) (m,r)).2.length ≤ max m.length r.length := by
      induction l generalizing r with
      | nil => exact ⟨rfl,Nat.le_max_right _ _⟩
      | cons y l ih =>
        change _ ∧ (l.foldl _ (m,(cutLists (m,mulMod (r,y,m))).1)).2.length ≤ _
        obtain ⟨he,hb⟩ := ih (cutLists (m,mulMod (r,y,m))).1
        exact ⟨he, hb.trans (max_le (Nat.le_max_left _ _) (by simp [cutLists]))⟩
    obtain ⟨hm,hr⟩ := hb l m r
    rw [size_prod,hm]
    simp only [size_prod,size_tally,pow_one]
    omega)
  exact (show Poly (fun p : Tally × List Tally => (p.2,p.1,tally 1)) by fun_prop).compose hfold.sndCompose

private theorem residue_correct
    (m : Tally) (l : List Tally) (hm : 0 < m.length) :
    (residue (m,l)).length ≡ (l.map List.length).prod [MOD m.length] := by
  have he (v z : Tally) :
      (accumulate ((m,v),z)).2.length ≡ v.length*z.length [MOD m.length] := by
    simp [accumulate,cutLists,mulMod_length,Nat.min_eq_right (Nat.mod_lt _ hm).le,Nat.ModEq]
  have aux (s : Tally) (q : List Tally) :
      (q.foldl (fun v z => accumulate (v,z)) (m,s)).2.length ≡
        s.length * (q.map List.length).prod [MOD m.length] := by
    induction q generalizing s with
    | nil => simp [Nat.ModEq]
    | cons y q ih =>
      change (q.foldl _ (m,(accumulate ((m,s),y)).2)).2.length ≡ _ [MOD _]
      exact (ih _).trans (by simpa [mul_assoc] using (he s y).mul_right (q.map List.length).prod)
  simpa [residue] using aux (tally 1) l

/-- The shared context consists of the target modulus and its preceding axes.
A column index is supplied in unary. -/
private def entry (p : (Tally × List Tally) × Tally) : Tally :=
  inverse (residue (p.1.1, (cutLists (p.2, p.1.2)).2), p.1.1)

private theorem entry_poly :
    Poly (entry) := by
  have hcut : Poly (fun p : (Tally × List Tally) × Tally => (cutLists (p.2,p.1.2)).2) :=
    ((easy_cut (X := Tally) (by fun_prop)).sndCompose).poly
  have hm : Poly (fun p : (Tally × List Tally) × Tally => p.1.1) := by fun_prop
  exact (((hm.pair hcut).compose (residue_poly)).pair hm).compose inverse_poly

private def row (p : List Tally × Tally) : List Tally :=
  polyPush (entry)
    ((Iter.pick [] p, (cutLists (p.2,p.1)).1), Iter.lineup p.2)

private theorem row_poly :
    Poly (row) := by
  have hcut : Poly (fun p : List Tally × Tally => (cutLists (p.2,p.1)).1) :=
    ((easy_cut (X := Tally) (by fun_prop)).fstCompose).poly
  have h := (Iter.facile ([] : Tally)).poly
  exact (((h.pair hcut).pair (Easy.snd.poly.compose Iter.poly_line))).compose
    (Poly.push ([],[]) [] (entry_poly))

/-- Generate the entire lower-triangular table in physical axis order. -/
def coefficients (axes : List Tally) : List (List Tally) :=
  polyPush (row) (axes, Iter.lineup (ruler axes))

theorem coefficients_poly :
    Poly (coefficients) := by
  exact (Poly.identity.pair ((Easy.ruler Easy.identity).poly.compose Iter.poly_line)).compose
    (Poly.push [] [] (row_poly))

@[simp] theorem coefficients_length (axes : List Tally) :
    (coefficients axes).length = axes.length := by simp [coefficients,polyPush]

private theorem coefficients_row (axes : List Tally) (i : ℕ) (hi : i < axes.length) :
    (coefficients axes)[i]'(by simpa using hi) =
      ((Iter.lineup (tally i)).map fun j =>
        inverse (residue (axes[i],(axes.take i).drop j.length),axes[i])) := by
  simp [coefficients,polyPush,row,entry,Iter.lineup,cutLists,Iter.pick,Function.comp_def]

@[simp] theorem row_length (axes : List Tally) (i : ℕ) (hi : i < axes.length) :
    ((coefficients axes)[i]'(by simpa using hi)).length = i := by
  rw [coefficients_row axes i hi]
  simp

/-- Read the length of a coefficient in the encoded, ascending triangular array. -/
def coefficientAt (axes : List Tally) (i j : ℕ) : ℕ :=
  (((coefficients axes)[i]?.getD [])[j]?.getD []).length

private theorem coefficientAt_eq (axes : List Tally) {i j : ℕ}
    (hi : i < axes.length) (hj : j < i) :
    coefficientAt axes i j =
      (inverse (residue (axes[i], (axes.take i).drop j),axes[i])).length := by
  unfold coefficientAt
  rw [List.getElem?_eq_getElem (l := coefficients axes) (i := i) (by simpa using hi)]
  simp only [Option.getD_some,coefficients_row axes i hi]
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simp [Iter.lineup]

/-- Each serialized coefficient is a bounded inverse of the intervening radices. -/
theorem coefficientAt_window
    (axes : List Tally) (hcop : (axes.map List.length).Pairwise Nat.Coprime)
    {i j : ℕ} (hi : i < axes.length) (hj : j < i) (hm : 0 < axes[i].length) :
    coefficientAt axes i j < axes[i].length ∧
    coefficientAt axes i j *
        (((axes.map List.length).take i).drop j).prod ≡ 1 [MOD axes[i].length] := by
  rw [coefficientAt_eq axes hi hj]
  let v := residue (axes[i],(axes.take i).drop j)
  have hv : v.length ≡ (((axes.map List.length).take i).drop j).prod [MOD axes[i].length] := by
    simpa only [List.map_drop, List.map_take] using residue_correct axes[i] ((axes.take i).drop j) hm
  have hcop' : ((((axes.map List.length).take i).drop j).prod).Coprime axes[i].length := by
    rw [List.getElem_map_rev List.length (h := hi)]
    exact (CRT.window_coprime (axes.map List.length) hcop (j := j) (by simpa using hi : i < (axes.map List.length).length))
  have ⟨hbound,hs⟩ := inverse_spec v axes[i] hm (show v.length.Coprime axes[i].length from hv.gcd_eq.trans hcop')
  refine ⟨hbound,?_⟩
  exact (hv.symm.mul_left _).trans (by simpa only [Nat.ModEq,Nat.mul_comm] using hs)

/-- Exact coefficient ratio in terms of prefix place values. -/
theorem coefficientAt_prefix
    (axes : List Tally) (hcop : (axes.map List.length).Pairwise Nat.Coprime)
    {i j : ℕ} (hi : i < axes.length) (hj : j < i) (hm : 0 < axes[i].length) :
    coefficientAt axes i j * ((axes.map List.length).take i).prod ≡
      ((axes.map List.length).take j).prod [MOD axes[i].length] :=
  CRT.window_inverse_prefix _ hj.le (coefficientAt_window axes hcop hi hj hm).2

/-- On the serialized axes, the physical row entry has the exact scaled
residue value used by the abstract CRT permutation. -/
theorem coefficientAt_weight
    {d : ℕ} (a : Fin d → ℕ) (hcop : Pairwise (fun i j => (a i).Coprime (a j)))
    {i j : Fin d} (hji : j < i) (hm : 0 < a i) :
    (coefficientAt (List.ofFn (fun t => tally (a t))) i.val j.val : ZMod (a i)) =
      CRT.weight a i * (CRT.«prefix» a j : ZMod (a i)) := by
  let axes := List.ofFn (fun t => tally (a t))
  have ha : axes.map List.length = List.ofFn a := by simp [axes,Function.comp_def]
  have hi : i.val < axes.length := by simp [axes]
  have hm' : axes[i.val].length = a i := by simp [axes]
  have hc : (axes.map List.length).Pairwise Nat.Coprime := by
    rw [ha,List.pairwise_iff_getElem]
    intro s t hs ht hst
    change _ < (List.ofFn a).length at hs ht
    simp only [List.getElem_ofFn]
    apply hcop
    intro e
    exact hst.ne (congrArg Fin.val e)
  have hw := (coefficientAt_window axes hc hi hji (hm' ▸ hm)).2
  rw [ha,hm'] at hw
  exact CRT.window_inverse_eq_weight_mul a hcop hji.le hw

end CRTTable

end NearSquareRoot
end Computability
end OAI
