import OAI.Computability.NearSquareRoot.CRTTableArithmetic

/-! Generate one complete padded axis table by enumerating its addresses in unary. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication.Code

/-- Rotate residues by a displacement and fix all padding addresses. -/
def rotateEntry (i : (Tally × Tally) × Tally) : Tally :=
  bif Iter.small (i.2,i.1.2) then addMod (i.2,i.1.1,i.1.2) else i.2

@[fun_prop] theorem rotateEntry_poly : Poly rotateEntry := by
  let A := (Tally × Tally) × Tally
  have test := (show Poly (fun i : A => (i.2,i.1.2)) by fun_prop).compose
    (Iter.small_easy (X:=Unit) (Y:=Unit)).poly
  have value := (show Poly (fun i : A => (i.2,i.1.1,i.1.2)) by fun_prop).compose addMod_poly
  exact Poly.choose test value Easy.snd.poly

theorem rotateEntry_length (s a j : Tally) :
    (rotateEntry ((s,a),j)).length =
      if j.length < a.length then (j.length+s.length)%a.length else j.length := by
  by_cases h : j.length < a.length <;> simp [rotateEntry, Iter.small, h]

/-- Arguments are displacement, modulus and padded address count. The table has
one unary entry for each address, ordered from zero to the padded count minus one. -/
def rotation (i : Tally × Tally × Tally) : List Tally :=
  polyPush rotateEntry ((i.1,i.2.1), Iter.lineup i.2.2)

@[fun_prop] theorem rotation_poly : Poly rotation := by
  let A := Tally × Tally × Tally
  have init := (show Poly (fun i : A => (i.1,i.2.1)) by fun_prop).pair
    ((show Poly (fun i : A => i.2.2) by fun_prop).compose Iter.poly_line)
  exact init.compose (Poly.push ([],[]) [] rotateEntry_poly)

@[simp] theorem rotation_length (s a L : Tally) : (rotation (s,a,L)).length = L.length := by
  simp [rotation,polyPush]

theorem rotation_entry (s a L : Tally) (j : Fin L.length) :
    ((rotation (s,a,L))[j.val]'(by simp)).length =
      if j.val < a.length then (j.val+s.length)%a.length else j.val := by
  simp [rotation,polyPush,Iter.lineup,rotateEntry_length]

/-- Every entry is in the padded address range when the axis fits. -/
theorem rotation_entry_lt (s a L : Tally) (j : Fin L.length) (ha : a.length ≤ L.length) :
    ((rotation (s,a,L))[j.val]'(by simp)).length < L.length := by
  rw [rotation_entry]
  split
  · next hj => exact (Nat.mod_lt _ (by omega)).trans_le ha
  · exact j.isLt

/-- Displacement of the inverse translation, computed in unary. -/
def inverseOffset (p : Tally × Tally) : Tally :=
  (cutLists (rem p, p.2)).2

@[fun_prop] theorem inverseOffset_poly : Poly inverseOffset :=
  (rem_poly.pair Easy.snd.poly).compose (easy_cut (X := Unit) Easy.identity).sndCompose.poly

@[simp] theorem inverseOffset_length (s a : Tally) :
    (inverseOffset (s,a)).length = a.length - s.length % a.length := by
  simp [inverseOffset, cutLists]

private theorem rotateEntry_cancel (s t a j : Tally)
    (hzero : (s.length + t.length) % a.length = 0) :
    rotateEntry ((t,a),rotateEntry ((s,a),j)) = j := by
  apply (recover_tally _).symm.trans
  rw [rotateEntry_length, rotateEntry_length]
  by_cases hj : j.length < a.length
  · rw [ite_eq_left hj, ite_eq_left (Nat.mod_lt _ (by omega)), Nat.mod_add_mod, Nat.add_assoc,
      ← Nat.add_mod_mod, hzero, Nat.add_zero, Nat.mod_eq_of_lt hj, recover_tally]
  · simp [hj, recover_tally]

/-- The executable tables obtained by supplying `s` and its inverse offset
give mutually inverse permutations, including the fixed padding addresses. -/
theorem rotation_permutation (s a L : Tally) (ha : 0 < a.length) (hL : a.length ≤ L.length) :
    ∃ e : Equiv.Perm (Fin L.length), ∀ j,
      (e j).val = ((rotation (s,a,L))[j.val]'(by simp)).length ∧
      (e.symm j).val = ((rotation (inverseOffset (s,a),a,L))[j.val]'(by simp)).length := by
  let f (s : Tally) (j : Fin L.length) : Fin L.length :=
    ⟨(rotateEntry ((s,a),tally j.val)).length, by
      simpa only [rotateEntry_length, tally_length, rotation_entry] using rotation_entry_lt s a L j hL⟩
  have val (s : Tally) (j : Fin L.length) :
      (f s j).val = ((rotation (s,a,L))[j.val]'(by simp)).length := by
    simp only [f, rotateEntry_length, tally_length, rotation_entry]
  have inverse (s t : Tally) (h : (s.length+t.length)%a.length = 0) :
      Function.LeftInverse (f t) (f s) := by
    intro j
    apply Fin.ext
    change (rotateEntry ((t,a),tally (rotateEntry ((s,a), tally j.val)).length)).length = j.val
    rw [recover_tally, rotateEntry_cancel s t a _ h, tally_length]
  have hz : (s.length + (inverseOffset (s,a)).length) % a.length = 0 := by
    rw [inverseOffset_length, ← Nat.mod_add_mod, Nat.add_sub_of_le (Nat.mod_lt _ ha).le, Nat.mod_self]
  refine ⟨⟨f s, f (inverseOffset (s,a)), inverse _ _ hz,
    inverse _ _ (by rwa [Nat.add_comm])⟩, fun j => ⟨val _ _, val _ _⟩⟩

end CRTTable

end NearSquareRoot
end Computability
end OAI
