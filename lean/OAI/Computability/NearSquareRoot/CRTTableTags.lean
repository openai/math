import OAI.Computability.NearSquareRoot.CRTBalanced

/-! # Validity flags during padded CRT routing

Rotating the valid interval of an axis preserves the distinction between
residues and padding, for all settings of the other axes. This invariant
persists through inverse routing, so the test for a valid left child can
read the current control coordinate on each axis.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRT

variable {d : ℕ} {a : Fin d → ℕ} {E : Fin d → Type}

/-- All axes retain their tag on every address. -/
def PreservesTags {l : Finset (Fin d)} (p : BlockPerm a E l) : Prop :=
  ∀ x i, (p.perm x i).isLeft = (x i).isLeft

theorem PreservesTags.inverse {l : Finset (Fin d)} {p : BlockPerm a E l} (h : PreservesTags p)
    (x : Address a E) (i : Fin d) : (p.perm.symm x i).isLeft = (x i).isLeft := by
  simpa using (h (p.perm.symm x) i).symm

private theorem translate_tag {m : ℕ} {V : Type} (v : ZMod m) (x : ZMod m ⊕ V) :
    (translate v x).isLeft = x.isLeft := by cases x <;> rfl

theorem PreservesTags.parallel {l r : Finset (Fin d)} {p : BlockPerm a E l}
    {q : BlockPerm a E r} (hp : PreservesTags p) (hq : PreservesTags q) (hd : Disjoint l r) :
    PreservesTags (p.parallel q hd) :=
  fun x i => (hq (p.perm x) i).trans (hp x i)

theorem preservesTags_shear {l r : Finset (Fin d)} (hd : Disjoint l r)
    (delta : Address a E → ∀ i, ZMod (a i)) (reads : ∀ x y, Agrees l x y → delta x = delta y) :
    PreservesTags (shear hd delta reads) := by
  intro x i
  change (if i ∈ r then translate (delta x i) (x i) else (x i)).isLeft = _
  split
  · exact translate_tag _ _
  · rfl

variable [∀ i, NeZero (a i)]

theorem PreservesTags.merge {l r : Finset (Fin d)} {p : BlockPerm a E l} {q : BlockPerm a E r}
    (hp : PreservesTags p) (hq : PreservesTags q) (hd : Disjoint l r) :
    PreservesTags (merge p q hd) :=
  fun x i => (preservesTags_shear hd (mergeOffset p) (mergeOffset_reads p) ((p.parallel q hd).perm x) i).trans
    (hp.parallel hq hd x i)

omit [∀ i, NeZero (a i)] in
private theorem preservesTags_cast {l r : Finset (Fin d)} (h : l = r)
    (s : {p : BlockPerm a E r // Computes p}) (hs : PreservesTags s.val) :
    PreservesTags ((congrArg (fun t => {p : BlockPerm a E t // Computes p}) h).mpr s).val := by
  cases h
  exact hs

theorem build_preservesTags (depth : ℕ) (xs : List (Fin d)) (hs : xs.Pairwise (· < ·))
    (hc : xs.length ≤ 2^depth) : PreservesTags (build (a := a) (E := E) depth xs hs hc).val := by
  induction depth generalizing xs with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    rw [build.eq_2]
    have h : xs.toFinset = (CRTTree.left xs).toFinset ∪ (CRTTree.right xs).toFinset := by
      rw [← List.toFinset_append, CRTTree.append_halves]
    apply preservesTags_cast h
    exact (ih _ _ _).merge (ih _ _ _) _

/-- A padded datum on any control axis forces the abstract join's offset to zero
at every target. The inverse join consequently subtracts zero as well. -/
theorem mergeOffset_zero_of_padding {l : Finset (Fin d)} {p : BlockPerm a E l}
    (hp : PreservesTags p) (x : Address a E) (h : ∃ j ∈ l, (x j).isLeft = false) (i : Fin d) :
    mergeOffset p x i = 0 := by
  obtain ⟨j, hj, hx⟩ := h
  apply ite_eq_right
  intro hall
  have hy := hall j hj
  rw [hp.inverse, hx] at hy
  contradiction

/-- Both directions of a controlled CRT layer fix the whole address as soon
as the current left control contains a padding value. -/
theorem shear_mergeOffset_invalid {l r : Finset (Fin d)} {p : BlockPerm a E l}
    (hp : PreservesTags p) (hd : Disjoint l r) (x : Address a E)
    (h : ∃ j ∈ l, (x j).isLeft = false) :
    let cross := shear hd (mergeOffset p) (mergeOffset_reads p)
    cross.perm x = x ∧ cross.perm.symm x = x := by
  have hz := mergeOffset_zero_of_padding hp x h
  have zero (i : Fin d) : translate (0 : ZMod (a i)) (x i) = x i := by
    cases x i <;> simp [translate]
  have hforward : (shear hd (mergeOffset p) (mergeOffset_reads p)).perm x = x := by
    funext i
    change (if i ∈ r then translate (mergeOffset p x i) (x i) else x i) = x i
    rw [hz, zero, ite_self]
  exact ⟨hforward, (Equiv.symm_apply_eq _).mpr hforward.symm⟩

end CRT

end NearSquareRoot
end Computability
end OAI
