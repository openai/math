import OAI.Computability.NearSquareRoot.CRTTableStage

/-! # Bottom-up execution of all balanced CRT shears

The layers at a parent pair the children's rows from the leaves upwards, and
finish with the parent's own shear. Pairing equally deep rows is correct
because every operation of either subtree reads and writes only its own axes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable.Stage

variable {d : ℕ}

theorem sortedLeft (s : Stage d) : (CRTTree.left s.node).Pairwise (· < ·) :=
  s.sorted.sublist (List.take_sublist _ _)

theorem sortedRight (s : Stage d) : (CRTTree.right s.node).Pairwise (· < ·) :=
  s.sorted.sublist (List.drop_sublist _ _)

theorem capacityLeft (s : Stage d) : (CRTTree.left s.node).length ≤ 2 ^ s.remaining :=
  CRTTree.length_le_of_mem_children (by simpa only [pow_succ, mul_comm] using s.capacity)
    (by simp [CRTTree.children])

theorem capacityRight (s : Stage d) : (CRTTree.right s.node).length ≤ 2 ^ s.remaining :=
  CRTTree.length_le_of_mem_children (by simpa only [pow_succ, mul_comm] using s.capacity)
    (by simp [CRTTree.children])

/-- Depth-first node order within each row, deepest gates first across rows. -/
def layers : (depth : ℕ) → (xs : List (Fin d)) → xs.Pairwise (· < ·) →
    xs.length ≤ 2 ^ depth → List (List (Stage d))
  | 0, _, _, _ => []
  | depth + 1, xs, hs, hc =>
    let s : Stage d := ⟨xs,depth,hs,hc⟩
    List.zipWith (· ++ ·)
      (layers depth (CRTTree.left xs) s.sortedLeft s.capacityLeft)
      (layers depth (CRTTree.right xs) s.sortedRight s.capacityRight) ++ [[s]]

@[simp] theorem length_layers (depth : ℕ) (xs : List (Fin d)) (hs hc) :
    (layers depth xs hs hc).length = depth := by
  induction depth generalizing xs with
  | zero => rfl
  | succ n ih => simp [layers, ih]

variable (a : Fin d → ℕ) (E : Fin d → Type) [∀ i, NeZero (a i)]

def layerPerm : List (Stage d) → Equiv.Perm (CRT.Address a E)
  | [] => Equiv.refl _
  | s :: ss => (s.cross a E).perm.trans (layerPerm ss)

def layersPerm : List (List (Stage d)) → Equiv.Perm (CRT.Address a E)
  | [] => Equiv.refl _
  | row :: rows => (layerPerm a E row).trans (layersPerm rows)

theorem layerPerm_append (xs ys : List (Stage d)) : layerPerm a E (xs ++ ys) =
    (layerPerm a E xs).trans (layerPerm a E ys) := by
  induction xs with
  | nil => simp [layerPerm]
  | cons _ _ ih => simp [layerPerm, ih, Equiv.trans_assoc]

theorem layersPerm_append (xs ys : List (List (Stage d))) : layersPerm a E (xs ++ ys) =
    (layersPerm a E xs).trans (layersPerm a E ys) := by
  induction xs with
  | nil => simp [layersPerm]
  | cons _ _ ih => simp [layersPerm, ih, Equiv.trans_assoc]

private structure ActsOn (s : Finset (Fin d)) (f : Equiv.Perm (CRT.Address a E)) : Prop where
  outside : ∀ x i, i ∉ s → f x i = x i
  reads : ∀ x y, CRT.Agrees s x y → CRT.Agrees s (f x) (f y)

variable {a E}

omit [∀ i, NeZero (a i)] in
private theorem ActsOn.refl (s : Finset (Fin d)) : ActsOn a E s (Equiv.refl _) :=
  ⟨fun _ _ _ => rfl, fun _ _ h => h⟩

omit [∀ i, NeZero (a i)] in
private theorem ActsOn.trans {s : Finset (Fin d)} {f g : Equiv.Perm (CRT.Address a E)}
    (hf : ActsOn a E s f) (hg : ActsOn a E s g) : ActsOn a E s (f.trans g) :=
  ⟨fun x i hi => (hg.outside (f x) i hi).trans (hf.outside x i hi),
    fun x y h => hg.reads _ _ (hf.reads x y h)⟩

omit [∀ i, NeZero (a i)] in
private theorem ActsOn.mono {s t : Finset (Fin d)} {f : Equiv.Perm (CRT.Address a E)}
    (hf : ActsOn a E s f) (h : s ⊆ t) : ActsOn a E t f := by
  refine ⟨fun x i hi => hf.outside x i (fun hs => hi (h hs)), ?_⟩
  intro x y he i hi
  by_cases his : i ∈ s
  · exact hf.reads x y (fun j hj => he j (h hj)) i his
  · rw [hf.outside _ _ his, hf.outside _ _ his, he i hi]

omit [∀ i, NeZero (a i)] in
private theorem ActsOn.commute {s t : Finset (Fin d)} {f g : Equiv.Perm (CRT.Address a E)}
    (hf : ActsOn a E s f) (hg : ActsOn a E t g) (hd : Disjoint s t) : f.trans g = g.trans f := by
  ext x i
  change g (f x) i = f (g x) i
  by_cases his : i ∈ s
  · rw [hg.outside _ _ (Finset.disjoint_left.mp hd his)]
    apply hf.reads _ _ _ i his
    exact fun j hj => (hg.outside _ _ (Finset.disjoint_left.mp hd hj)).symm
  by_cases hit : i ∈ t
  · rw [hf.outside _ _ his]
    apply hg.reads _ _ _ i hit
    exact fun j hj => hf.outside _ _ (Finset.disjoint_right.mp hd hj)
  rw [hg.outside _ _ hit, hf.outside _ _ his, hf.outside _ _ his, hg.outside _ _ hit]

variable (a E)

private theorem cross_actsOn (s : Stage d) : ActsOn a E s.node.toFinset (s.cross a E).perm := by
  have hu : s.node.toFinset = (CRTTree.left s.node).toFinset ∪ (CRTTree.right s.node).toFinset := by
    rw [← List.toFinset_append, CRTTree.append_halves]
  rw [hu]
  exact ⟨(s.cross a E).outside, (s.cross a E).reads⟩

private theorem cross_symm_actsOn (s : Stage d) : ActsOn a E s.node.toFinset (s.cross a E).perm.symm := by
  have hu : s.node.toFinset = (CRTTree.left s.node).toFinset ∪ (CRTTree.right s.node).toFinset := by
    rw [← List.toFinset_append, CRTTree.append_halves]
  rw [hu]
  exact ⟨(s.cross a E).inverse_outside, (s.cross a E).inverseReads⟩

/-- A coordinate outside every gate in a row is untouched by the row. -/
theorem layerPerm_outside (row : List (Stage d)) (x : CRT.Address a E) (i : Fin d)
    (h : ∀ s ∈ row, i ∉ s.node) : layerPerm a E row x i = x i := by
  induction row generalizing x with
  | nil => rfl
  | cons s ss ih =>
    change layerPerm a E ss ((s.cross a E).perm x) i = x i
    rw [ih _ (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    exact (cross_actsOn a E s).outside x i (by simpa using h s (by simp))

theorem layerPerm_symm_outside (row : List (Stage d)) (x : CRT.Address a E) (i : Fin d)
    (h : ∀ s ∈ row, i ∉ s.node) : (layerPerm a E row).symm x i = x i := by
  induction row with
  | nil => rfl
  | cons s ss ih =>
    change (s.cross a E).perm.symm ((layerPerm a E ss).symm x) i = x i
    rw [(cross_symm_actsOn a E s).outside _ i (by simpa using h s (by simp))]
    exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- On the axes of a selected node the full row acts as that node's shear. -/
theorem layerPerm_on (row : List (Stage d)) (hd : row.Pairwise (fun s t => s.node.Disjoint t.node))
    (s : Stage d) (hs : s ∈ row) (x : CRT.Address a E) (i : Fin d) (hi : i ∈ s.node) :
    layerPerm a E row x i = (s.cross a E).perm x i := by
  induction row generalizing x with
  | nil => cases hs
  | cons t ts ih =>
    obtain ⟨dis, rest⟩ := List.pairwise_cons.mp hd
    change layerPerm a E ts ((t.cross a E).perm x) i = (s.cross a E).perm x i
    rcases List.mem_cons.mp hs with rfl | hs
    · exact layerPerm_outside a E _ _ _ (fun u hu => dis u hu hi)
    · rw [ih rest hs]
      apply (cross_actsOn a E s).reads _ _ _ i (List.mem_toFinset.mpr hi)
      intro j hj
      apply (cross_actsOn a E t).outside
      exact fun h => dis s hs (List.mem_toFinset.mp h) (List.mem_toFinset.mp hj)

theorem layerPerm_symm_on (row : List (Stage d)) (hd : row.Pairwise (fun s t => s.node.Disjoint t.node))
    (s : Stage d) (hs : s ∈ row) (x : CRT.Address a E) (i : Fin d) (hi : i ∈ s.node) :
    (layerPerm a E row).symm x i = (s.cross a E).perm.symm x i := by
  induction row with
  | nil => cases hs
  | cons t ts ih =>
    obtain ⟨dis, rest⟩ := List.pairwise_cons.mp hd
    change (t.cross a E).perm.symm ((layerPerm a E ts).symm x) i = (s.cross a E).perm.symm x i
    rcases List.mem_cons.mp hs with rfl | hs
    · apply (cross_symm_actsOn a E s).reads _ _ _ i (List.mem_toFinset.mpr hi)
      intro j hj
      exact layerPerm_symm_outside a E _ _ _ (fun u hu => dis u hu (List.mem_toFinset.mp hj))
    · rw [(cross_symm_actsOn a E t).outside _ i (fun h => dis s hs (List.mem_toFinset.mp h) hi)]
      exact ih rest hs

private theorem layersPerm_actsOn (support : Finset (Fin d)) (xs : List (List (Stage d)))
    (hx : ∀ row ∈ xs, ActsOn a E support (layerPerm a E row)) :
    ActsOn a E support (layersPerm a E xs) := by
  induction xs with
  | nil => exact ActsOn.refl _
  | cons row rows ih =>
    exact (hx row (by simp)).trans (ih (fun r hr => hx r (List.mem_cons_of_mem _ hr)))

private theorem layersPerm_zipWith {l r : Finset (Fin d)} (hd : Disjoint l r)
    (xs ys : List (List (Stage d))) (hlen : xs.length = ys.length)
    (hl : ∀ row ∈ xs, ActsOn a E l (layerPerm a E row))
    (hr : ∀ row ∈ ys, ActsOn a E r (layerPerm a E row)) :
    layersPerm a E (List.zipWith (· ++ ·) xs ys) =
      (layersPerm a E xs).trans (layersPerm a E ys) := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    simp [hy, layersPerm]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxt (row) (h : row ∈ xs) := hl row (List.mem_cons_of_mem _ h)
      have hyt (row) (h : row ∈ ys) := hr row (List.mem_cons_of_mem _ h)
      have commute := (hr y (by simp)).commute (layersPerm_actsOn a E l xs hxt) hd.symm
      simp only [List.zipWith_cons_cons, layersPerm, layerPerm_append,
        ih ys (by simpa using hlen) hxt hyt]
      rw [Equiv.trans_assoc, ← Equiv.trans_assoc (layerPerm a E y), commute]
      simp [Equiv.trans_assoc]

private theorem row_actsOn (depth : ℕ) (xs : List (Fin d)) (hs hc)
    (row : List (Stage d)) (hr : row ∈ layers depth xs hs hc) :
    ActsOn a E xs.toFinset (layerPerm a E row) := by
  induction depth generalizing xs row with
  | zero => simp [layers] at hr
  | succ depth ih =>
    let s : Stage d := ⟨xs,depth,hs,hc⟩
    change row ∈ List.zipWith (· ++ ·) (layers _ _ s.sortedLeft s.capacityLeft)
      (layers _ _ s.sortedRight s.capacityRight) ++ [[s]] at hr
    rcases List.mem_append.mp hr with h | h
    · obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h
      rw [← heq, List.getElem_zipWith, layerPerm_append]
      apply ActsOn.trans
      · apply (ih _ _ _ _ (List.getElem_mem _)).mono
        intro j hj
        exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hj))
      · apply (ih _ _ _ _ (List.getElem_mem _)).mono
        intro j hj
        exact List.mem_toFinset.mpr (List.mem_of_mem_drop (List.mem_toFinset.mp hj))
    · have eq : row = [s] := List.mem_singleton.mp h
      simpa [eq, layerPerm] using cross_actsOn a E s

/-- Evaluating the deepest row first through to the final root shear realizes
the exact recursively built permutation on all addresses, including padding. -/
theorem layersPerm_build (depth : ℕ) (xs : List (Fin d)) (hs hc) :
    layersPerm a E (layers depth xs hs hc) = (CRT.build depth xs hs hc).val.perm := by
  induction depth generalizing xs with
  | zero => rfl
  | succ depth ih =>
    let s : Stage d := ⟨xs,depth,hs,hc⟩
    change layersPerm a E (List.zipWith (· ++ ·) (layers _ _ s.sortedLeft s.capacityLeft)
      (layers _ _ s.sortedRight s.capacityRight) ++ [[s]]) = (s.parent a E).perm
    rw [layersPerm_append, layersPerm_zipWith a E s.disjoint
      (layers _ _ s.sortedLeft s.capacityLeft) (layers _ _ s.sortedRight s.capacityRight) (by simp)
      (row_actsOn a E _ _ _ _) (row_actsOn a E _ _ _ _), s.parent_perm, ih, ih]
    simp only [layersPerm, layerPerm, Equiv.trans_refl]
    rfl

/-- The complete padded CRT permutation has exactly ceiling-log-many layers
of local shears with the tree's powers-of-two partition. -/
theorem layersPerm_paddedPermutation :
    layersPerm a E (layers (Nat.clog 2 d) (List.finRange d) (List.sortedLT_finRange d).pairwise
      (by simpa using Nat.le_pow_clog (by decide : 1 < 2) d)) = CRT.paddedPermutation a E :=
  layersPerm_build a E _ _ _ _

end CRTTable.Stage

end NearSquareRoot
end Computability
end OAI
