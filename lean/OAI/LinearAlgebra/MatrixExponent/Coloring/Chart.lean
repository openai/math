import OAI.LinearAlgebra.MatrixExponent.Coloring.Formula

/-!
# Three-stage routing on a packed product

At each end of an edge, add the edge colour to the fixed offset of
its fiber. Proper colouring makes both assignments permutations.
Composing one with the inverse of the other moves between fibers
while preserving colour.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {h d : ℕ} {X A : Type} [Fintype X] [Fintype A]

private def pack (hs : Fintype.card A * d ≤ 2 ^ h) : A × Fin d ↪ B h :=
  (((Fintype.equivFin A).prodCongr (.refl _)).trans finProdFinEquiv).toEmbedding.trans
    (Fin.castLEEmb hs)

private def offset (hs : Fintype.card A * d ≤ 2 ^ h) (hd : 0 < d) : A ↪ B h :=
  ⟨fun i => pack hs (i, ⟨0, hd⟩), fun _ _ he => congrArg Prod.fst ((pack hs).injective he)⟩

private theorem offset_add (hs : Fintype.card A * d ≤ 2 ^ h) (hd : 0 < d)
    (i : A) (j : B h) (hj : j.val < d) :
    offset hs hd i + j = pack hs (i, ⟨j.val, hj⟩) := by
  apply Fin.ext
  change ((finProdFinEquiv (Fintype.equivFin A i, ⟨0, hd⟩)).val + j.val) % 2 ^ h =
    (finProdFinEquiv (Fintype.equivFin A i, ⟨j.val, hj⟩)).val
  have hl := (finProdFinEquiv (Fintype.equivFin A i, ⟨j.val, hj⟩)).isLt.trans_le hs
  simp only [finProdFinEquiv_apply_val, zero_add] at hl ⊢
  rw [Nat.add_comm, Nat.mod_eq_of_lt hl]

private theorem degree_packed (t : X ≃ A × Fin d) (e : X ↪ B h) (o : A ↪ B h)
    (mask : B h → Bool) (hm : ∀ i, mask i = true ↔ ∃ z, e z = i)
    (f : B h → B h) (hf : ∀ i, f (e i) = o (t i).1) (j : B h) :
    degree f mask j = if j ∈ Finset.univ.image o then d else 0 := by
  classical
  unfold degree
  by_cases hi : j ∈ Finset.univ.image o
  · rw [ite_eq_left hi]
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    let z (a : Fin d) := e (t.symm (u, a))
    have hz : Function.Injective z := fun _ _ hh =>
      congrArg Prod.snd (t.symm.injective (e.injective hh))
    have he : (Finset.univ.filter (fun i => mask i = true ∧ f i = o u)) = Finset.univ.image z := by
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, hm]
      constructor
      · rintro ⟨⟨v, rfl⟩, hv⟩
        rw [hf] at hv
        refine ⟨(t v).2, ?_⟩
        simp [z, ← o.injective hv]
      · rintro ⟨a, rfl⟩
        exact ⟨⟨t.symm (u, a), rfl⟩, by simp [z, hf]⟩
    rw [he, Finset.card_image_of_injective _ hz, Finset.card_fin]
  · rw [ite_eq_right hi, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro i hit
    obtain ⟨⟨v, rfl⟩, hv⟩ := And.imp_left (hm i).mp (Finset.mem_filter.mp hit).2
    exact hi (Finset.mem_image.mpr ⟨(t v).1, Finset.mem_univ _, (hf v).symm.trans hv⟩)

omit [Fintype X] in
private theorem inverse_agrees (e : X ↪ B h) (v : Equiv.Perm X) (f : B h → B h)
    (hf : ∀ i, f (e i) = e (v i)) (hout : ∀ i, (¬∃ z, e z = i) → f i = i)
    (inv : (B h → B h) → (B h → B h)) (hi : ∀ g : Equiv.Perm (B h), inv g = ⇑g.symm) :
    ∀ i, inv f (e (v i)) = e i := by
  have surj : Function.Surjective f := by
    intro j
    by_cases hh : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hh
      exact ⟨e (v.symm i), by simp [hf]⟩
    · exact ⟨j, hout _ hh⟩
  let g := Equiv.ofBijective f (Finite.surjective_iff_bijective.mp surj)
  intro i
  rw [← hf]
  change inv g (g (e i)) = e i
  rw [hi, Equiv.symm_apply_apply]

private theorem product_routes [Nonempty X] (t : X ≃ A × Fin d) (e : X ↪ B h)
    (inv : (B h → B h) → (B h → B h)) (hi : ∀ g : Equiv.Perm (B h), inv g = ⇑g.symm) :
    ∃ p : Chart h, ∀ (g : Equiv.Perm X) (y : B h → B h), (∀ i, y (e i) = e (g i)) →
      ∃ w v : Equiv.Perm X, (∀ i, (t (w i)).1 = (t i).1 ∧
        (t (v i)).1 = (t (g i)).1 ∧ (t (w i)).2 = (t (v i)).2) ∧
        (∀ i, (p.run inv y).1 (e (v i)) = e (g i)) ∧
        (∀ i, (p.run inv y).2.1 (e (w i)) = e (v i)) ∧
        (∀ i, (p.run inv y).2.2 (e i) = e (w i)) := by
  classical
  let z := t (Classical.arbitrary X)
  let _ : Nonempty (A × Fin d) := ⟨z⟩
  have hd : 0 < d := Nat.zero_lt_of_lt z.2.isLt
  have hs : Fintype.card A * d ≤ 2 ^ h := by
    simpa [Fintype.card_congr t] using Fintype.card_le_of_injective _ e.injective
  have hd' : d ≤ 2 ^ h :=
    (Nat.le_mul_of_pos_left _ (Fintype.card_pos_iff.mpr ⟨z.1⟩)).trans hs
  let o := offset hs hd
  let p : Chart h :=
    { base := fun i => o (t (Function.invFun e i)).1
      location := fun i => e (t.symm (Function.invFun (pack hs) i))
      support := Finset.univ.image o
      mask := fun i => decide (∃ j, e j = i)
      degree := d }
  have hmask (i) : p.mask i = true ↔ ∃ j, e j = i := decide_eq_true_iff
  have live (i) : p.mask (e i) = true := (hmask _).mpr ⟨i, rfl⟩
  have base (i) : p.base (e i) = o (t i).1 := by
    simp only [p, Function.leftInverse_invFun e.injective i]
  have loc (a : A) (i : B h) (hi : i.val < d) :
      p.location (o a + i) = e (t.symm (a, ⟨i.val, hi⟩)) := by
    rw [offset_add hs hd a i hi]
    exact congrArg (e ∘ t.symm) (Function.leftInverse_invFun (pack hs).injective _)
  refine ⟨p, fun g y hy => ?_⟩
  have target (i) : (p.base ∘ y) (e i) = o (t (g i)).1 := by simp only [Function.comp_apply, hy, base]
  have reg : Regular p.support d p.base (p.base ∘ y) p.mask :=
    ⟨degree_packed t e o p.mask hmask _ base,
     degree_packed (g.trans t) e o p.mask hmask _ target⟩
  have bound : p.support.card * d ≤ 2 ^ h := by
    simpa only [p, Finset.card_image_of_injective _ o.injective, Finset.card_univ] using hs
  have col := edge_coloring p.support d hd' bound p.base (p.base ∘ y) p.mask reg
  let c (i : X) : Fin d := ⟨(p.label y (e i)).val, (col _ (live i)).1⟩
  have route (f : B h → B h) (u : X → A) (hu : ∀ i, f (e i) = o (u i))
      (hf : f = p.base ∨ f = p.base ∘ y) :
      ∃ v : Equiv.Perm X, (∀ i, t (v i) = (u i, c i)) ∧
        (∀ i, p.route f (p.label y) (e i) = e (v i)) ∧
        (∀ i, inv (p.route f (p.label y)) (e (v i)) = e i) := by
    let move i := t.symm (u i, c i)
    have inject : Function.Injective move := by
      intro i j he
      obtain ⟨hl, hr⟩ := Prod.mk.inj (t.symm.injective he)
      have ends : f (e i) = f (e j) := by rw [hu, hu, hl]
      apply e.injective
      apply (col _ (live i)).2 _ (live j) (Fin.ext (congrArg (fun z : Fin d => z.val) hr))
      rcases hf with rfl | rfl
      · exact .inl ends
      · exact .inr ends
    let v := Equiv.ofBijective move inject.bijective_of_finite
    have hv (i) : p.route f (p.label y) (e i) = e (v i) := by
      rw [Chart.route, ite_eq_left (live i), hu, loc _ _ (c i).isLt]
      rfl
    exact ⟨v, fun _ => t.apply_symm_apply _, hv,
      inverse_agrees e v _ hv (fun i h => ite_eq_right (mt (hmask i).mp h)) inv hi⟩
  obtain ⟨w, hw, hl, hil⟩ := route _ (fun i => (t i).1) base (.inl rfl)
  obtain ⟨v, hv, hr, hir⟩ := route _ (fun i => (t (g i)).1) target (.inr rfl)
  refine ⟨w, v, fun i => by simp only [hw, hv, and_self], ?_, ?_, hl⟩
  · intro i
    exact (congrArg y (hir i)).trans (hy i)
  · intro i
    exact (congrArg (p.right y) (hil i)).trans (hr i)

theorem chart_exists (h : ℕ) (X C A D : Type) [Fintype X] [Fintype C] [Fintype A] [Fintype D]
    (s : X ≃ C × (A × D)) (e : X ↪ B h) (inv : (B h → B h) → (B h → B h))
    (hi : ∀ g : Equiv.Perm (B h), inv g = ⇑g.symm) :
    ∃ p : Chart h, ∀ (g : Equiv.Perm X), (∀ i, (s (g i)).1 = (s i).1) →
      ∀ y : (Perm h).obj, (∀ i, y (e i) = e (g i)) →
      ∃ u v w : Equiv.Perm X, g = u * v * w ∧
        (∀ i, (s (u i)).1 = (s i).1 ∧ (s (u i)).2.1 = (s i).2.1) ∧
        (∀ i, (s (v i)).1 = (s i).1 ∧ (s (v i)).2.2 = (s i).2.2) ∧
        (∀ i, (s (w i)).1 = (s i).1 ∧ (s (w i)).2.1 = (s i).2.1) ∧
        (∀ i, (p.run inv y).1 (e i) = e (u i)) ∧ (∀ i, (p.run inv y).2.1 (e i) = e (v i)) ∧
        (∀ i, (p.run inv y).2.2 (e i) = e (w i)) := by
  classical
  rcases isEmpty_or_nonempty X with _ | _
  · refine ⟨⟨id, id, fun _ => false, ∅, 0⟩, fun g _ _ _ => ⟨g, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp
    all_goals exact fun i => isEmptyElim i
  let t := (s.trans (Equiv.prodAssoc C A D).symm).trans
    ((Equiv.refl (C × A)).prodCongr (Fintype.equivFin D))
  obtain ⟨p, hp⟩ := product_routes t e inv hi
  refine ⟨p, fun g hg y hy => ?_⟩
  obtain ⟨w, z, hz, hu, hv, hw⟩ := hp g y hy
  have first (i) : (s (w i)).1 = (s i).1 ∧ (s (w i)).2.1 = (s i).2.1 :=
    Prod.mk.inj (hz i).1
  have last (i) : (s (g i)).1 = (s (z i)).1 ∧ (s (g i)).2.1 = (s (z i)).2.1 :=
    Prod.mk.inj (hz i).2.1.symm
  have middle (i) : (s (z i)).1 = (s (w i)).1 ∧ (s (z i)).2.2 = (s (w i)).2.2 :=
    ⟨(last i).1.symm.trans ((hg i).trans (first i).1.symm),
      (Fintype.equivFin D).injective (hz i).2.2.symm⟩
  refine ⟨g * z⁻¹, z * w⁻¹, w, by simp [mul_assoc], ?_, ?_, first, ?_, ?_, hw⟩
  · intro i
    simpa using last (z.symm i)
  · intro i
    simpa using middle (w.symm i)
  · intro i
    simpa using hu (z.symm i)
  · intro i
    simpa using hv (w.symm i)

end OAI.LinearAlgebra.MatrixExponent.Coloring
