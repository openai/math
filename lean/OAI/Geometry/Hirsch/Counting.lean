import OAI.Geometry.Hirsch.Span

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Assembly

variable {clock res : Package} {count buckets labels windows : ℕ} [NeZero count]
  {ep : Episodes count} {sch : Schedule res.prog ep buckets labels}
  (asm : Assembly clock res sch windows)

def smallUpper (clock : Package) (windows : ℕ) : Set (Option (Overlay.Rows clock windows)) :=
  insert none (range fun pos => some (Sum.inr pos))

def smallLower (res : Package) (windows : ℕ) : Set (Overlay.Rows res windows) := range Sum.inr

theorem smallUpper_iff (tr : asm.machine.Trip) (side : Bool) :
    tr.side side ∈ smallUpper clock windows ↔ ¬asm.copy tr (some side) := by
  change _ ↔ ¬∃ idx row, tr.side side = some (.inl (idx, row))
  cases tr.side side with
  | none => simp [smallUpper]
  | some row => rcases row with ⟨idx, src⟩ | pos <;> simp [smallUpper]

theorem smallLower_iff (tr : asm.machine.Trip) :
    tr.2.2 ∈ smallLower res windows ↔ ¬asm.copy tr none := by
  change _ ↔ ¬∃ idx row, tr.2.2 = .inl (idx, row)
  rcases tr.2.2 with ⟨idx, src⟩ | pos <;> simp [smallLower]

theorem sparse_bound {small full : ℕ}
    (hs : (smallUpper clock windows).ncard ≤ small) (ht : (smallLower res windows).ncard ≤ small)
    (hf : Fintype.card (Option (Overlay.Rows clock windows)) ≤ full)
    (hg : Fintype.card (Overlay.Rows res windows) ≤ full) :
    {tr | asm.sparse tr}.ncard ≤ 3 * full * small ^ 2 := by
  let upper := smallUpper clock windows
  let lower := smallLower res windows
  let first : Set asm.machine.Trip := univ ×ˢ upper ×ˢ lower
  let second : Set asm.machine.Trip := upper ×ˢ univ ×ˢ lower
  let third : Set asm.machine.Trip := upper ×ˢ upper ×ˢ univ
  have hsub : {tr | asm.sparse tr} ⊆ first ∪ second ∪ third := by
    intro tr he
    have hh : ∀ kind other, asm.copy tr kind → kind ≠ other → ¬asm.copy tr other :=
      fun _ _ hi hn hj => hn (he hi hj)
    by_cases ha : asm.copy tr (some false)
    · exact Or.inl (Or.inl ⟨mem_univ _, (asm.smallUpper_iff tr true).mpr (hh _ _ ha (by decide)),
        (asm.smallLower_iff tr).mpr (hh _ _ ha (by decide))⟩)
    have hl := (asm.smallUpper_iff tr false).mpr ha
    by_cases hb : asm.copy tr (some true)
    · exact Or.inl (Or.inr ⟨hl, mem_univ _, (asm.smallLower_iff tr).mpr (hh _ _ hb (by decide))⟩)
    exact Or.inr ⟨hl, (asm.smallUpper_iff tr true).mpr hb, mem_univ _⟩
  calc
    _ ≤ (first ∪ second ∪ third).ncard := ncard_le_ncard hsub
    _ ≤ first.ncard + second.ncard + third.ncard :=
      (ncard_union_le _ _).trans (Nat.add_le_add_right (ncard_union_le _ _) _)
    _ ≤ full * (small * small) + small * (full * small) + small * (small * full) := by
      simp only [first, second, third, ncard_prod, ncard_univ, Nat.card_eq_fintype_card]
      gcongr
    _ = _ := by ring

theorem package_rows {span : ℕ} (hr : ∀ row, res.span row ≤ span) (hl : 0 < labels) :
    asm.package.rows ≤ sch.pkg.rows + buckets * 2 * (count * 2) * clock.size +
      buckets * {tr | asm.sparse tr}.ncard * (2 * labels) ^ span := by
  classical
  let triples := {tr | asm.sparse tr}
  let actions := Σ bucket, Σ tr : triples, asm.machine.Picks bucket tr.val
  let codes := asm.machine.Ordinary ⊕ asm.machine.FloorRow ⊕ actions
  let decoder : codes → asm.package.Row
    | .inl row => ⟨.inl row, True.intro⟩
    | .inr (.inl row) => ⟨.inr (.inl row), True.intro⟩
    | .inr (.inr ⟨bucket, tr, pick⟩) => ⟨.inr (.inr ⟨bucket, tr.val, pick⟩), tr.property⟩
  have hd : Function.Surjective decoder := by
    rintro ⟨row | row | ⟨bucket, tr, pick⟩, hh⟩
    · exact ⟨.inl row, rfl⟩
    · exact ⟨.inr (.inl row), rfl⟩
    · exact ⟨.inr (.inr ⟨bucket, ⟨tr, hh⟩, pick⟩), rfl⟩
  have hp : ∀ bucket tr, Fintype.card (asm.machine.Picks bucket tr) ≤ (2 * labels) ^ span := by
    intro bucket tr
    apply (sch.paint.card_pick bucket _ (sch.groupBound bucket)).trans
    apply Nat.pow_le_pow_right (by positivity)
    exact (ncard_le_ncard (res.prog.subset_closure _)).trans (asm.lower.span hr _)
  have ha : Fintype.card actions ≤ buckets * triples.ncard * (2 * labels) ^ span := by
    unfold actions
    simp only [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : Fin buckets, ∑ _ : triples, (2 * labels) ^ span :=
        Finset.sum_le_sum fun bucket _ => Finset.sum_le_sum fun tr _ => hp bucket tr
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, fintypeCard_eq_ncard,
          nsmul_eq_mul, Nat.cast_id, mul_assoc]
  have ho : Fintype.card asm.machine.Ordinary ≤ sch.pkg.rows := Fintype.card_subtype_le _
  have hf : Fintype.card asm.machine.FloorRow = buckets * 2 * (count * 2) * clock.size := by
    change Fintype.card (Fin buckets × Bool × (Fin count × Bool) × clock.prog.Coord) = _
    simp [Package.size, mul_assoc]
  apply (Fintype.card_le_of_surjective decoder hd).trans
  unfold codes
  rw [Fintype.card_sum, Fintype.card_sum, hf, ← add_assoc]
  exact Nat.add_le_add (Nat.add_le_add_right ho _) ha

theorem small_bounds (pkg : Package) (windows : ℕ) :
    (smallUpper pkg windows).ncard ≤ windows * 2 * pkg.size + 1 ∧
    (smallLower pkg windows).ncard ≤ windows * 2 * pkg.size + 1 := by
  have aux : ∀ {α : Type} (fn : Fin windows × Bool × pkg.prog.Coord → α),
      (range fn).ncard ≤ windows * 2 * pkg.size := by
    intro α fn
    rw [← image_univ]
    simpa [Package.size, mul_assoc] using
      (ncard_image_le (f := fn) (s := univ))
  exact ⟨(ncard_insert_le ..).trans (Nat.add_le_add_right (aux _) 1), (aux _).trans (Nat.le_add_right ..)⟩

end OAI.Geometry.Hirsch.Assembly
