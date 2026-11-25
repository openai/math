import OAI.Geometry.Hirsch.CutMass

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Trial.Gates

variable {Ω I Z : Type} [Fintype Ω] {p : Law Ω} {place : I → Z} {K e d : ℕ}
  {tests : Tests place e d} {pins : Pins p I} {gamma alpha : ℝ}

structure Resample (gate : Gates pins place K gamma alpha) (site : Z) where
  Resp : Type
  [finite : Fintype Resp]
  law : Law Resp
  before : Resp → Ω
  after : Resp → Ω
  marginal : ∀ E, law.prob (fun x => E (after x)) = p.prob E
  fixed : ∀ x g, place g ≠ site → (g ∈ pins.success (before x) ↔ g ∈ pins.success (after x))
  extra : ∀ (s : Finset I) (f : Ω → Finset I) (N : ℕ), site ∉ s.image place →
    (∀ x, (f x).card ≤ N ∧ ∀ i ∈ f x, place i = site) →
    law.prob (fun x => s ⊆ pins.success (before x) ∧ ∃ i ∈ f (after x), i ∈ pins.success (before x)) ≤
      N * pins.rate * pins.weight s
  possible : ∀ s : Finset I, s.card ≤ K → (∃ x, s ⊆ gate.pass x) →
    gamma * pins.weight s ≤ law.prob (fun x => s ⊆ gate.pass (before x) ∧
      ∀ i ∈ s, place i ≠ site → i ∈ gate.pass (after x))

attribute [instance] Resample.finite

variable {gate : Gates pins place K gamma alpha} {family : Finset (Finset I)}
  (hl : gate.ListAt tests family) (hs : gate.Serves tests) (s : Finset I)

include hl hs in
theorem ListAt.foreign {g : I} (change : gate.Resample (place g))
    (fresh : place g ∉ s.image place) (contains : ∀ t ∈ family, s ⊆ t)
    (some : ∃ t ∈ family, g ∈ t) (transfer : ∀ t ∈ family, g ∉ t → (tests.next g).Covers t) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * (alpha + (d+1)*pins.rate) * pins.weight s := by
  have hex : ∀ x, ∃ f : Finset I, (f.card ≤ d+1 ∧ ∀ i ∈ f, place i = place g) ∧
      (¬gate.bad g x → ∀ t ∈ family, (∀ i ∈ t, place i ≠ place g → i ∈ gate.pass x) →
        ∃ i ∈ f, i ∈ t) := by
    intro x
    by_cases hb : gate.bad g x
    · exact ⟨∅,by simp,fun h => (h hb).elim⟩
    obtain ⟨path,hp,hh⟩ := hs x g hb
    refine ⟨insert g (keysAt place path {place g}),⟨?_,?_⟩,fun _ t ht hpass => ?_⟩
    · exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right (tests.nextBound g _ hp _) 1)
    · simp
    · by_cases hg : g ∈ t
      · exact ⟨g,by simp,hg⟩
      obtain ⟨i,hi,hit⟩ := transfer t ht hg path hp
      have eq : place i = place g := by_contra fun hn => hn (hh i hi (hpass i hit hn))
      exact ⟨i,by simp [hi,eq],hit⟩
  choose f hsize hf using hex
  let A := fun x => gate.bad g (change.after x) ∧ s ⊆ pins.success (change.after x)
  let B := fun x => s ⊆ pins.success (change.before x) ∧ ∃ i ∈ f (change.after x), i ∈ pins.success (change.before x)
  have ha : change.law.prob A ≤ alpha * pins.weight s := by
    obtain ⟨t,ht,hgt⟩ := some
    obtain ⟨⟨hk,_,_⟩,x,hx⟩ := hl _ ht
    have hc := gate.compatible x g (hx hgt) s ((contains _ ht).trans hx)
      ((Finset.card_le_card (contains _ ht)).trans hk)
    have he : change.law.prob A = pins.joint (gate.bad g) s :=
      change.marginal (fun x => gate.bad g x ∧ s ⊆ pins.success x)
    rw [he]
    exact (div_le_iff₀ (pins.positive s)).mp hc
  have hb : change.law.prob B ≤ (d+1)*pins.rate*pins.weight s := by
    simpa only [Nat.cast_add,Nat.cast_one] using change.extra s f (d+1) fresh hsize
  let hit := fun (t : Finset I) x => t ⊆ gate.pass (change.before x) ∧
    ∀ i ∈ t, place i ≠ place g → i ∈ gate.pass (change.after x)
  have key : gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * change.law.prob (fun x => A x ∨ B x) := by
    apply hl.estimate hs change.law change.before hit _
      (fun t ht => change.possible t (hl _ ht).1.1 (hl _ ht).2) (fun _ _ _ hh => hh.1)
    intro t ht x hh
    have pin := hh.1.trans (gate.pinned _)
    have fixed := (contains _ ht).trans pin
    by_cases bad : gate.bad g (change.after x)
    · left
      refine ⟨bad,fun i hi => (change.fixed _ _ ?_).mp (fixed hi)⟩
      exact fun he => fresh (Finset.mem_image.mpr ⟨i,hi,he⟩)
    · obtain ⟨i,hi,hmem⟩ := hf _ bad t ht hh.2
      exact .inr ⟨fixed,i,hi,pin hmem⟩
  rw [mul_assoc]
  exact key.trans (mul_le_mul_of_nonneg_left ((change.law.either A B).trans (by linarith)) (by positivity))

include hl hs in
theorem ListAt.link (change : ∀ z, Nonempty (gate.Resample z)) (ha : 0 ≤ alpha)
    (contains : ∀ t ∈ family, s ⊂ t) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) *
      (alpha + (K*e+d+1)*pins.rate) * pins.weight s := by
  have hp := pins.pos
  have hw := pins.positive s
  by_cases hn : family.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp only [Pins.mass,Finset.sum_empty,mul_zero]
    positivity
  obtain ⟨t,ht⟩ := hn
  have hk := (Finset.card_lt_card (contains _ ht)).trans_le (hl _ ht).1.1
  obtain ⟨path,hpath,hmiss⟩ := missed ((hl _ ht).1.2.2 _ (contains _ ht))
  let a := keysAt place path (s.image place)
  have hsize : a.card ≤ K*e := (tests.shortBound.sites hpath _).trans
    (Nat.mul_le_mul_right _ (Finset.card_image_le.trans hk.le))
  let P := fun t : Finset I => ∃ i ∈ a, i ∈ t
  let left := family.filter P
  let right := family.filter (fun t => ¬P t)
  have hl₁ : gate.ListAt tests left := hl.sub (Finset.filter_subset ..)
  have hl₂ : gate.ListAt tests right := hl.sub (Finset.filter_subset ..)
  have h₁ : gamma * pins.mass left ≤ (Tests.capacity K e d : ℝ) * (K*e*pins.rate*pins.weight s) := by
    let E := fun x => s ⊆ pins.success x ∧ ∃ i ∈ a, i ∈ pins.success x
    have hh : gamma * pins.mass left ≤ (Tests.capacity K e d : ℝ) * p.prob E := by
      apply hl₁.bound hs
      intro t ht x hx
      obtain ⟨ht,i,hi,hm⟩ := Finset.mem_filter.mp ht
      exact ⟨(contains _ ht).subset.trans (hx.trans (gate.pinned _)),i,hi,gate.pinned _ (hx hm)⟩
    apply hh.trans
    gcongr
    apply (pins.extra s a (fun i hi hm => hmiss ⟨i,(mem_at.mp hi).1,hm⟩)).trans
    gcongr
    exact_mod_cast hsize
  have h₂ : gamma * pins.mass right ≤ (Tests.capacity K e d : ℝ) * (alpha+(d+1)*pins.rate)*pins.weight s := by
    by_cases hn : right.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simp only [Pins.mass,Finset.sum_empty,mul_zero]
      positivity
    let pool := right.biUnion id
    have incl : ∀ t ∈ right, t ⊆ pool := fun t ht _ hi => Finset.mem_biUnion.mpr ⟨t,ht,hi⟩
    obtain ⟨u,hu⟩ := hn
    obtain ⟨pre,g,rest,he,hpre,hg⟩ := ((tests.refines _ (hl₂ _ hu).1.2.1 _ hpath).mono (incl u hu)).first
    obtain ⟨v,hv,hg⟩ := Finset.mem_biUnion.mp hg
    have fresh : place g ∉ s.image place := fun h =>
      (Finset.mem_filter.mp hv).2 ⟨g,mem_at.mpr ⟨by simp [he],h⟩,hg⟩
    exact hl₂.foreign hs s (Classical.choice (change _)) fresh
      (fun t ht => (contains _ (Finset.mem_filter.mp ht).1).subset) ⟨v,hv,hg⟩
      (fun t ht hn => tests.transfer _ _ _ (he ▸ hpath) t (hl₂ _ ht).1.2.1
        (fun h => hpre (h.mono (incl t ht))) hn)
  rw [← pins.mass_split family P,mul_add]
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end OAI.Geometry.Hirsch.Layer.Trial.Gates
