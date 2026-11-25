import OAI.Geometry.Hirsch.SpineBounds

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I Ω : Type} [Fintype Ω] {p : Law Ω} {pins : Pins p I} {n K : ℕ} {w : Board I n}
  {q r : w.Round} {area : Set ℕ} {d : Bool} {P : I → Prop} {i : I} {a : Ω → Finset I}

namespace Round

def Cover (q : w.Round) (area : Set ℕ) (d : Bool) (R : ℕ) (a : Ω → Finset I) (i : I) (x : Ω) :=
  (q.test area d (flat R) i).Covers (a x)

theorem Links.start (link : q.Links d P) (dir : Bool) (hi : w.place i ∈ area) :
    [] ∈ q.test area dir (flat 1) i ∨ ∃ y l, P y ∧ w.Shore d y ∧ w.place y ∈ area ∧
      q.Trip area i y (flat 2) l ∧ l.toFinset.card ≤ 2 := by
  obtain ⟨l,hl,hh⟩ := q.spine hi dir
  cases l with
  | nil => exact .inl hl
  | cons g rest =>
    right
    have ho := hh g (by simp)
    obtain ⟨j,_,ht⟩ := hl
    change q.Trip area i j (flat 1) ([] ++ g :: rest) at ht
    by_cases he : dir = d
    · subst dir
      obtain ⟨u,_,_,hm,he⟩ := ho
      have hg : P g := he ▸ link.east _ hm
      have ho := hh g (by simp)
      exact ⟨g,[g],hg,ho.info.1,ho.info.2.1,ht.redirect.more (fun _ => by norm_num [flat]),by simp⟩
    · have he' : dir = !d := by cases dir <;> cases d <;> simp_all
      obtain ⟨y,l,hy,hs,hp,ht,hl⟩ := link.divert ht (he' ▸ ho.info.1)
      refine ⟨y,l,hy,hs,hp.symm ▸ ho.info.2.1,ht,?_⟩
      have sub : l.toFinset ⊆ {g,y} := by
        intro k hk; simpa using hl (List.mem_toFinset.mp hk)
      exact (Finset.card_le_card sub).trans ((Finset.card_insert_le ..).trans (by simp))

theorem Links.reduce (link : q.Links d P) (dir : Bool) (hi : w.place i ∈ area)
    (pin : ∀ x, a x ⊆ pins.success x) {R : ℕ} {B : ℝ} (hn : 0 ≤ B)
    (bound : ∀ y, P y → w.Shore d y → w.place y ∈ area → p.prob (q.Cover area dir R a y) ≤ B) :
    p.prob (q.Cover area dir (2+R) a i) ≤ 2*pins.rate + B := by
  rcases link.start dir hi with he | ⟨y,l,hy,hs,hp,ht,hk⟩
  · have hh : ∀ x, ¬q.Cover area dir (2+R) a i x := by
      intro x hc
      have h := test_mono _ _ _ _ (show flat 1 ≤ flat (2+R) from fun _ => by simp only [flat]; omega) _ hc _ he
      simp [Trial.Hit] at h
    simp only [Law.prob,hh,↓reduceIte,Finset.sum_const_zero]; linarith [pins.pos]
  have hhit : p.prob (fun x => Trial.Hit (a x) l) ≤ 2*pins.rate := by
    have hb := pins.extra_hit ∅ l.toFinset (Finset.disjoint_empty_right _)
    simp only [Finset.empty_subset,true_and,Pins.weight,Finset.card_empty,pow_zero,mul_one] at hb
    exact ((p.mono fun x ⟨g,hg,hm⟩ => ⟨g,List.mem_toFinset.mpr hg,pin x hm⟩).trans hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) pins.pos.le)
  apply le_trans _ ((p.either _ _).trans (add_le_add hhit (bound y hy hs hp)))
  apply p.mono
  intro x hc
  by_cases h : Trial.Hit (a x) l
  · exact .inl h
  · exact .inr (ht.carry h hc le_rfl)

theorem Finer.escape (hr : q.Finer r) {R F : ℕ} {b : Budget} (hb : b ≤ flat F)
    {s t u : Finset I} (hsub : u ⊆ s) (hc : (q.test area d (flat (F+R)) i).Covers u)
    (hmiss : ¬(r.test area (!d) b i).Covers s) (ht : (r.test area (!d) b i).Covers t) :
    ∃ g ∈ t, (q.test area d (flat R) g).Covers u := by
  obtain ⟨l,hl,hn⟩ := Trial.missed hmiss
  obtain ⟨pre,g,rest,rfl,_,hg⟩ := (ht _ hl).first
  obtain ⟨_,_,hpath⟩ := hl
  obtain ⟨l,hl,h⟩ := hr.trip (hpath.redirect.more hb)
  refine ⟨g,hg,hl.carry ?_ hc le_rfl⟩
  rintro ⟨j,hj,hm⟩
  have hh := h hj
  exact hn ⟨j,by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto,hsub hm⟩

end Round

namespace Ledger

variable [Fintype I] {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old : w.Round} {D : Depths K} {M A : ℝ} (L : Ledger gate old area d D M A)
  {fresh : Pins p I} (draw : gate.Draw fresh)

structure Switched (r q : w.Round) (P : I → Prop) (a : Ω → Finset I) (b err v U : ℝ) : Prop where
  mid : r.Finer old
  last : q.Finer r
  link : q.Links d P
  thinned : ∀ x, a x ⊆ draw.thin x
  crude : ∀ i, w.place i ∈ area → p.prob (old.Cover area (!d) D.step draw.available i) ≤ U
  rare : ∀ i, w.place i ∈ area → w.Shore d i →
    pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err
  large : ∀ i, w.place i ∈ area → P i → b ≤ pins.mass (L.band r i)
  positive : 0 < b
  small : err+L.loss ≤ b/4
  pairs : 12*L.beta < b^2
  nonneg : 0 ≤ v
  shared : ∀ B, b/4 ≤ pins.mass B → ∃ event : Ω → Prop, p.prob event ≤ v ∧
    (∀ g, w.place g ∈ area → P g → B ⊆ L.band r g → ∀ x, g ∈ a x → event x) ∧
    ∀ j, (∀ s ∈ B, s.Nonempty ∧ ∀ g ∈ s, w.rank j < w.rank g) →
      ∀ R, p.Independent event (q.Cover area d R a j)

namespace Switched

variable {L draw} {b err v U : ℝ} (h : L.Switched draw r q P a b err v U)

include h in
theorem at_key (hi : w.place i ∈ area) (he : w.Shore d i) (hp : P i)
    {R : ℕ} {S : ℝ} (hS : 0 ≤ S) (bound : ∀ j, w.place j ∈ area → p.prob (q.Cover area d R a j) ≤ S) :
    p.prob (q.Cover area d (D.max+R) a i) ≤ L.error U fresh.rate + err + K*pins.rate*M + K*v*S := by
  have rare := h.rare i hi he
  obtain ⟨t,ht,B,hB,hall,hrank⟩ := L.barriers h.mid hi rare (h.large i hi hp) h.positive h.small h.pairs
  obtain ⟨e,he,pass,indep⟩ := h.shared B hB
  have hc := L.cut hi base (L.band_sub ht)
  have inside : ∀ j ∈ t, w.place j ∈ area := fun _ hj =>
    Round.keys_inside ((L.core r hi base).refines _ hc.1) hc.2 hj
  have each : ∀ j ∈ t, p.prob (fun x => e x ∧ q.Cover area d R a j x) ≤ v*S := by
    intro j hj
    rw [indep j (fun s hs => ⟨(hrank _ hs).1,fun g hg => (hrank _ hs).2 g hg j hj⟩) R]
    exact mul_le_mul he (bound _ (inside _ hj)) (p.positive _) h.nonneg
  have high : p.prob (fun x => ∃ j ∈ t, e x ∧ q.Cover area d R a j x) ≤ K*v*S := by
    apply ((p.union_finset t _).trans (Finset.sum_le_sum each)).trans
    rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (L.mem.mp ht).1) (mul_nonneg h.nonneg hS)
  have low := L.joint_hit draw h.mid hi rare (h.crude _ hi)
  apply le_trans _ ((p.either _ _).trans (add_le_add low high))
  apply p.mono
  intro x hx
  have hD := D.order
  obtain ⟨g,hg,ho⟩ := Round.hits hi (show flat 1 ≤ flat (D.max+R) from fun _ => by simp only [flat]; omega) hx
  by_cases hwest : (r.test area (!d) (L.depth i) i).Covers (draw.thin x)
  · exact .inl ⟨hwest,g,h.thinned x hg,h.last.on ho⟩
  have hd : L.depth i ≤ flat D.max := (L.range_depth _).2.trans (fun _ => hD.2.2.2.2)
  obtain ⟨j,hj,hcov⟩ := h.last.escape hd (h.thinned x) hx hwest (L.mem.mp ht).2.1
  have pg : P g := by obtain ⟨u,_,_,hm,rfl⟩ := ho; exact h.link.east u hm
  exact .inr ⟨j,hj,pass g ho.info.2.1 pg (hall g ho.info.2.1 ho.info.2.2.1) x hg,hcov⟩

include h in
theorem iterate {t : ℝ} (ht : 0 ≤ t) (herr : 0 ≤ err) (hU : 0 ≤ U)
    (he : 2*pins.rate + L.error U fresh.rate + err + K*pins.rate*M ≤ t/4)
    (hv : K*v ≤ 1/2) (j : ℕ) (hi : w.place i ∈ area) :
    p.prob (q.Cover area d (j*(2+D.max)) a i) ≤ t/2 + (K*v)^j := by
  have vpos := h.nonneg
  induction j generalizing i with
  | zero =>
    rw [pow_zero]
    linarith [p.positive (fun x => ¬q.Cover area d (0*(2+D.max)) a i x),
      p.neg (q.Cover area d (0*(2+D.max)) a i)]
  | succ j ih =>
    let S := t/2+(K*v)^j
    have hS : 0 ≤ S := by unfold S; positivity
    have hpos : 0 ≤ L.error U fresh.rate + err + K*pins.rate*M + K*v*S := by
      have := fresh.pos
      have := pins.pos
      have := L.positive.1
      have := L.mass
      unfold error; positivity
    have hb := h.link.reduce d hi (fun x => (h.thinned x).trans (draw.pinned x)) hpos
      (fun _ hp he hi => h.at_key hi he hp hS (fun _ hi => ih hi))
    rw [Nat.succ_mul,add_comm (j*_ ),add_assoc,pow_succ']
    apply hb.trans
    unfold S
    linarith only [he,mul_le_mul_of_nonneg_right hv ht]

end Switched
end Ledger
end OAI.Geometry.Hirsch.Layer.Board
