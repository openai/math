import OAI.Geometry.Hirsch.Refinement

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Stage

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k : ℕ} {u : Dials}
  {rule : Rules raw} {old mid q : w.Round} {d : Bool}
  (G : Stage tag u k rule old d) (v : u.Valid) (hk : k < u.h)
  (foil : ∀ j : Fin u.J, Foil coin tag (k+1) raw.pins.rate u.L (price u.t j))
  (hf : tag.Fresh fresh k) (hz : fresh.rate = u.z)

include hz in
theorem error_eq (j : ℕ) : (G.ledger v hk j).error u.U fresh.pins.rate = u.error k := by
  change (G.ledger v hk j).error u.U fresh.rate = _
  rw [hz]; rfl

include v hk G in
theorem small : 2*raw.pins.rate + u.error k + u.err + u.K*raw.pins.rate*u.M ≤ u.t/4 := by
  have h : raw.pins.rate ≤ u.p := G.rate.le.trans (v.rate_le k)
  apply le_trans _ (v.small k hk)
  have := v.mass
  gcongr

include hz in
theorem next (hn : n ≤ u.a^u.h) (hm : mid.Finer old) (hq : q.Finer mid) {c : u.Scale}
    (hl : mid.Links d (fun i => G.scale v hk i = c)) {bin : u.Bin}
    (hl' : q.Links d (fun i => G.pick v hk mid i = bin)) :
    Stage tag u (k+1) (G.advance v hk foil hf mid) q (!(u.dir d bin)) := by
  have hr := G.visible_next v hk foil hf mid
  refine ⟨?_,hr,?_,G.reliable_next v hk foil hf mid⟩
  · change raw.rate * fresh.rate = _
    rw [G.rate,hz]; simp [Dials.rate,pow_succ,mul_assoc]
  rw [Bool.not_not]
  apply hr.capped v.tpos.le
  intro hide s hs i
  let j := w.place i / u.a^(k+1)
  let area := piece (u.a^(k+1)) j
  have hi : w.place i ∈ area := rfl
  let L := G.ledger v hk j
  let draw := G.draw v hk hf hide s hs
  let select := (G.advance v hk foil hf mid).watch hide s
  have hthin : ∀ x, select x ⊆ draw.thin x := G.thin v hk foil hf hide s hs
  have herr := G.error_eq v hk hz j
  have small := G.small v hk
  have hpos := v.scale.le.trans v.err_pos
  change coin.law.prob (q.Cover area (u.dir d bin) (u.cycles*(2+(u.D k).max)) select i) ≤ u.t
  cases bin with
  | some b =>
    have h := G.switched v hk foil hf hide s hs hn hm hq hl hl' j
    have hh := h.iterate v.tpos.le hpos v.crude_pos.le (by rw [herr]; exact small) v.contraction u.cycles hi
    exact hh.trans (by linarith [v.stop])
  | none =>
    have bound : ∀ y, G.pick v hk mid y = none → w.Shore d y → w.place y ∈ area →
        coin.law.prob (q.Cover area (!d) (u.D k).max select y) ≤ u.error k + u.t/4 := by
      intro y hy _ hya
      have mass : raw.pins.mass (L.band mid y) ≤ u.M :=
        (raw.pins.mass_mono L.band_sub).trans (L.bound hm hya (fun _ => Ledger.base)).mass
      have low : raw.pins.mass (L.band mid y) ≤ u.t/4 := by
        unfold pick at hy
        rw [G.band_eq v hk hya] at hy
        exact (bucket_low (mass.trans_lt v.bins) hy).le
      have hh := L.neutral draw hm hya (G.crude v hide s hs j y hya)
      rw [herr] at hh
      apply le_trans _ (hh.trans (add_le_add_right low _))
      exact coin.law.mono fun x h => (hq.test le_rfl _ h).mono (hthin x)
    have red := hl'.reduce (!d) hi (fun x => (hthin x).trans (draw.pinned x))
      (add_nonneg (v.error_pos k) (div_nonneg v.tpos.le (by norm_num))) bound
    have hsize : 2+(u.D k).max ≤ u.cycles*(2+(u.D k).max) := Nat.le_mul_of_pos_left _ u.run
    apply le_trans _ (red.trans (show _ ≤ u.t by
      have hh : 0 ≤ (u.K : ℝ)*raw.pins.rate*u.M := mul_nonneg (mul_nonneg (by positivity) raw.pos.le) v.mass
      linarith [v.tpos]))
    exact coin.law.mono fun _ h => Round.test_mono _ _ _ _ (fun _ => hsize) _ h

include v in
theorem initial (hr : tag.Tagged raw 0) (hp : raw.rate = u.p) (r : w.Round) (d : Bool) :
    Stage tag u 0 (Rules.initial raw) r d := by
  have hv : tag.Visible w (Rules.initial raw) 0 (u.a^0) :=
    ⟨hr,by simp [Rules.initial],fun _ _ _ _ => rfl⟩
  refine ⟨by simpa [Dials.rate] using hp,hv,?_,?_⟩
  swap
  · simpa [Dials.margin,Dials.cost] using Rules.initial_reliable raw w.place u.K
  apply hv.capped v.tpos.le
  intro hide s hs i
  let area := w.home (u.a^0) i
  obtain ⟨l,hl,hh⟩ := r.spine (i := i) (area := area) rfl (!d)
  have hsize : l.toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro g hg j hj
    have h₁ := hh g (List.mem_toFinset.mp hg)
    have h₂ := hh j (List.mem_toFinset.mp hj)
    apply h₁.unique h₂
    simpa [area,home,piece] using h₁.info.2.1.trans h₂.info.2.1.symm
  have hprob := raw.pins.extra_hit ∅ l.toFinset (Finset.disjoint_empty_right _)
  simp only [Pins.weight,Finset.card_empty,pow_zero,mul_one,Finset.empty_subset,true_and] at hprob
  have hraw : l.toFinset.card * raw.pins.rate ≤ u.t :=
    (mul_le_of_le_one_left raw.pos.le (by exact_mod_cast hsize)).trans (hp.le.trans v.initial_le)
  apply le_trans _ (hprob.trans hraw)
  apply coin.law.mono
  intro x hc
  obtain ⟨g,hg,hm⟩ := hc l hl
  exact ⟨g,List.mem_toFinset.mpr hg,(Rules.initial raw).watch_pin hs x hm⟩

theorem final_path (hn : n ≤ u.a^(k+1)) {g : I} {x : Table Bit}
    (hp : g ∈ (screened u k rule old d).pass x) :
    ∃ j l, ¬w.live j ∧ old.Trip Set.univ g j (flat (u.D k).step) l ∧
      ∀ i ∈ l, i ∈ (screened u k rule old d).pass x → w.place i = w.place g := by
  have hb := ((Rules.mem ..).mp hp).2.2.2.1
  obtain ⟨l,⟨j,he,ht⟩,hh⟩ := Stamp.available rule u.tests hb
  have same : ∀ i, w.place i / u.a^(k+1) = 0 := fun i => Nat.div_eq_of_lt ((w.num_lt true i).trans_le hn)
  have hi : w.place j ∈ w.home (u.a^(k+1)) g := (same j).trans (same g).symm
  exact ⟨j,l,(he.resolve_right fun h => h.1 hi).2,ht.widen (Set.subset_univ _),hh⟩

end OAI.Geometry.Hirsch.Layer.Board.Stage
