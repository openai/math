import OAI.Geometry.Hirsch.Barriers

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins.Rules

variable {Bit I Z : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} {raw : coin.Raw I} {place : I → Z} {rule : Rules raw}
  {K : ℕ} {margin loss gamma alpha : ℝ} (hr : rule.Reliable place K margin loss)
  {s : Finset I} (hk : s.card ≤ K) (hc : ∀ g ∈ s, rule.Compatible place s g)

include hr hk hc in
theorem Reliable.failures (site : Z) :
    coin.two.prob (fun x => ∃ g ∈ s, s ⊆ raw.pins.success x.1 ∧
      (¬rule.ok g x.1 ∨ ¬rule.ok g (raw.after place site x))) ≤ 2*K*loss*raw.pins.weight s := by
  let fail := fun g (x : Table Bit × Table Bit) => s ⊆ raw.pins.success x.1 ∧
    (¬rule.ok g x.1 ∨ ¬rule.ok g (raw.after place site x))
  have each : ∀ g ∈ s, coin.two.prob (fail g) ≤ 2*loss*raw.pins.weight s := by
    intro g hg
    let bad := fun t => ¬rule.ok g t
    let orig := fun x : Table Bit × Table Bit => bad x.1 ∧ s ⊆ raw.pins.success x.1
    let later := fun x : Table Bit × Table Bit => bad (raw.after place site x) ∧ s ⊆ raw.pins.success x.1
    have h₁ : coin.two.prob orig ≤ loss * raw.pins.weight s := by
      rw [show coin.two.prob orig = raw.pins.joint bad s from coin.law.tensor_first _ (fun y => bad y ∧ s ⊆ raw.pins.success y)]
      exact (div_le_iff₀ (raw.pins.positive s)).mp (hr.screen g s hk (hc g hg))
    have h₂ : coin.two.prob later ≤ loss * raw.pins.weight s := by
      unfold later
      rw [raw.joint_after]
      apply mul_le_mul_of_nonneg_right _ (raw.pins.positive s).le
      exact hr.screen g _ ((Finset.card_filter_le ..).trans hk) ((hc g hg).sub (Finset.filter_subset ..))
    apply le_trans _ ((coin.two.either orig later).trans (show _ ≤ 2*loss*raw.pins.weight s by linarith))
    exact coin.two.mono fun _ ⟨hp,h⟩ => h.imp (fun h => ⟨h,hp⟩) (fun h => ⟨h,hp⟩)
  calc
    _ ≤ ∑ g ∈ s, coin.two.prob (fail g) := coin.two.union_finset ..
    _ ≤ ∑ _ ∈ s, 2*loss*raw.pins.weight s := Finset.sum_le_sum each
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hn := hr.nonneg
      have hp := raw.pins.positive s
      linarith [mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk : (s.card : ℝ) ≤ K)
        (show 0 ≤ 2*loss*raw.pins.weight s by positivity)]

include hr hk hc in
theorem Reliable.joint (site : Z) (hg : gamma ≤ margin^K - 2*K*loss) :
    gamma * raw.pins.weight s ≤ coin.two.prob (fun x => s ⊆ rule.pass x.1 ∧
      ∀ g ∈ s, place g ≠ site → g ∈ rule.pass (raw.after place site x)) := by
  let start := fun x => s ⊆ raw.pins.success x ∧ ∀ g ∈ s, All (rule.barriers g) x
  let stop := fun x : Table Bit × Table Bit => s ⊆ rule.pass x.1 ∧
    ∀ g ∈ s, place g ≠ site → g ∈ rule.pass (raw.after place site x)
  let fail := fun x : Table Bit × Table Bit => ∃ g ∈ s, s ⊆ raw.pins.success x.1 ∧
    (¬rule.ok g x.1 ∨ ¬rule.ok g (raw.after place site x))
  have cover : ∀ x, start x.1 → stop x ∨ fail x := by
    intro x hx
    by_cases hn : fail x
    · exact .inr hn
    have pass : ∀ g ∈ s, rule.ok g x.1 ∧ rule.ok g (raw.after place site x) := by
      intro g h
      exact ⟨by_contra (fun hh => hn ⟨g,h,hx.1,.inl hh⟩),by_contra (fun hh => hn ⟨g,h,hx.1,.inr hh⟩)⟩
    left
    exact ⟨fun g h => (rule.mem ..).mpr ⟨hx.1 h,hx.2 g h,(pass g h).1⟩,fun g h he =>
      (rule.mem ..).mpr ⟨(raw.fixed place site x he).mp (hx.1 h),
        rule.barriers_keep site x g (hx.2 g h),(pass g h).2⟩⟩
  have low : margin^K * raw.pins.weight s ≤ coin.two.prob (fun x => start x.1) :=
    (hr.start hk).trans_eq (coin.law.tensor_first _ start).symm
  have high : coin.two.prob fail ≤ 2*K*loss*raw.pins.weight s := hr.failures hk hc site
  apply le_trans _ (coin.two.event_loss _ _ _ cover)
  linarith [mul_le_mul_of_nonneg_right hg (raw.pins.positive s).le]

include hr hk hc in
theorem Reliable.passage [Nonempty Z] (hg : gamma ≤ margin^K - 2*K*loss) :
    gamma * raw.pins.weight s ≤ coin.law.prob (fun x => s ⊆ rule.pass x) := by
  rw [← coin.law.tensor_first coin.law (fun x => s ⊆ rule.pass x)]
  exact (hr.joint hk hc (Classical.arbitrary Z) hg).trans (coin.two.mono (fun _ h => h.1))

theorem compatible_of_possible (hs : ∃ x, s ⊆ rule.pass x) : ∀ g ∈ s, rule.Compatible place s g := by
  obtain ⟨x,hx⟩ := hs
  exact fun g hg => .inr ⟨x,hx.trans (Finset.filter_subset ..),((rule.mem ..).mp (hx hg)).2.2⟩

variable [Nonempty Z] (hg : gamma ≤ margin^K - 2*K*loss) (thr : Thresholds K)
  (bad : I → Table Bit → Prop) (screened : ∀ g x, rule.ok g x → raw.pins.Screen thr (bad g) x)

def Reliable.gates : Trial.Gates raw.pins place K gamma (thr.value K) where
  pass := rule.pass
  pinned _ := Finset.filter_subset ..
  bad := bad
  screen x g hh := (screened g x ((rule.mem ..).mp hh).2.2).1
  possible _ hk hs := hr.passage hk (compatible_of_possible hs) hg
  compatible x g hh s hs hk := ((screened g x ((rule.mem ..).mp hh).2.2).2 s
    (hs.trans (Finset.filter_subset ..)) hk).trans (thr.mono hk)

theorem Reliable.resample (site : Z) : Nonempty ((hr.gates hg thr bad screened).Resample site) := by
  refine ⟨{
    Resp := Table Bit × Table Bit, law := coin.two, before := Prod.fst, after := raw.after place site,
    marginal := coin.marginal _, fixed := fun x g => raw.fixed place site x,
    extra := raw.extra place site, possible := fun s hk hs => hr.joint hk (compatible_of_possible hs) site hg }⟩

end OAI.Geometry.Hirsch.Layer.Coins.Rules
