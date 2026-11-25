import OAI.Geometry.Hirsch.Ledger

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Ω : Type} [Fintype Ω] {p : Law Ω} {pins : Pins p I}

theorem Pins.split_mass (pins : Pins p I) (B : Finset (Finset I)) (P : Finset I → Prop) [DecidablePred P] :
    pins.mass B ≤ pins.mass (B.filter P) + pins.mass (B.filter fun s => ¬P s) := by
  apply le_trans _ (pins.mass_union ..)
  apply pins.mass_mono
  intro s hs; simp [hs]; tauto

theorem Pins.retain (pins : Pins p I) {B C : Finset (Finset I)} (P : Finset I → Prop) [DecidablePred P]
    {loss : ℝ} (sub : B ⊆ C) (hb : pins.mass (C.filter fun s => ¬P s) ≤ loss) :
    pins.mass B ≤ pins.mass (B.filter P) + loss :=
  (pins.split_mass B P).trans (add_le_add_right ((pins.mass_mono (Finset.filter_subset_filter _ sub)).trans hb) _)

namespace Board.Ledger

variable [Fintype I] {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A) {i y : I} {s t : Finset I} {f scale : ℕ}

def close (i : I) (scale : ℕ) := (L.book old i (flat (4*D.near))).filter fun t =>
  ∃ g ∈ t, old.On area d i g ∧ w.left d t + scale ≤ w.num d g ∧ 4*w.num d g ≤ 4*w.num d i + scale

theorem force_charge (hr : r.Finer old) (hi : w.place i ∈ area) (hscale : 0 < scale)
    (ht : t ∈ L.book r i (flat (4*D.near))) (ht' : t ∈ L.book old i (flat (4*D.near)))
    (hs : s ∈ L.close i scale) (hleft : 4*w.num d i ≤ 4*w.left d t + scale)
    (hg : (L.core old hi (by omega : 2*D.near ≤ 4*D.near)).Good t s) :
    r.Straddles d t area i ∧ 4*r.right d t area i ≤ 4*w.num d i + scale := by
  obtain ⟨hs,g,hgs,ho,h₁,h₂⟩ := Finset.mem_filter.mp hs
  have hH := D.order.2.1
  have hf : 2*D.near ≤ 4*D.near := by omega
  let c := L.core old hi hf
  have newer : c.Newer t s := by
    rcases hg.order (L.cut hi hf ht') (L.cut hi hf hs) with hh | hh
    · exact hh
    · have := Round.newer_left (L.cut hi hf hs) hh
      omega
  obtain ⟨l,b,hp,hb,hh⟩ := r.trace ho.info.2.2.1
  have hit : Trial.Hit t l := by
    by_contra miss
    have small : b ≤ flat 1 := le_self_add.trans (hb.le.trans (w.ahead_one d i))
    have cost : b + flat D.near ≤ flat (4*D.near) := by
      intro x; have := small x; simp only [flat,Pi.add_apply] at *; omega
    have cover := hr.test le_rfl _ (hp.carry miss (L.mem.mp ht).2.1 cost)
    obtain ⟨j,hj⟩ := (c.refines _ (L.cut hi hf ht').1).nonempty c.inhabited
    exact (c.falls.older cover (hg.2.2 g hgs) j hj).not_gt ((newer.2.2 j hj).2 g hgs)
  obtain ⟨j,hj,hjt⟩ := hit
  obtain ⟨ho',hle⟩ := hh j hj
  have hnum : w.num d j ≤ w.num d g := Nat.div_le_div_right hle
  have := ho'.right_le hjt
  exact ⟨⟨j,hjt,ho'⟩,by omega⟩

def Cohort (_L : Ledger gate old area d D M A) (r : w.Round) (i : I) (scale : ℕ) (B : Finset (Finset I)) :=
  (∀ s ∈ B, r.Straddles d s area i ∧ w.left d s + scale ≤ r.right d s area i) ∧
  ∀ s ∈ B, ∀ t ∈ B, 4*w.left d s ≤ 4*w.left d t + scale ∧
    4*r.right d t area i ≤ 4*r.right d s area i + scale

set_option maxHeartbeats 600000 in
theorem shift (hr : r.Finer old) (hi : w.place i ∈ area) (hf : 9*D.near ≤ f)
    {B : Finset (Finset I)} (hB : B ⊆ L.book r i (flat f)) (hc : L.Cohort r i scale B)
    (hscale : 0 < scale) {theta : ℝ} (hth : 0 < theta) (hbeta : 3*L.beta < theta^2)
    (hm : 3*(theta+L.loss) ≤ pins.mass B)
    {P : I → Prop} (link : r.Links d P)
    (stable : ∀ u y, w.place u ∈ area → w.place y ∈ area → P u → P y → theta ≤ pins.mass (L.close u scale) → theta ≤ pins.mass (L.close y scale)) :
    ∃ y C, w.place y ∈ area ∧ w.Shore d y ∧ C ⊆ B ∧ C ⊆ L.book r y (flat (f-3*D.near)) ∧
      pins.mass B / 3 ≤ pins.mass C + L.key + L.loss + theta ∧
      ∀ t ∈ C, r.Straddles d t area y ∧ r.right d t area y < r.right d t area i := by
  have hH := D.order.2.1
  have hf' : 2*D.near ≤ f := by omega
  let c := L.core r hi hf'
  have bound := L.bound hr hi (show flat (2*D.near) ≤ flat f from fun _ => hf')
  have big : 3*L.beta < (pins.mass B)^2 := by nlinarith [L.positive.1]
  obtain ⟨s,hs,hheavy⟩ := (c.heavy pins B (fun t ht => L.cut hi hf' (hB ht)) (L.bad hr hi hf' hB hB) big).1
  let older := B.filter (c.Newer s)
  change pins.mass B / 3 < pins.mass older at hheavy
  have sub : older ⊆ L.book r i (flat f) := (Finset.filter_subset ..).trans hB
  have sc := L.cut hi hf' (hB hs)
  obtain ⟨u,hus,hu,heu⟩ := (hc.1 s hs).1.endpoint
  have pu : P u := by
    obtain ⟨v,_,_,hv,he⟩ := hu
    exact he ▸ link.east _ hv
  let keep := fun j t => (old.test area (!d) (flat D.near) j).Minimal t
  have loss : ∀ j, w.place j ∈ area → pins.mass ((L.book r i (flat f)).filter fun t => ¬keep j t) ≤ L.loss :=
    fun _ hj => L.discard bound (.refl old) hj (Nat.le_succ _)
  have east : theta ≤ pins.mass (L.close u scale) := by
    have err := pins.retain (keep u) sub (loss u hu.info.2.1)
    have incl : older.filter (keep u) ⊆ L.close u scale := by
      intro t ht
      obtain ⟨ht,hm⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht,hn⟩ := Finset.mem_filter.mp ht
      obtain ⟨hk,_,_,hp⟩ := L.mem.mp (hB ht)
      have cov := hr.test (show flat (4*D.near) ≤ flat (f-D.near) from fun _ => by simp only [flat]; omega)
        _ (hn.2.2 u hus).1
      obtain ⟨g,hg,ho,he⟩ := (hc.1 t ht).1.endpoint
      have hlt := Round.newer_right hn (hc.1 t ht).1
      have ho' := hr.on (ho.later hu.info.2.2.1 (by omega))
      have h₁ := (hc.1 t ht).2
      have h₂ := (hc.2 s hs t ht).2
      exact Finset.mem_filter.mpr ⟨L.mem.mpr ⟨hk,cov,hm,hp⟩,g,hg,ho',by omega,by omega⟩
    linarith [pins.mass_mono incl]
  have sh := c.refines _ sc.1
  obtain ⟨_,g,hgs,hgw,heg⟩ := Round.west hi (fun _ => hH) sh
  obtain ⟨pre,rest,hh,hn⟩ := sc.2.essential sh hgs
  obtain ⟨j,_,htrip⟩ := hh
  obtain ⟨y,l,py,hy,he,hpath,hl⟩ := link.divert htrip hgw
  have hey : w.num d y = w.left d s := ((w.same d y g).mpr he).trans heg
  have hyi := he.symm ▸ Round.keys_inside sh sc.2 hgs
  have hybit := stable u y hu.info.2.1 hyi pu py east
  let free := older.filter (y ∉ ·)
  let both := free.filter (keep y)
  have hfree : free ⊆ older := Finset.filter_subset ..
  have hboth : both ⊆ free := Finset.filter_subset ..
  have err₁ : pins.mass older ≤ pins.mass free + L.key := by
    apply pins.retain (fun t => y ∉ t) sub
    simpa only [not_not,key] using bound.key y
  have err₂ := pins.retain (keep y) (hfree.trans sub) (loss y hyi)
  change pins.mass free ≤ pins.mass both + L.loss at err₂
  have moved : ∀ t ∈ both, t ∈ L.book r y (flat (f-3*D.near)) ∧ t ∈ L.book old y (flat (4*D.near)) := by
    intro t h
    obtain ⟨ht,hm⟩ := Finset.mem_filter.mp h
    obtain ⟨ht,hyt⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hnew⟩ := Finset.mem_filter.mp ht
    obtain ⟨hk,hcov,_,hp⟩ := L.mem.mp (hB ht)
    have miss := hnew.2.1.missed ⟨j,htrip⟩ hn
    have avoid : ¬Trial.Hit t l := by
      rintro ⟨v,hv,hvt⟩
      rcases List.mem_append.mp (hl hv) with hv | hv
      · exact miss ⟨v,hv,hvt⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl
        · exact Finset.disjoint_left.mp hnew.1.1 hgs hvt
        · exact hyt hvt
    have cost : flat D.near + flat 1 + flat (f-3*D.near) ≤ flat f :=
      fun _ => by simp only [flat,Pi.add_apply]; omega
    have cov := hpath.carry avoid hcov cost
    exact ⟨L.mem.mpr ⟨hk,cov,fun a ha hh => hm _ ha (hr.test le_rfl _ hh),hp⟩,
      L.mem.mpr ⟨hk,hr.test (fun _ => by simp only [flat]; omega) _ cov,hm,hp⟩⟩
  let c' := L.core old hyi (by omega : 2*D.near ≤ 4*D.near)
  let good := fun t => ∃ a ∈ L.close y scale, c'.Good t a
  let C := both.filter good
  have err₃ : pins.mass both ≤ pins.mass C + theta := by
    apply pins.retain good Finset.Subset.rfl
    have hb := L.bad (.refl old) hyi (by omega : 2*D.near ≤ 4*D.near)
      (fun _ h => (moved _ h).2) (show L.close y scale ⊆ _ from Finset.filter_subset ..)
    have hexc := (pins.pair_exception (P := fun t a => ¬c'.Good t a) both (L.close y scale)).trans hb
    have hhx : pins.mass (both.filter fun t => ¬good t) * pins.mass (L.close y scale) ≤ L.beta := by
      apply le_trans _ hexc
      apply mul_le_mul_of_nonneg_right _ (pins.mass_nonneg _)
      apply pins.mass_mono
      intro t ht
      simpa [good] using ht
    by_contra! hh
    have hh' := mul_lt_mul_of_pos_right hh hth
    have hh'' := mul_le_mul_of_nonneg_left hybit (le_trans hth.le hh.le)
    have low := (hh'.trans_le hh'').trans_le hhx

    nlinarith only [low,hbeta,L.positive.2.2]
  have sub' : C ⊆ older := (Finset.filter_subset ..).trans (hboth.trans hfree)
  refine ⟨y,C,hyi,hy,sub'.trans (Finset.filter_subset ..),fun _ h => (moved _ (Finset.mem_filter.mp h).1).1,
    by linarith,?_⟩
  intro t ht
  obtain ⟨ht',hnew⟩ := Finset.mem_filter.mp (sub' ht)
  obtain ⟨ht,a,ha,hg⟩ := Finset.mem_filter.mp ht
  obtain ⟨hm,ho⟩ := moved t ht
  have hleft := (hc.2 s hs t ht').1
  obtain ⟨hh,hnear⟩ := L.force_charge hr hyi hscale (L.sub (fun _ => by simp only [flat]; omega) hm) ho ha (by omega) hg
  have hlt := Round.newer_right hnew (hc.1 t ht').1
  have hgap := (hc.1 s hs).2
  exact ⟨hh,by omega⟩

end Board.Ledger
end OAI.Geometry.Hirsch.Layer
