import OAI.Geometry.Hirsch.Bands

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}

omit [Fintype I] in
theorem Pins.extra_hit (pins : Pins p I) (s t : Finset I) (hd : Disjoint t s) :
    p.prob (fun x => s ⊆ pins.success x ∧ ∃ g ∈ t, g ∈ pins.success x) ≤ t.card * pins.rate * pins.weight s :=
  pins.extra s t (fun _ h => Finset.disjoint_left.mp hd h)



namespace Board.Ledger

variable {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A) {i j : I} {s : Finset I} {fresh : Pins p I} (draw : gate.Draw fresh)

def sharp (_L : Ledger gate old area d D M A) (b : Budget) := b + flat ((K+2)*D.step)

def error (U : ℝ) (z : ℝ) := Trial.Tests.capacity K D.max D.step * U * z^K + (K+1)*L.loss

theorem extract (hr : r.Finer old) (hi : w.place i ∈ area) {b : Budget} (hb : b ≤ flat (D.band+1))
    {U : ℝ} (hu : p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (draw.available x)) ≤ U) :
    p.prob (fun x => (r.test area (!d) (L.sharp b) i).Covers (draw.thin x) ∧
      ¬∃ s ∈ L.book r i b, s ⊆ draw.thin x) ≤ L.error U fresh.rate := by
  let a := fun j => b + flat (j*D.step)
  have zero : a 0 = b := by ext; simp [a,flat]
  have next : ∀ j, a j + flat D.step ≤ a (j+1) := by
    intro j x; simp [a,flat,add_mul,add_assoc]
  have bound : ∀ j ≤ K+2, a j ≤ flat D.max := by
    intro j hj x
    exact Nat.add_le_add (hb x) (Nat.mul_le_mul_right _ hj)
  let paths := fun j => r.test area (!d) (a j) i
  have hs := serves hr i _ _ (bound (K+1) (by omega)) (next (K+1)) L.available
  have he := draw.extract hs (r.test area (!d) (flat D.near) i) paths
    (fun j _ => Round.test_mono _ _ _ _ (by rw [zero]; exact le_self_add))
    (fun _ h => h)
    (fun j hj => L.discard (L.bounds _ hr _ hi _ _ (bound _ (by omega)) (next j)) hr hi (Nat.le_succ _))
    ((p.mono fun _ h => hr.test (le_add_self.trans (next (K+1))) _ h).trans hu)
  change p.prob (fun x => (r.test area (!d) (L.sharp b) i).Covers (draw.thin x) ∧
      ¬∃ s ∈ L.book r i (a 0), s ⊆ draw.thin x) ≤ L.error U fresh.rate at he
  rwa [zero] at he

theorem neutral (hr : r.Finer old) (hi : w.place i ∈ area)
    {U : ℝ} (hu : p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (draw.available x)) ≤ U) :
    p.prob (fun x => (r.test area (!d) (flat D.max) i).Covers (draw.thin x)) ≤
      L.error U fresh.rate + pins.mass (L.band r i) := by
  have hb := (L.range_depth i).2
  have h := L.extract draw hr hi hb hu
  apply le_trans _ ((p.either _ _).trans (add_le_add h (pins.family (L.band r i))))
  apply p.mono
  intro x hc
  by_cases hh : ∃ s ∈ L.band r i, s ⊆ draw.thin x
  · obtain ⟨s,hs,hh⟩ := hh
    exact .inr ⟨s,hs,hh.trans (draw.pinned x)⟩
  · exact .inl ⟨Round.test_mono _ _ _ _ (fun j => Nat.add_le_add_right (hb j) _) _ hc,hh⟩

theorem same_site (hr : r.Finer old) (hs : s ∈ L.book r i (flat D.limit))
    (hn : ¬r.Straddles d s area i) (ho : r.On area d i j) {x : Ω}
    (hx : s ⊆ draw.thin x) (hj : j ∈ draw.thin x) : w.place j ∈ s.image w.place := by
  obtain ⟨path,b,ht,hb,hmiss⟩ := Round.missed_ray ho.info.2.2.1 hn
  have small : b ≤ flat 1 := le_self_add.trans (hb.le.trans (w.ahead_one d i))
  have cost : b + flat D.step ≤ flat D.limit := by
    intro k
    have := small k
    have := D.order
    simp only [Depths.near,flat,Pi.add_apply] at *; omega
  have hc := hr.test le_rfl _ (ht.carry hmiss (L.mem.mp hs).2.1 cost)
  obtain ⟨y,hy⟩ := draw.old x
  have pass : draw.thin x ⊆ gate.pass y := Finset.inter_subset_left.trans hy
  obtain ⟨l,hl,hh⟩ := L.available y j ho.info.2.1 (gate.screen _ _ (pass hj))
  obtain ⟨g,hg,hm⟩ := hc l hl
  exact Finset.mem_image.mpr ⟨g,hm,hh g hg (pass (hx hm))⟩

theorem joint_hit (hr : r.Finer old) (hi : w.place i ∈ area) {err U : ℝ}
    (he : pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err)
    (hu : p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (draw.available x)) ≤ U) :
    p.prob (fun x => (r.test area (!d) (L.depth i) i).Covers (draw.thin x) ∧
      r.Straddles d (draw.thin x) area i) ≤ L.error U fresh.rate + err + K*pins.rate*M := by
  let B := L.book r i (flat D.limit)
  let C := B.filter fun s => r.Straddles d s area i
  let E := fun s x => s ⊆ draw.thin x ∧ r.Straddles d (draw.thin x) area i ∧ ¬r.Straddles d s area i
  have each : ∀ s ∈ B, p.prob (E s) ≤ K*pins.rate*pins.weight s := by
    intro s hs
    let t := Finset.univ.filter fun j => r.On area d i j ∧ w.place j ∈ s.image w.place ∧ j ∉ s
    have dis : Disjoint t s := Finset.disjoint_left.mpr fun _ h => (Finset.mem_filter.mp h).2.2.2
    have card : t.card ≤ K := by
      have eq : (t.image w.place).card = t.card := Finset.card_image_iff.mpr (by
        intro u hu v hv he
        exact (Finset.mem_filter.mp hu).2.1.unique (Finset.mem_filter.mp hv).2.1 he)
      have sub : t.image w.place ⊆ s.image w.place := by
        rintro _ hz
        obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp hg).2.2.1
      rw [← eq]; exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (L.mem.mp hs).1)
    apply le_trans _ ((pins.extra_hit s t dis).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr card) pins.pos.le) (pins.positive s).le))
    apply p.mono
    rintro x ⟨hx,⟨j,hj,ho⟩,hn⟩
    exact ⟨hx.trans (draw.pinned x),j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho,
      L.same_site draw hr hs hn ho hx hj,fun h => hn ⟨j,h,ho⟩⟩,draw.pinned x hj⟩
  have hsum : p.prob (fun x => ∃ s ∈ B, E s x) ≤ K*pins.rate*M := by
    apply ((p.union_finset B E).trans (Finset.sum_le_sum each)).trans
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (L.bound hr hi (fun _ => base)).mass (mul_nonneg (by positivity) pins.pos.le)
  have hex := L.extract draw hr hi (b := flat D.limit) (fun _ => D.order.2.2.2.1.trans (Nat.le_succ _)) hu
  have hh := (p.either _ _).trans (add_le_add hex ((pins.family C).trans he))
  apply le_trans _ ((p.either _ _).trans (add_le_add hh hsum))
  apply p.mono
  rintro x ⟨hc,ho⟩
  by_cases hs : ∃ s ∈ B, s ⊆ draw.thin x
  swap
  · exact .inl (.inl ⟨Round.test_mono _ _ _ _ (L.range_depth i).1 _ hc,hs⟩)
  obtain ⟨s,hs,hx⟩ := hs
  by_cases hn : r.Straddles d s area i
  · exact .inl (.inr ⟨s,Finset.mem_filter.mpr ⟨hs,hn⟩,hx.trans (draw.pinned x)⟩)
  · exact .inr ⟨s,hs,hx,ho,hn⟩

end Board.Ledger
end OAI.Geometry.Hirsch.Layer
