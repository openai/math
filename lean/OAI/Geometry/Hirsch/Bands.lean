import OAI.Geometry.Hirsch.Straddlers

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}
  {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A) {i j : I} {s : Finset I}

theorem Ray.last (hi : w.place i ∈ area) :
    ∃ j, w.place j ∈ area ∧ w.Ray area d i j ∧
      ∀ g, w.place g ∈ area → w.Ray area d i g → w.Ray area d g j := by
  let keys := Finset.univ.filter fun g => w.place g ∈ area ∧ w.Ray area d i g
  have ne : keys.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,.self⟩⟩
  obtain ⟨j,hj,hm⟩ := keys.exists_max_image (w.loc d) ne
  obtain ⟨_,hj,hr⟩ := Finset.mem_filter.mp hj
  exact ⟨j,hj,hr,fun g hg ht => ht.ordered hr (hm _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg,ht⟩))⟩

omit [Fintype I] in
theorem Round.missed_ray (hr : w.Ray area d i j) (hn : ¬r.Straddles d s area i) :
    ∃ path b, r.Trip area i j b path ∧ b + w.ahead d j = w.ahead d i ∧ ¬Trial.Hit s path := by
  obtain ⟨l,b,ht,hb,hh⟩ := r.trace hr
  exact ⟨l,b,ht,hb,fun ⟨g,hg,hm⟩ => hn ⟨g,hm,(hh _ hg).1⟩⟩

namespace Ledger

def depth (_L : Ledger gate old area d D M A) (i : I) := flat D.band + w.ahead d i

def band (r : w.Round) (i : I) := L.book r i (L.depth i)

theorem range_depth (i : I) : flat D.band ≤ L.depth i ∧ L.depth i ≤ flat (D.band+1) :=
  ⟨le_self_add,fun _ => Nat.add_le_add_left (w.ahead_one d i _) _⟩

theorem base : 2*D.near ≤ D.limit := by have := D.order; omega

theorem band_sub : L.band r i ⊆ L.book r i (flat D.limit) :=
  L.sub ((show flat D.limit ≤ flat D.band from fun _ => D.order.2.2.2.1).trans (L.range_depth i).1)

theorem persists (hs : s ∈ L.band r i) (hn : ¬r.Straddles d s area i)
    (hm : (r.test area (!d) (flat D.low) j).Minimal s) {g : I}
    (hg : w.Ray area d i g) (hj : w.Ray area d g j) : s ∈ L.band r g := by
  obtain ⟨hk,hc,_,hp⟩ := L.mem.mp hs
  obtain ⟨l,b,ht,hb,hmiss⟩ := Round.missed_ray hg hn
  have cost : b + L.depth g ≤ L.depth i := by unfold depth; rw [add_left_comm,hb]
  refine L.mem.mpr ⟨hk,ht.carry hmiss hc cost,fun t hts hc => ?_,hp⟩
  have miss : ¬r.Straddles d t area g := fun ⟨v,hv,ho⟩ => hn ⟨v,hts.subset hv,ho.extend hg⟩
  obtain ⟨l,b,ht,hb,hmiss⟩ := Round.missed_ray hj miss
  apply hm t hts
  apply ht.carry hmiss hc
  have small : b ≤ flat 1 := le_self_add.trans (hb.le.trans (w.ahead_one d g))
  intro x; have := small x
  simp only [Pi.add_apply,flat,Depths.near] at *; omega

theorem common (hr : r.Finer old) (hi : w.place i ∈ area) {err : ℝ}
    (he : pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err) :
    ∃ B ⊆ L.band r i, pins.mass (L.band r i) ≤ pins.mass B + err + L.loss ∧
      ∀ g, w.place g ∈ area → w.Ray area d i g → B ⊆ L.band r g := by
  obtain ⟨j,hj,hij,hh⟩ := Ray.last (d := d) hi
  let free := (L.band r i).filter fun s => ¬r.Straddles d s area i
  let keep := (r.test area (!d) (flat D.low) j).Minimal
  let B := free.filter keep
  have sub : free ⊆ L.band r i := Finset.filter_subset ..
  have first : pins.mass (L.band r i) ≤ pins.mass free + err := by
    apply pins.retain (fun s => ¬r.Straddles d s area i) L.band_sub
    simpa only [not_not] using he
  have hb := L.bound hr hi (show flat (2*D.near) ≤ flat D.limit from fun _ => base)
  have second := pins.retain keep (sub.trans L.band_sub) (L.discard hb hr hj le_rfl)
  refine ⟨B,(Finset.filter_subset ..).trans sub,by unfold B; linarith,?_⟩
  intro g hg ht s hs
  obtain ⟨hs,hm⟩ := Finset.mem_filter.mp hs
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hs
  exact L.persists hs hn hm ht (hh _ hg ht)

theorem barriers (hr : r.Finer old) (hi : w.place i ∈ area) {err b : ℝ}
    (he : pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err)
    (hb : b ≤ pins.mass (L.band r i)) (hpos : 0 < b) (herr : err + L.loss ≤ b/4)
    (hbeta : 12*L.beta < b^2) :
    ∃ t ∈ L.band r i, ∃ B, b/4 ≤ pins.mass B ∧
      (∀ g, w.place g ∈ area → w.Ray area d i g → B ⊆ L.band r g) ∧
      ∀ s ∈ B, s.Nonempty ∧ ∀ g ∈ s, ∀ j ∈ t, w.rank j < w.rank g := by
  obtain ⟨C,hC,hm,hall⟩ := L.common hr hi he
  have big : 3*L.beta < (pins.mass C)^2 := by nlinarith
  let c := L.core r hi (base (D := D))
  have sub := hC.trans L.band_sub
  have hs : ∀ s ∈ C, c.Cut s := fun _ h => L.cut hi base (sub h)
  obtain ⟨t,ht,hh⟩ := (c.heavy pins C hs (L.bad hr hi base sub sub) big).2
  refine ⟨t,hC ht,_,le_trans (by linarith) hh.le,fun g hg ht => (Finset.filter_subset ..).trans (hall g hg ht),?_⟩
  intro s h
  obtain ⟨h,hn⟩ := Finset.mem_filter.mp h
  exact ⟨(c.refines _ (hs _ h).1).nonempty c.inhabited,fun g hg => (hn.2.2 g hg).2⟩

end Ledger
end OAI.Geometry.Hirsch.Layer.Board
