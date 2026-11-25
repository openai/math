import OAI.Geometry.Hirsch.Visibility

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Stamp

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} {rule : Rules raw} {n : ℕ} {w : Board I n} {k width : ℕ}
  {tag : Stamp Bit I}

structure Fresh (tag : Stamp Bit I) (fresh : coin.Raw I) (k : ℕ) : Prop where
  tagged : tag.Tagged fresh (k+1)
  age : ∀ i b, b ∈ fresh.bits i → tag.age b = k+1

namespace Fresh

variable (h : tag.Fresh fresh k) (hr : tag.Visible w rule k width)

include h hr in
omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem separate : raw.Separate fresh := by
  intro i j
  apply Finset.disjoint_left.mpr
  intro b hb hb'
  have := (hr.pins _ _ hb).2.1
  have := h.age _ _ hb'
  omega

include h in
omit [Fintype Bit] in
theorem previous (i : I) : tag.scope w k width i ⊆ (↑(fresh.bitsOf Finset.univ))ᶜ := by
  intro b hb hh
  obtain ⟨j,_,hb'⟩ := Finset.mem_biUnion.mp hh
  have := hb.1
  have := h.age _ _ hb'
  omega

include h hr in
omit [Fintype Bit] [Fintype I] in
theorem combined : tag.Tagged (raw.join fresh (h.separate hr)) (k+1) := by
  intro i b hb
  rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨hp,ha,hk⟩ := hr.pins i b hb
    exact ⟨hp,ha.trans (Nat.le_succ _),hk⟩
  · exact h.tagged i b hb

variable {K : ℕ} {gamma alpha : ℝ} (gate : Trial.Gates raw.pins w.place K gamma alpha)
  (he : gate.pass = rule.pass) (hide s : Finset I) (hs : s ⊆ hide)

def draw : gate.Draw fresh.pins where
  available := rule.watch hide s
  old x := ⟨raw.force s x,by rw [he]; exact Finset.sdiff_subset⟩
  pin := rule.watch_pin hs
  independent E t := by
    apply coin.independent (s := ↑(fresh.bitsOf Finset.univ))
    · intro x y eq
      apply congrArg E
      ext i
      exact iff_of_eq ((hr.watch hide s i).mono (h.previous i) x y eq)
    · apply (fresh.reads t).mono
      intro b hb
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩

variable (bars : I → Finset Bit) (hb : ∀ i b, b ∈ bars i → ¬tag.pin b ∧ b ∈ tag.scope w (k+1) width i)

include h hr hb in
omit [Fintype Bit] [Fintype I] in
theorem disjoint (i j : I) : Disjoint (rule.barriers i ∪ bars i) ((raw.join fresh (h.separate hr)).bits j) := by
  apply Finset.disjoint_left.mpr
  intro b hm hp
  rcases Finset.mem_union.mp hm with hm | hm
  · exact (hr.bars i b hm).1 (h.combined hr j b hp).1
  · exact (hb i b hm).1 (h.combined hr j b hp).1

def advance := rule.next (h.separate hr) bars (h.disjoint hr bars hb)

omit [Fintype Bit] [Fintype I] in
theorem visible : tag.Visible w (h.advance hr bars hb) (k+1) width := by
  have sub : ∀ i, tag.scope w k width i ⊆ tag.scope w (k+1) width i :=
    fun _ => tag.scope_mono w (Nat.le_succ k) Set.Subset.rfl le_rfl
  refine ⟨h.combined hr,fun i b hm => ?_,fun i => (hr.ok i).mono (sub i)⟩
  rcases Finset.mem_union.mp hm with hm | hm
  · exact ⟨(hr.bars _ _ hm).1,sub i (hr.bars _ _ hm).2⟩
  · exact hb _ _ hm

theorem reliable {margin loss v : ℝ} (hv : 0 < v) (hv' : v ≤ 1) (hv'' : ∀ i, v ≤ coin.weight (bars i))
    (hrel : rule.Reliable w.place K margin loss) :
    (h.advance hr bars hb).Reliable w.place K (margin*v) loss :=
  rule.reliable_next _ _ _ hrel (fun i => (hr.ok i).mono (h.previous i)) hv hv' hv''

theorem watched (x : Table Bit) (g : I) (hg : g ∈ (h.advance hr bars hb).watch hide s x) :
    g ∈ (h.draw hr gate he hide s hs).thin x ∧ All (bars g) x := by
  let total := raw.join fresh (h.separate hr)
  let y := total.force s x
  obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hg
  obtain ⟨hp,_,hall⟩ := (rule.next_pass _ _ _ y g).mp hm
  have old : g ∈ rule.pass (raw.force s x) := by
    apply (iff_of_eq (hr.pass g y _ ?_)).mp hp
    intro b hscope
    have eq : b ∈ total.bitsOf s ↔ b ∈ raw.bitsOf s := by
      simp only [Raw.bitsOf,Finset.mem_biUnion,total,Raw.join,Finset.mem_union]
      have no : ∀ i, b ∉ fresh.bits i := fun i hi => h.previous g hscope
        (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
      simp [no]
    simp only [y,Raw.force,Table.replace,Finset.mem_coe,eq]
  have pinned := (h.advance hr bars hb).watch_pin hs x hg
  rw [Raw.join_success] at pinned
  refine ⟨Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨old,hn⟩,(Finset.mem_inter.mp pinned).2⟩,?_⟩
  intro b hm
  have free : b ∉ total.bitsOf s := by
    rintro hh
    obtain ⟨j,_,hp⟩ := Finset.mem_biUnion.mp hh
    exact (hb _ _ hm).1 (h.combined hr j b hp).1
  exact (Raw.force_keep free).symm.trans (hall _ hm)

end Fresh
end OAI.Geometry.Hirsch.Layer.Stamp
