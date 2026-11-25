import OAI.Geometry.Hirsch.Merge

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} (rule : Coins.Rules raw)

namespace Coins

omit [Fintype Bit] [Fintype I] in
theorem Raw.force_keep {s : Finset I} {x : Table Bit} {b : Bit} (hb : b ∉ raw.bitsOf s) :
    raw.force s x b = x b := by simp [force,Table.replace,hb]

omit [Fintype Bit] [Fintype I] in
theorem Raw.force_empty (raw : coin.Raw I) (x : Table Bit) : raw.force ∅ x = x := by
  ext; simp [force,bitsOf,Table.replace]

omit [Fintype Bit] [Fintype I] in
theorem Raw.force_reads (raw : coin.Raw I) (s : Finset I) {S : Set Bit} {x y : Table Bit} (h : Set.EqOn x y S) :
    Set.EqOn (raw.force s x) (raw.force s y) S := by
  intro b hb
  simp only [force,Table.replace,h hb]

theorem Raw.force_pin (raw : coin.Raw I) {s : Finset I} {i : I} (hi : i ∉ s) (x : Table Bit) :
    i ∈ raw.pins.success (raw.force s x) ↔ i ∈ raw.pins.success x := by
  simp only [mem]
  apply iff_of_eq
  apply reads_all
  intro b hb
  apply force_keep
  rintro h
  obtain ⟨j,hj,hb'⟩ := Finset.mem_biUnion.mp h
  exact Finset.disjoint_left.mp (raw.unique i j (fun he => hi (he.symm ▸ hj))) hb hb'

def Rules.watch (hide s : Finset I) (x : Table Bit) := rule.pass (raw.force s x) \ hide

theorem Rules.watch_pin {hide s : Finset I} (hs : s ⊆ hide) (x : Table Bit) :
    rule.watch hide s x ⊆ raw.pins.success x := by
  intro g hg
  obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp hg
  exact (raw.force_pin (fun h => hn (hs h)) x).mp ((rule.mem ..).mp hg).1

end Coins

structure Stamp (Bit I : Type) where
  age : Bit → ℕ
  keys : Bit → Finset I
  pin : Bit → Prop

namespace Stamp

variable (tag : Stamp Bit I) {n : ℕ} (w : Board I n) {k width : ℕ}

def scope (k width : ℕ) (i : I) : Set Bit :=
  {b | tag.age b ≤ k ∧ b ∈ w.zone tag.keys (w.home width i) ∧ ∀ j ∈ tag.keys b, w.rank j ≤ w.rank i}

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem scope_mono {i j : I} {k' width' : ℕ} (hk : k ≤ k') (hh : w.home width i ⊆ w.home width' j)
    (hr : w.rank i ≤ w.rank j) : tag.scope w k width i ⊆ tag.scope w k' width' j :=
  fun _ h => ⟨h.1.trans hk,w.zone_mono _ hh h.2.1,fun g hg => (h.2.2 g hg).trans hr⟩

def Tagged (raw : coin.Raw I) (k : ℕ) :=
  ∀ i b, b ∈ raw.bits i → tag.pin b ∧ tag.age b ≤ k ∧ tag.keys b = {i}

structure Visible (rule : Coins.Rules raw) (k width : ℕ) : Prop where
  pins : tag.Tagged raw k
  bars : ∀ i b, b ∈ rule.barriers i → ¬tag.pin b ∧ b ∈ tag.scope w k width i
  ok : ∀ i, Table.Reads (tag.scope w k width i) (rule.ok i)

variable {tag w rule}

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem Tagged.scope (ht : tag.Tagged raw k) (i : I) : ↑(raw.bits i) ⊆ tag.scope w k width i := by
  intro b hb
  obtain ⟨_,hk,he⟩ := ht i b hb
  refine ⟨hk,?_,?_⟩
  · simp [Board.zone,he,Board.home,Board.piece]
  · simp [he]

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem Tagged.whole (ht : tag.Tagged raw k) (i : I) :
    ∀ j b, b ∈ raw.bits j → b ∈ tag.scope w k width i → ↑(raw.bits j) ⊆ tag.scope w k width i := by
  intro j b hb hs c hc
  obtain ⟨_,_,he⟩ := ht _ _ hb
  obtain ⟨_,hk,hc⟩ := ht _ _ hc
  exact ⟨hk,by simpa only [Board.zone,Set.mem_ofPred_eq,he,hc] using hs.2⟩

namespace Visible

variable (h : tag.Visible w rule k width)

include h in
theorem pass (i : I) : Table.Reads (tag.scope w k width i) (fun x => i ∈ rule.pass x) := by
  intro x y he
  have hp := (Coins.reads_all (raw.bits i)).mono (h.pins.scope i) x y he
  have hb := (Coins.reads_all (rule.barriers i)).mono (fun b hb => (h.bars i b hb).2) x y he
  simp only [Coins.Rules.mem,Coins.Raw.mem,hp,hb,h.ok i x y he]

include h in
theorem watch (hide s : Finset I) (i : I) : Table.Reads (tag.scope w k width i)
    (fun x => i ∈ rule.watch hide s x) := by
  intro x y he
  simp only [Coins.Rules.watch,Finset.mem_sdiff,h.pass i _ _ (raw.force_reads s he)]

include h in
omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem enlarge (a : ℕ) : tag.Visible w rule k (width*a) := by
  have sub := fun i => tag.scope_mono w (k := k) le_rfl (w.home_sub width a i) le_rfl
  exact ⟨h.pins,fun i b hb => ⟨(h.bars i b hb).1,sub i (h.bars i b hb).2⟩,
    fun i => (h.ok i).mono (sub i)⟩

include h in
theorem cover (hide s : Finset I) (r : w.Round) (d : Bool) (R : ℕ) (i : I) :
    Table.Reads (tag.scope w k width i) (r.Cover (w.home width i) d R (rule.watch hide s) i) := by
  apply Board.Round.reads_cover
  intro j hj hr
  exact (h.watch hide s j).mono (tag.scope_mono w le_rfl (w.home_eq hj).subset hr.le)

end Visible

def hidden (w : Board I n) (g : I) := Finset.univ.filter fun i => w.place i = w.place g

def bad (rule : Coins.Rules raw) (r : w.Round) (d : Bool) (width R : ℕ) (g : I) :=
  r.Cover (w.home width g) d R (rule.watch (hidden w g) ∅) g

def Capped (tag : Stamp Bit I) (rule : Coins.Rules raw) (r : w.Round) (d : Bool) (width R : ℕ) (t : ℝ) :=
  ∀ hide s, s ⊆ hide → Board.Round.Caps coin tag.keys r d R (rule.watch hide s) width t

variable {r : w.Round} {d : Bool} {R K : ℕ} {t : ℝ}

theorem Visible.capped (h : tag.Visible w rule k width) (ht : 0 ≤ t)
    (hh : ∀ hide s, s ⊆ hide → ∀ i, coin.law.prob (r.Cover (w.home width i) d R (rule.watch hide s) i) ≤ t) :
    tag.Capped rule r d width R t := by
  intro hide s hs j
  refine ⟨ht,fun i hi => (h.watch hide s i).mono ?_,fun i hi => ?_⟩
  · rw [← w.home_eq hi]; exact fun _ hb => hb.2.1
  · rw [← w.home_eq hi]; exact hh hide s hs i

theorem Capped.merge (h : tag.Capped rule r d width R t) {a : ℕ} (ha : 0 < a) :
    tag.Capped rule r d (width*a) R (a*t) := fun hide s hs => (h hide s hs).merge ha

theorem Capped.given (h : tag.Capped rule r d width R t) (g : I) (s : Finset I)
    (hs : ∀ i ∈ s, w.place i = w.place g) : raw.pins.given (bad rule r d width R g) s ≤ t := by
  rw [← raw.forced]
  have sub : s ⊆ hidden w g := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs i hi⟩
  have hh := (h _ s sub (w.place g / width)).bound g rfl
  simp only [bad,Board.Round.Cover,Coins.Rules.watch,Coins.Raw.force_empty]
  exact hh

theorem Visible.screen (h : tag.Visible w rule k width) (thr : Thresholds K) :
    tag.Visible w (rule.screen thr (bad rule r d width R)) k width := by
  refine ⟨h.pins,h.bars,fun i => ?_⟩
  have he := h.cover (hidden w i) ∅ r d R i
  exact fun x y hh => congrArg₂ And (h.ok i x y hh) (raw.reads_screen he (h.pins.whole i) thr x y hh)

theorem available (rule : Coins.Rules raw) (thr : Thresholds K) {x : Table Bit} {g : I}
    (hn : ¬bad rule r d width R g x) :
    ∃ l ∈ r.test (w.home width g) d (Board.flat R) g,
      ∀ j ∈ l, j ∈ (rule.screen thr (bad rule r d width R)).pass x → w.place j = w.place g := by
  obtain ⟨l,hl,hm⟩ := Trial.missed hn
  refine ⟨l,hl,fun j hj hh => ?_⟩
  by_contra he
  apply hm
  refine ⟨j,hj,?_⟩
  simpa [Coins.Rules.watch,Coins.Raw.force_empty,hidden,he] using rule.screen_pass thr _ x hh

end Stamp
end OAI.Geometry.Hirsch.Layer
