import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Runs
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix

section
/-! # Sorting the two sides of a matching by source, then item or bin -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows

variable {h k : ℕ}

def gather (x : Rows h k) (f : B h → B h) : Rows h k :=
  (x.active ∘ f, x.thick ∘ f, x.src ∘ f, x.item ∘ f, x.dest ∘ f)

private abbrev row (h k : ℕ) :=
  Format.lex (.lex .bit (.lex .bit (.addr k))) (.lex (.addr k) (.addr h))

private def entry (x : Rows h k) (i : B h) : (row h k).obj :=
  toLex (toLex (x.active i, toLex (x.thick i, x.src i)),
    toLex (if x.thick i then x.dest i else x.item i, i))

def perm (x : Rows h k) : Equiv.Perm (B h) := Tuple.sort (entry x)

theorem gather_sorted (x : Rows h k) : (x.gather x.perm).sorted := by
  let z := x.gather x.perm
  let key i := toLex (z.active i, toLex (z.thick i, z.src i))
  let val i := if z.thick i then z.dest i else z.item i
  have order {i j} (hij : i ≤ j) : key i < key j ∨ (key i = key j ∧ val i ≤ val j) := by
    have e := Tuple.monotone_sort (entry x) hij
    rcases Prod.Lex.toLex_le_toLex.mp e with a | ⟨a, b⟩
    · exact .inl a
    · exact .inr ⟨a, (Prod.Lex.toLex_le_toLex.mp b).elim LT.lt.le (fun hb => hb.1.le)⟩
  have between {i j p} (ij : i ≤ j) (jp : j ≤ p)
      (ha : z.active i = z.active p) (hb : z.thick i = z.thick p) (hs : z.src i = z.src p) :
      z.active j = z.active i ∧ z.thick j = z.thick i ∧ z.src j = z.src i ∧
        val i ≤ val j ∧ val j ≤ val p := by
    have e : key i = key p := by unfold key; rw [ha, hb, hs]
    have h₁ := order ij
    have h₂ := order jp
    have he : key j = key i := by grind
    have h₃ : z.key j = z.key i := he
    exact ⟨congrArg Prod.fst h₃, congrArg (fun t => t.2.1) h₃,
      congrArg (fun t => t.2.2) h₃, by grind, by grind⟩
  change z.sorted
  constructor
  · intro i j p ij jp hi hp hs
    obtain ⟨ha, hb, he, _⟩ := between ij jp (hi.1.trans hp.1.symm) (hi.2.trans hp.2.symm) hs
    exact ⟨⟨ha.trans hi.1, hb.trans hi.2⟩, he⟩
  · intro i j p ij jp hi hp hs ht
    obtain ⟨_, hb, _, lo, up⟩ := between ij jp (hi.1.trans hp.1.symm) (hi.2.trans hp.2.symm) hs
    simp [val, hb, hi.2, hp.2, ←ht] at lo up
    exact le_antisymm up lo
  · intro i j p ij jp hi hp hs ht
    obtain ⟨_, hb, _, lo, up⟩ := between ij jp (hi.1.trans hp.1.symm) (hi.2.trans hp.2.symm) hs
    simp [val, hb, hi.2, hp.2, ←ht] at lo up
    exact le_antisymm up lo

private theorem prepared (F : Type) [Field F] (h k : ℕ) :
    Circuit F (RowFmt h k) (.vec h (row h k)) entry
      ((RowFmt h k).width + 134 * (Format.vec h (row h k)).width) := by
  classical
  let enc := (Format.vec h (row h k)).code ∘ entry ∘ (RowFmt h k).code.symm
  have t : Install.Depends enc 3 := by
    rintro ⟨i, (j | j | j) | (j | j)⟩
    · refine ⟨{.inl (i, j)}, by simp, fun x y e => ?_⟩
      exact e (.inl (i, j)) (by simp)
    · refine ⟨{.inr (.inl (i, j))}, by simp, fun x y e => ?_⟩
      exact e (.inr (.inl (i, j))) (by simp)
    · refine ⟨{.inr (.inr (.inl (i, j)))}, by simp, fun x y e => ?_⟩
      change (Format.addr k).code ((Format.addr k).code.symm _) _ =
        (Format.addr k).code ((Format.addr k).code.symm _) _
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact e (.inr (.inr (.inl (i, j)))) (by simp)
    · let flag : (RowFmt h k).pins := .inr (.inl (i, ()))
      let data (b : Bool) (l : (Format.addr k).pins) : (RowFmt h k).pins :=
        .inr (.inr (.inr (if b then .inr (i, l) else .inl (i, l))))
      have value (x : (RowFmt h k).pins → Bool) :
          enc x (i, .inr (.inl j)) = x (data (x flag) j) := by
        change (Format.addr k).code (if x flag then (Format.addr k).code.symm (x ∘ data true)
          else (Format.addr k).code.symm (x ∘ data false)) j = _
        cases x flag <;> simp
      refine ⟨{flag, data false j, data true j}, Finset.card_le_three, fun x y e => ?_⟩
      rw [value, value, e flag (by simp)]
      cases y flag <;> exact e _ (by simp)
    · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
  exact t.bnet F

theorem cheap_perm (F : Type) [Field F] (h k : ℕ) :
    Cheap F h (h + k + 1) (RowFmt h k) (Perm h) (fun x => ⇑(perm x)) 5 := by
  have flag := Coloring.small (F := F) (A := .pair .bit .bit) (by simp) (fun x => decide (x.1 < x.2))
  have cmp := lex_lt (lex_lt flag (lex_lt flag (numeric_lt F k))) (lex_lt (numeric_lt F k) (numeric_lt F h))
  have out := Circuit.project (F := F) (A := .vec h (row h k)) (D := Perm h)
    (f := fun x i => (x i).2.2) (fun z => (z.1, .inr (.inr z.2))) (fun _ _ => rfl)
  have hs := cmp.sort h
  have net := ((prepared F h k).comp hs).comp out
  refine ⟨_, net, ?_⟩
  simp only [Format.width_pair, Format.width_lex, Format.width_addr, Format.width_vec]
  rw [Format.width_bit]
  ring_nf
  omega

theorem cheap_gather (F : Type) [Field F] (h k : ℕ) :
    Cheap F h (h + k + 1) (.pair (RowFmt h k) (Perm h)) (RowFmt h k)
      (fun x => gather x.1 x.2) 20 := by
  let A := Format.pair (RowFmt h k) (Perm h)
  have hw : A.width ≤ 2 ^ h * (100 + (h + k + 1)) ^ 2 := by
    simp only [A, Format.width_pair, Format.width_vec, Format.width_addr]
    rw [Format.width_bit]
    ring_nf
    omega
  have x := Cheap.id F hw
  have bit := Cheap.lookup F h (h + k + 1) .bit (by omega) (by simp)
  have addr := Cheap.lookup F h (h + k + 1) (.addr k) (by omega) (by simp; omega)
  have a := (x.fst.fst.pair x.snd).comp bit
  have b := (x.fst.snd.fst.pair x.snd).comp bit
  have c := (x.fst.snd.snd.fst.pair x.snd).comp addr
  have d := (x.fst.snd.snd.snd.fst.pair x.snd).comp addr
  have e := (x.fst.snd.snd.snd.snd.pair x.snd).comp addr
  exact (a.pair (b.pair (c.pair (d.pair e)))).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

section
/-! # Circuits computing one rank per row with no factor for alphabet size -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable (F : Type) [Field F] {h k t : ℕ}

abbrev Column (h k : ℕ) := Format.vec h (.addr k)

theorem column_width (h : ℕ) (hk : k ≤ t) : (Column h k).width ≤ 2 ^ h * (100 + t) ^ 1 := by
  simp only [Column, Format.width_vec, Format.width_addr, pow_one]
  exact Nat.mul_le_mul_left _ (by omega)

theorem cheap_eq (hk : k ≤ t) :
    Cheap F 0 t (.pair (.addr k) (.addr k)) .bit (fun z => decide (z.1 = z.2)) 2 := by
  refine ⟨_, numeric_eq F k, ?_⟩
  simp only [Format.width_pair, Format.width_addr]
  rw [Format.width_bit]
  ring_nf
  omega

private theorem cheap_back (hh : h ≤ t) (hk : k ≤ t) :
    Cheap F h t (Column h k) (Perm h) back 10 := by
  let A := Format.pair (.addr k) (.addr k)
  let D := Format.pair (.addr h) (.addr h)
  have ha : A.width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp [A]; ring_nf; omega
  have hd : D.width ≤ 2 ^ 0 * (100 + t) ^ 2 := by simp [D]; ring_nf; omega
  have pick (i : B h) : Cheap F 0 t A (.addr h)
      (fun z => if z.1 = z.2 then previous i else i) 6 := by
    have H := ((Cheap.const F ha hd (previous i, i)).pair (cheap_eq F hk)).comp ((cheap_select F h).widen hh)
    convert H.mono (d := 6) (by decide) using 1
    funext z
    simp
  have hw := column_width h hk
  have prev : Cheap F h t (Column h k) (Column h k) (fun f => f ∘ previous) 2 :=
    Cheap.project F hw hw (fun i => (previous i.1, i.2)) (fun _ _ => rfl)
  exact (((prev.pair (Cheap.id F hw)).zip.comp (Cheap.map _ pick)).mono (by decide))

theorem cheap_leader (hh : h ≤ t) (hk : k ≤ t) :
    Cheap F h t (Column h k) (Perm h) leader 15 := by
  have a := Cheap.id F (column_width h hh)
  have square := (a.pair a).comp (Cheap.lookup F h t (.addr h) hh (by simpa))
  exact ((cheap_back F hh hk).comp (square.iterate hh)).mono (by decide)

private theorem cheap_offset (hh : h ≤ t) :
    Cheap F h t (Perm h) (Perm h) (fun a i => i - a i) 15 := by
  have width := column_width h hh
  have base := Cheap.id F width
  have get := Cheap.lookup F h t (.addr h) hh (by simpa)
  have neg := ((Cheap.const F width width (fun i => -i)).pair base).comp get
  have inp := ((Cheap.const F width width id).pair neg).zip
  have add : Cheap F 0 t (.pair (.addr h) (.addr h)) (.addr h) (fun x => x.1 + x.2) 4 := by
    refine ⟨_, numeric_add F h, ?_⟩
    simp only [Format.width_pair, Format.width_addr]
    ring_nf
    omega
  convert (inp.comp (Cheap.map (fun _ => _) (fun _ => add))).mono (d := 15) (by decide) using 1
  funext a i
  exact sub_eq_add_neg _ _

theorem cheap_order (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) (fun f => ⇑(order f)) 41 := by
  have ha := column_width h (Nat.le_add_left k h)
  have hb : (Format.vec h .bit).width ≤ 2 ^ h * (100 + (h + k)) ^ 1 := by
    rw [Format.width_vec, Format.width_bit, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  have H := ((Cheap.id F ha).pair (Cheap.const F ha hb (fun _ => true))).comp (cheap_permutation F h k)
  exact H.mono (by decide)

theorem cheap_sorted_leader (h k : ℕ) : Cheap F h (h + k) (Column h k) (Perm h)
    (fun f => leader (f ∘ order f)) 44 := by
  have hh := Nat.le_add_right h k
  have hk := Nat.le_add_left k h
  have sorted := ((Cheap.id F (column_width h hk)).pair (cheap_order F h k)).comp
    (Cheap.lookup F h (h + k) (.addr k) hh (by simp))
  exact (sorted.comp (cheap_leader F hh hk)).mono (by decide)

theorem cheap_inverse_order (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) (fun f => ⇑(order f).symm) 101 := by
  obtain ⟨g, hg, he⟩ := cheap_inverse F h
  have H := (cheap_order F h k).comp (hg.widen (Nat.le_add_right h k))
  have eq : g ∘ (fun f : B h → B k => ⇑(order f)) = fun f => ⇑(order f).symm := funext fun f => he _
  rwa [eq] at H

theorem cheap_groupRank (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) groupRank 103 := by
  have hh := Nat.le_add_right h k
  have a := (cheap_sorted_leader F h k).comp (cheap_offset F hh)
  have H := (a.pair (cheap_inverse_order F h k)).comp (Cheap.lookup F h (h + k) (.addr h) hh (by simp))
  exact H.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-! # First, last and other occurrences of a key -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring
variable {h k : ℕ} (f : B h → B k)

def groupFirst := order f ∘ leader (f ∘ order f) ∘ (order f).symm

def groupLast := Fin.rev ∘ groupFirst (f ∘ Fin.rev) ∘ Fin.rev

def other (i : B h) := if groupFirst f i = i then groupLast f i else groupFirst f i

theorem first_spec (i : B h) :
    f (groupFirst f i) = f i ∧ ∀ j, f j = f i → groupFirst f i ≤ j := by
  let e := order f
  obtain ⟨he, hl⟩ := leader_spec (f ∘ e) (order_mono f) (e.symm i)
  have ht : f (groupFirst f i) = f i := he.trans (congrArg f (e.apply_symm_apply i))
  refine ⟨ht, fun j hj => ?_⟩
  have hle := hl (e.symm j) (by simpa using hj)
  have h := order_le f hle
  change f (groupFirst f i) < f (e (e.symm j)) ∨
    f (groupFirst f i) = f (e (e.symm j)) ∧ groupFirst f i ≤ e (e.symm j) at h
  rw [Equiv.apply_symm_apply, ht, hj] at h
  exact (h.resolve_left (lt_irrefl _)).2

theorem last_spec (i : B h) :
    f (groupLast f i) = f i ∧ ∀ j, f j = f i → j ≤ groupLast f i := by
  obtain ⟨he, hl⟩ := first_spec (f ∘ Fin.rev) i.rev
  refine ⟨by simpa [groupLast] using he, fun j hj => ?_⟩
  simpa [groupLast] using Fin.rev_le_rev.mpr (hl j.rev (by simpa using hj))

theorem other_spec (i : B h) :
    f (other f i) = f i ∧ ∀ j, f j = f i → j ≠ i → other f i ≠ i := by
  obtain ⟨he, hl⟩ := first_spec f i
  obtain ⟨he', hr⟩ := last_spec f i
  unfold other
  split_ifs with h
  · exact ⟨he', fun j hj hn h' => hn (le_antisymm ((hr j hj).trans_eq h')
      (h.symm.trans_le (hl j hj)))⟩
  · exact ⟨he, fun _ _ _ => h⟩

def lastRank := groupRank f ∘ groupLast f

theorem lastRank_val (i : B h) : (lastRank f i).val + 1 = Control.histogram f (f i) none := by
  obtain ⟨he, hr⟩ := last_spec f i
  rw [lastRank, Function.comp_apply, groupRank_val, Control.rank, Control.histogram_some, he,
    Control.histogram_none]
  let S := Finset.univ.filter fun j => f j = f i
  have hi : groupLast f i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  change _ = S.card
  rw [← Finset.card_erase_add_one hi]
  congr 2
  ext j
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  exact ⟨fun h => ⟨h.2.ne, h.1⟩, fun h => ⟨h.2, (hr j h.2).lt_of_ne h.1⟩⟩

variable (F : Type) [Field F]

theorem cheap_first (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) groupFirst 103 := by
  have get := Cheap.lookup F h (h + k) (.addr h) (by omega) (by simp)
  have a := ((cheap_order F h k).pair (cheap_sorted_leader F h k)).comp get
  exact ((a.pair (cheap_inverse_order F h k)).comp get).mono (by decide)

theorem cheap_last (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) groupLast 110 := by
  have hw := column_width h (Nat.le_add_left k h)
  have hi := column_width h (Nat.le_add_right h k)
  have get := Cheap.lookup F h (h + k) (.addr h) (by omega) (by simp)
  have rev : Cheap F h (h + k) (Column h k) (Column h k) (fun f => f ∘ Fin.rev) 2 :=
    Cheap.project F hw hw (fun i => (i.1.rev, i.2)) (fun _ _ => rfl)
  have a := rev.comp (cheap_first F h k)
  have r := Cheap.const F hw hi Fin.rev
  have b := (a.pair r).comp get
  exact ((r.pair b).comp get).mono (by decide)

theorem cheap_other (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) other 120 := by
  have hh := Nat.le_add_right h k
  have i := Cheap.const F (column_width h (Nat.le_add_left k h)) (column_width h hh) id
  have a := cheap_first F h k
  have b := cheap_last F h k
  have eq := (a.pair i).zip.comp (Cheap.map (fun _ => _) (fun _ => cheap_eq F hh))
  have H := (((b.pair a).zip.pair eq).zip.comp (Cheap.map (fun _ => _) (fun _ => (cheap_select F h).widen hh)))
  convert H.mono (d := 120) (by decide) using 1
  funext x i
  simp [other]

theorem cheap_lastRank (h k : ℕ) :
    Cheap F h (h + k) (Column h k) (Perm h) lastRank 112 :=
  (((cheap_groupRank F h k).pair (cheap_last F h k)).comp
    (Cheap.lookup F h (h + k) (.addr h) (by omega) (by simp))).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-! # Treating a tuple of fixed-width fields as one comparison key -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable {h k : ℕ} (A : Format)

private def layout : slots (word A.width) ≃ A.pins :=
  @Fintype.equivOfCardEq _ _ (slotsFintype _) A.finite
    ((card_slots _).trans (wd_word _))

def Format.serial : A.obj ≃ B A.width :=
  (A.code.trans ((layout A).symm.arrowCongr (Equiv.refl _))).trans (Format.addr _).code.symm

def Format.keys (f : B h → A.obj) := A.serial ∘ f

theorem cheap_keys (F : Type) [Field F] (h : ℕ) (ha : A.width ≤ k) :
    Cheap F h k (.vec h A) (Column h A.width) A.keys 2 := by
  have b : (Format.vec h A).width ≤ 2 ^ h * (100 + k) ^ 1 := by
    rw [Format.width_vec, pow_one]
    exact Nat.mul_le_mul_left _ (by omega)
  apply Cheap.project F b (column_width h ha) (fun i => (i.1, layout A i.2))
  intro f i
  change (Format.addr A.width).code (A.serial (f i.1)) i.2 = _
  rw [Format.serial, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem keys_rank [DecidableEq A.obj] (f : B h → A.obj) (i : B h) :
    (groupRank (A.keys f) i).val = Control.rank f i := by
  rw [groupRank_val, Control.rank, Control.rank, Control.histogram_some, Control.histogram_some]
  congr 1
  ext j
  simp [Format.keys]

theorem keys_last [DecidableEq A.obj] (f : B h → A.obj) (i : B h) :
    (lastRank (A.keys f) i).val + 1 = (Finset.univ.filter fun j => f j = f i).card := by
  rw [lastRank_val, Control.histogram_none]
  congr 1
  ext j
  simp [Format.keys]

/-- Comparing the counts in two fibers tests whether all rows in the
first fiber agree on their additional field. -/
theorem same_group {D : Format} [DecidableEq A.obj] [DecidableEq D.obj]
    (f : B h → A.obj) (g : B h → D.obj) (i : B h) :
    lastRank (A.keys f) i = lastRank ((A.pair D).keys (fun j => (f j, g j))) i ↔
      ∀ j, f j = f i → g j = g i := by
  have hl := keys_last A f i
  have hr := keys_last (A.pair D) (fun j => (f j, g j)) i
  let s := Finset.univ.filter fun j => f j = f i
  let t := Finset.univ.filter fun j => (f j, g j) = (f i, g i)
  have sub : t ⊆ s := fun j h => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, congrArg Prod.fst (Finset.mem_filter.mp h).2⟩
  constructor
  · intro h j he
    rw [h] at hl
    have eq : t = s := Finset.eq_of_subset_of_card_le sub (hl.symm.trans hr).le
    have hm : j ∈ t := eq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    exact congrArg Prod.snd (Finset.mem_filter.mp hm).2
  · intro h
    have eq : s = t := Finset.Subset.antisymm (fun j he => by
      obtain ⟨_, he⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext he (h j he)⟩) sub
    exact Fin.ext (Nat.succ_inj.mp (hl.trans ((congrArg Finset.card eq).trans hr.symm)))

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# Matching rows at equal rank

The first key distinguishes the two colors. The second key erases the
color and adds its within-color rank. Every active fiber of that key
contains at most one row of each color. Comparing two group counts
then tests that a thin item lies entirely in one thick bin.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows

variable {h k : ℕ} (x : Rows h k)

abbrev ColorKey (k : ℕ) := Format.pair .bit (.pair .bit (.addr k))
abbrev RankKey (h k : ℕ) := Format.pair .bit (.pair (.addr k) (.addr h))
abbrev ItemKey (k : ℕ) := (ColorKey k).pair (.addr k)
abbrev BinKey (k : ℕ) := Format.pair .bit (.addr k)

def ordinal := groupRank ((ColorKey k).keys x.key)

def rankKey (i : B h) : (RankKey h k).obj := (x.active i, x.src i, x.ordinal i)

def friend := other ((RankKey h k).keys x.rankKey)

theorem friend_spec : x.friends x.friend := by
  intro i hi
  let f := (RankKey h k).keys x.rankKey
  let a := x.friend i
  have ord j : (x.ordinal j).val = Control.rank x.key j := keys_rank (ColorKey k) x.key j
  have eqn (j : B h) : f j = f i ↔ x.active j = true ∧ x.src j = x.src i ∧
      Control.rank x.key j = Control.rank x.key i := by
    simp only [f, Format.keys, Function.comp_apply, Equiv.apply_eq_iff_eq, rankKey,
      Prod.mk.injEq, hi.1, Fin.ext_iff, ord]
  have ho := other_spec f i
  obtain ⟨active, src, rank⟩ := (eqn a).mp ho.1
  have thick (ha : a ≠ i) : x.isThick a := by
    refine ⟨active, ?_⟩
    cases h : x.thick a
    · apply False.elim
      apply ha
      apply Control.rank_injective x.key
      exact Prod.ext (Prod.ext (active.trans hi.1.symm) (Prod.ext (h.trans hi.2.symm) src)) rank
    · rfl
  refine ⟨?_, fun h => ⟨thick h, src, rank⟩⟩
  intro j hj hs hr
  have ne : j ≠ i := by intro eq; subst j; simp [isThin, isThick] at hi hj; grind
  have ha := thick (ho.2 j ((eqn _).mpr ⟨hj.1, hs, hr⟩) ne)
  apply Control.rank_injective x.key
  exact Prod.ext (Prod.ext (ha.1.trans hj.1.symm) (Prod.ext (ha.2.trans hj.2.symm) (src.trans hs.symm)))
    (rank.trans hr.symm)

def itemKey (i : B h) : (ItemKey k).obj := (x.key i, x.item i)

def binKey (i : B h) : (BinKey k).obj := (decide (x.friend i = i), x.dest (x.friend i))

def sameBin (i : B h) :=
  decide (lastRank ((ItemKey k).keys x.itemKey) i =
    lastRank (((ItemKey k).pair (BinKey k)).keys (fun j => (x.itemKey j, x.binKey j))) i)

def mask (i : B h) := x.active i && !x.thick i && !(x.binKey i).1 && x.sameBin i

theorem mask_iff (i : B h) : x.mask i = true ↔ x.passes x.friend i := by
  have he : x.sameBin i = true ↔ ∀ j, x.itemKey j = x.itemKey i → x.binKey j = x.binKey i := by
    rw [sameBin, decide_eq_true_eq, same_group]
  simp only [mask, Bool.and_eq_true, Bool.not_eq_true', he, itemKey, key, binKey,
    decide_eq_false_iff_not, Prod.mk.injEq, passes, isThin]
  grind

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

section
/-!
# Bounded-fan-in costs for ordered matching

Use two rank comparisons per row. The costs depend polynomially on
the address and label widths and linearly on the padded array length.
They do not depend on the number of distinct keys or the item size.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
variable (F : Type) [Field F] (h k : ℕ)

def overhead (h k : ℕ) := 2 * h + 4 * k + 4

private theorem widths :
    h + (ColorKey k).width ≤ overhead h k ∧
    h + (RankKey h k).width ≤ overhead h k ∧
    h + (ItemKey k).width ≤ overhead h k ∧
    h + ((ItemKey k).pair (BinKey k)).width ≤ overhead h k := by
  simp only [ColorKey, RankKey, ItemKey, BinKey, Format.width_pair, Format.width_addr, overhead]
  rw [Format.width_bit]
  omega

theorem row_width : (RowFmt h k).width ≤ 2 ^ h * (100 + overhead h k) ^ 1 := by
  simp only [RowFmt, Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add, pow_one]
  rw [Format.width_bit]
  exact Nat.mul_le_mul_left _ (by unfold overhead; omega)

private theorem cheap_color :
    Cheap F h (overhead h k) (RowFmt h k) (.vec h (ColorKey k)) key 10 := by
  have x := Cheap.id F (row_width h k)
  exact ((x.fst.pair (x.snd.fst.pair x.snd.snd.fst).zip).zip).mono (by decide)

theorem cheap_friend : Cheap F h (overhead h k) (RowFmt h k) (Perm h) friend 122 := by
  have hc := (widths h k).1
  have hr := (widths h k).2.1
  have x := Cheap.id F (row_width h k)
  have key := (cheap_color F h k).comp (cheap_keys (ColorKey k) F h (by omega))
  have rank := key.comp ((cheap_groupRank F h _).widen hc)
  have row := (x.fst.pair (x.snd.snd.fst.pair rank).zip).zip
  have keys := row.comp (cheap_keys (RankKey h k) F h (by omega))
  exact (keys.comp ((cheap_other F h _).widen hr)).mono (by decide)

private theorem cheap_missed :
    Cheap F h (overhead h k) (RowFmt h k) (.vec h .bit) (fun x i => decide (friend x i = i)) 125 := by
  have hh : h ≤ overhead h k := by unfold overhead; omega
  have idx := Cheap.const F (row_width h k) (column_width h hh) id
  have eq := Cheap.map (h := h) (fun _ => _) (fun _ => cheap_eq F hh)
  exact (((cheap_friend F h k).pair idx).zip.comp eq).mono (by decide)

private theorem cheap_item :
    Cheap F h (overhead h k) (RowFmt h k) (.vec h (ItemKey k)) itemKey 12 := by
  have x := Cheap.id F (row_width h k)
  exact ((cheap_color F h k).pair x.snd.snd.snd.fst).zip.mono (by decide)

private theorem cheap_bin :
    Cheap F h (overhead h k) (RowFmt h k) (.vec h (BinKey k)) binKey 127 := by
  have hh : h ≤ overhead h k := by unfold overhead; omega
  have hk : k ≤ overhead h k := by unfold overhead; omega
  have x := Cheap.id F (row_width h k)
  have addr := (x.snd.snd.snd.snd.pair (cheap_friend F h k)).comp
    (Cheap.lookup F h (overhead h k) (.addr k) hh (by simpa))
  exact ((cheap_missed F h k).pair addr).zip.mono (by decide)

private theorem cheap_sameBin :
    Cheap F h (overhead h k) (RowFmt h k) (.vec h .bit) sameBin 135 := by
  have hh : h ≤ overhead h k := by unfold overhead; omega
  have count (A : Format) (hw : h + A.width ≤ overhead h k) :=
    (cheap_keys A F h (by omega)).comp ((cheap_lastRank F h _).widen hw)
  have first := cheap_item F h k
  have both := (first.pair (cheap_bin F h k)).zip
  have a := first.comp (count _ (widths h k).2.2.1)
  have b := both.comp (count _ (widths h k).2.2.2)
  have eq := Cheap.map (h := h) (fun _ => _) (fun _ => cheap_eq F hh)
  exact ((a.pair b).zip.comp eq).mono (by decide)

private theorem cheap_bool (f : Bool × Bool → Bool) :
    Cheap F 0 (overhead h k) (.pair .bit .bit) .bit f 2 := by
  refine ⟨_, Coloring.small (A := .pair .bit .bit) (by simp) f, ?_⟩
  change 2 + 1 + 200 ≤ _
  ring_nf
  omega

theorem cheap_mask : Cheap F h (overhead h k) (RowFmt h k) (.vec h .bit) mask 140 := by
  have x := Cheap.id F (row_width h k)
  have notAnd := Cheap.map (h := h) (fun _ => _) (fun _ => cheap_bool F h k (fun z => z.1 && !z.2))
  have andNet := Cheap.map (h := h) (fun _ => _) (fun _ => cheap_bool F h k (fun z => z.1 && z.2))
  have thin := (x.fst.pair x.snd.fst).zip.comp notAnd
  have matched := (thin.pair (cheap_missed F h k)).zip.comp notAnd
  exact ((matched.pair (cheap_sameBin F h k)).zip.comp andNet).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

/-! # Returning the matching mask and mate addresses in the original order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
variable {h k : ℕ}

def control (x : Rows h k) : (B h → Bool) × (B h → B h) :=
  let y := x.gather x.perm
  (y.mask ∘ x.perm.symm, x.perm ∘ y.friend ∘ x.perm.symm)

theorem cheap_control (F : Type) [Field F] (h k : ℕ) :
    Cheap F h (overhead h k) (RowFmt h k) (.pair (.vec h .bit) (Perm h)) control 150 := by
  have hh : h ≤ overhead h k := by unfold overhead; omega
  have hk : h + k + 1 ≤ overhead h k := by unfold overhead; omega
  have forward := (cheap_perm F h k).widen hk
  have backward : Cheap F h (overhead h k) (RowFmt h k) (Perm h)
      (fun x => ⇑(perm x).symm) 101 := by
    obtain ⟨g, hg, he⟩ := cheap_inverse F h
    have H := forward.comp (hg.widen hh)
    have eq : g ∘ (fun x : Rows h k => ⇑(perm x)) = fun x => ⇑(perm x).symm := funext fun x => he _
    rwa [eq] at H
  have sorted := ((Cheap.id F (row_width h k)).pair forward).comp ((cheap_gather F h k).widen hk)
  have bit := Cheap.lookup F h (overhead h k) .bit hh (by rw [Format.width_bit]; omega)
  have addr := Cheap.lookup F h (overhead h k) (.addr h) hh (by simpa)
  have keep := ((sorted.comp (cheap_mask F h k)).pair backward).comp bit
  have mate := ((sorted.comp (cheap_friend F h k)).pair backward).comp addr
  exact (keep.pair ((forward.pair mate).comp addr)).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

/-!
# The matching decoded from the row circuit

The selected mask is constant on each thin item. On this mask the friend
pointer gives a distinct thick mate, with common destination for the item.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
open Packing Finset
open scoped Classical

variable {E P : Type} {r h k : ℕ} {src dst : E → P} {ix : E → Cell r}
  (x : P → Rows h k) (pos : E → B h) {tag : P → B k}

/-- Both the mask and the mate address are specified, for every unit. -/
private structure SortedControls (m : Matching src dst ix) : Prop where
  mask : ∀ e, (m.plan (src e) (ix e)).isSome = (x (src e)).mask (pos e)
  mate : ∀ e, pos (m.mate e) = (x (src e.val)).friend (pos e.val)

private theorem decode {c : Color r} (enc : ∀ p, (x p).Represents src dst ix c p pos (tag p)) :
    ∃ m : Matching src dst ix, m.color = c ∧ SortedControls x pos m := by
  let take e := (x (src e)).passes (x (src e)).friend (pos e)
  have pick (e : E) : ∃ d : E, take e → src d = src e ∧
      pos d = (x (src e)).friend (pos e) ∧ Packing.thick c (ix d) := by
    by_cases he : take e
    · have ht := ((x (src e)).friend_spec _ he.1).2 he.2.1
      obtain ⟨d, hd, hp⟩ := (enc _).onto _ ht.1.1 (ht.2.1.trans ((enc _).source e rfl))
      exact ⟨d, fun _ => ⟨hd, hp, ((enc _).isThick d hd).mp (hp.symm ▸ ht.1)⟩⟩
    · exact ⟨e, fun h => (he h).elim⟩
  choose mate hm using pick
  have same (e d : E) (he : take e) (hs : src d = src e) (hi : ix d = ix e) :
      take d ∧ dst (mate d) = dst (mate e) := by
    let z := enc (src e)
    have ht := (z.isThin d hs).mpr (hi.symm ▸ (z.isThin e rfl).mp he.1)
    have hsrc := (z.source d hs).trans (z.source e rfl).symm
    have hit := (z.item d e hs rfl).mpr hi
    obtain ⟨hne, hdst⟩ := he.2.2 (pos d) ht hsrc hit
    have hd : take d := by
      unfold take
      rw [hs]
      refine ⟨ht, hne, fun j hj h₁ h₂ => ?_⟩
      obtain ⟨hn, h⟩ := he.2.2 j hj (h₁.trans hsrc) (h₂.trans hit)
      exact ⟨hn, h.trans hdst.symm⟩
    refine ⟨hd, (z.dest _ _ ((hm d hd).1.trans hs) (hm e he).1).mp ?_⟩
    rw [(hm d hd).2.1, (hm e he).2.1, hs]
    exact hdst
  let plan p t :=
    if h : ∃ e, src e = p ∧ ix e = t ∧ take e then some (dst (mate h.choose)) else none
  have used p t (h : (plan p t).isSome) : ∃ e, src e = p ∧ ix e = t ∧ take e := by
    by_contra hn
    simp only [plan, dite_eq_right hn, Option.isSome_none, Bool.false_eq_true] at h
  have spec (e : E) (he : take e) : plan (src e) (ix e) = some (dst (mate e)) := by
    have h : ∃ d, src d = src e ∧ ix d = ix e ∧ take d := ⟨e, rfl, rfl, he⟩
    unfold plan
    rw [dite_eq_left h, (same e _ he h.choose_spec.1 h.choose_spec.2.1).2]
  have selected (e : E) : (plan (src e) (ix e)).isSome ↔ take e := by
    constructor
    · intro h
      obtain ⟨d, hs, hi, hd⟩ := used _ _ h
      exact (same d e hd hs.symm hi.symm).1
    · intro he
      simp [spec e he]
  let f : {e // (plan (src e) (ix e)).isSome} ↪ E := ⟨fun e => mate e.val, by
    rintro ⟨e, he⟩ ⟨d, hd⟩ eq
    have te := (selected e).mp he
    have td := (selected d).mp hd
    have hs := (hm d td).1.symm.trans ((congrArg src eq.symm).trans (hm e te).1)
    have hp := (hm e te).2.1.symm.trans ((congrArg pos eq).trans (hm d td).2.1)
    unfold take at td
    rw [hs] at hp td
    exact Subtype.ext ((enc _).inj e d rfl hs ((x _).friend_injective (x _).friend_spec te td hp))⟩
  let m : Matching src dst ix := {
    color := c
    plan := plan
    thin p t h := by
      obtain ⟨e, _, rfl, he⟩ := used p t h
      exact ((enc _).isThin e rfl).mp he.1
    used p t h := by
      obtain ⟨e, hs, hi, _⟩ := used p t h
      exact ⟨e, hs, hi⟩
    mate := f
    spec e := by
      have he := (selected e.val).mp e.property
      exact ⟨(hm _ he).2.2, (hm _ he).1, spec _ he⟩ }
  refine ⟨m, rfl, ?_, fun e => (hm _ ((selected _).mp e.property)).2.1⟩
  intro e
  exact Bool.eq_iff_iff.mpr ((selected e).trans ((x _).mask_iff _).symm)

private theorem decoded_count [Fintype E] [Fintype P] {c : Color r}
    (enc : ∀ p, (x p).Represents src dst ix c p pos (tag p)) (sorted : ∀ p, (x p).sorted)
    (b K : ℕ) (size : ∀ p t, (univ.filter fun e => src e = p ∧ ix e = t).card ≤ b)
    (deg : ∀ p, ((univ.filter fun e => src e = p).image dst).card ≤ K)
    {m : Matching src dst ix} (hm : SortedControls x pos m) :
    (∑ p, min (univ.filter fun e => src e = p ∧ ¬Packing.thick c (ix e)).card
        (univ.filter fun e => src e = p ∧ Packing.thick c (ix e)).card) ≤
      m.count + b * K * Fintype.card P := by
  let selected := univ.filter fun e => (m.plan (src e) (ix e)).isSome
  have ht (p : P) :
      (univ.filter fun e => src e = p ∧ (x p).passes (x p).friend (pos e)) =
        selected.filter fun e => src e = p := by
    ext e
    simp only [selected, mem_filter, mem_univ, true_and, hm.mask, mask_iff]
    by_cases hp : src e = p <;> simp [hp]
  have h := sum_le_sum (s := univ) fun p _ =>
    (enc p).local_count (sorted p) (x p).friend_spec b K (size p) (deg p)
  simp_rw [ht] at h
  rw [sum_add_distrib, ← card_eq_sum_card_fiberwise (fun e _ => mem_univ (src e)),
    sum_const, card_univ, Nat.nsmul_eq_mul, mul_comm (Fintype.card P)] at h
  exact h

private theorem gather_enc {c : Color r} (enc : ∀ p, (x p).Represents src dst ix c p pos (tag p))
    (p : P) : ((x p).gather (x p).perm).Represents src dst ix c p
      (fun e => (x (src e)).perm.symm (pos e)) (tag p) := by
  let z := enc p
  constructor
  · intro e f he hf eq
    rw [he, hf] at eq
    exact z.inj e f he hf ((x p).perm.symm.injective eq)
  · intro e he
    simpa only [gather, active, he, Function.comp_apply, Equiv.apply_symm_apply] using z.active e he
  · intro i hi ht
    obtain ⟨e, he, hp⟩ := z.onto _ hi ht
    exact ⟨e, he, by rw [he, hp, Equiv.symm_apply_apply]⟩
  · intro e he
    simpa only [gather, Rows.src, he, Function.comp_apply, Equiv.apply_symm_apply] using z.source e he
  · intro e he
    simpa only [gather, Rows.thick, he, Function.comp_apply, Equiv.apply_symm_apply] using z.thick e he
  · intro e f he hf
    simpa only [gather, dest, he, hf, Function.comp_apply, Equiv.apply_symm_apply] using z.dest e f he hf
  · intro e f he hf
    simpa only [gather, item, he, hf, Function.comp_apply, Equiv.apply_symm_apply] using z.item e f he hf

/-- The controls in original row order determine the entire matching. -/
structure Controls (m : Matching src dst ix) : Prop where
  mask : ∀ e, (m.plan (src e) (ix e)).isSome = (x (src e)).control.1 (pos e)
  mate : ∀ e, pos (m.mate e) = (x (src e.val)).control.2 (pos e.val)

theorem controlled_matching [Fintype E] [Fintype P] {c : Color r}
    (enc : ∀ p, (x p).Represents src dst ix c p pos (tag p))
    (b K : ℕ) (size : ∀ p t, (univ.filter fun e => src e = p ∧ ix e = t).card ≤ b)
    (deg : ∀ p, ((univ.filter fun e => src e = p).image dst).card ≤ K) :
    ∃ m : Matching src dst ix, m.color = c ∧ Controls x pos m ∧
      (∑ p, min (univ.filter fun e => src e = p ∧ ¬Packing.thick c (ix e)).card
        (univ.filter fun e => src e = p ∧ Packing.thick c (ix e)).card) ≤
        m.count + b * K * Fintype.card P := by
  let row p := (x p).gather (x p).perm
  let loc e := (x (src e)).perm.symm (pos e)
  have rep := gather_enc x pos enc
  obtain ⟨m, hc, hm⟩ := decode row loc rep
  refine ⟨m, hc, ⟨hm.mask, ?_⟩, decoded_count row loc rep (fun p => (x p).gather_sorted)
    b K size deg hm⟩
  intro e
  have he := hm.mate e
  unfold loc at he
  rw [(m.spec e).2.1] at he
  exact (x _).perm.symm_apply_eq.mp he

/-- Different colonies may share an array, with one source tag per colony.
Array positions and tags may depend on the affine coloring. -/
theorem controlled_subround [Fintype E] [Fintype P] (src dst : E → P) (ix : E → Cell r)
    (rows : Color r → P → Rows h k) (loc : Color r → E → B h) (key : Color r → P → B k)
    (enc : ∀ c p, (rows c p).Represents src dst ix c p (loc c) (key c p))
    (u L : ℝ) (K : ℕ) (hu : 0 < u) (hL : 0 ≤ L)
    (hs : ∀ p t, u * (univ.filter fun e => src e = p ∧ ix e = t).card ≤ L)
    (hd : ∀ p, ((univ.filter fun e => src e = p).image dst).card ≤ K) :
    ∃ m : Matching src dst ix, Controls (rows m.color) (loc m.color) m ∧
      u * Fintype.card E * (3 / 8) ≤ u * m.count + L * (K + 1) * Fintype.card P := by
  apply subround_of_matching src dst ix u L K hu hL hs
  intro c b hb
  obtain ⟨m, hm, hc, hn⟩ := controlled_matching (rows c) (loc c) (enc c) b K hb hd
  exact ⟨m, by rw [hm]; exact hc, hn⟩

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

section
/-!
# Reading a matching in either direction

The friend address is an involution even for an unused row. Looking
up the mask at that address therefore identifies all used thick units.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows

variable {h k : ℕ} (x : Rows h k)

private theorem equal_of_rankKey {i j : B h}
    (eq : x.rankKey i = x.rankKey j) (he : x.thick i = x.thick j) : i = j := by
  obtain ⟨ha, hs⟩ := Prod.mk.inj eq
  obtain ⟨hs, hr⟩ := Prod.mk.inj hs
  have ord i : (x.ordinal i).val = Control.rank x.key i := keys_rank (ColorKey k) x.key i
  exact Control.rank_injective x.key (Prod.ext (Prod.ext ha (Prod.ext he hs))
    ((ord i).symm.trans ((congrArg Fin.val hr).trans (ord j))))

private theorem friend_key (i : B h) : x.rankKey (x.friend i) = x.rankKey i :=
  (RankKey h k).serial.injective (other_spec ((RankKey h k).keys x.rankKey) i).1

private theorem friend_involutive : Function.Involutive x.friend := by
  intro i
  by_cases he : x.friend i = i
  · rw [he, he]
  let j := x.friend i
  have h₁ := x.friend_key i
  have h₂ := x.friend_key j
  have hn : x.friend j ≠ j :=
    (other_spec ((RankKey h k).keys x.rankKey) j).2 i
      (congrArg (RankKey h k).serial h₁.symm) (Ne.symm he)
  apply x.equal_of_rankKey (h₂.trans h₁)
  have hi : x.thick j ≠ x.thick i := mt (x.equal_of_rankKey h₁) he
  have hj : x.thick (x.friend j) ≠ x.thick j := mt (x.equal_of_rankKey h₂) hn
  cases ha : x.thick j <;> simp [ha] at hi hj <;> exact hj.trans hi.symm

theorem control_involutive : Function.Involutive x.control.2 := by
  intro i
  simp only [control, Function.comp_apply, Equiv.symm_apply_apply,
    friend_involutive (x.gather x.perm) _, Equiv.apply_symm_apply]

theorem control_source (i : B h) :
    x.active (x.control.2 i) = x.active i ∧ x.src (x.control.2 i) = x.src i := by
  let y := x.gather x.perm
  obtain ⟨ha, hs⟩ := Prod.mk.inj (y.friend_key (x.perm.symm i))
  have h := And.intro ha (Prod.mk.inj hs).1
  simpa only [control, y, gather, active, src, Function.comp_apply, Equiv.apply_symm_apply] using h

variable {E P : Type} {r : ℕ} {src dst : E → P} {ix : E → Packing.Cell r}
  {rows : P → Rows h k} {pos : E → B h} {m : Packing.Matching src dst ix}
  (ctl : Controls rows pos m)

include ctl

theorem Controls.back (i : {e // (m.plan (src e) (ix e)).isSome}) :
    (rows (src i.val)).control.2 (pos (m.mate i)) = pos i.val := by
  rw [ctl.mate]
  exact (rows _).control_involutive _

theorem Controls.used_iff {tag : P → B k}
    (enc : ∀ p, (rows p).Represents src dst ix m.color p pos (tag p)) (e : E) :
    (rows (src e)).control.1 ((rows (src e)).control.2 (pos e)) = true ↔
      ∃ i, m.mate i = e := by
  let x := rows (src e)
  constructor
  · intro h
    obtain ⟨ha, hs⟩ := x.control_source (pos e)
    obtain ⟨t, ht, hi⟩ := (enc _).onto _ (ha.trans ((enc _).active e rfl)) (hs.trans ((enc _).source e rfl))
    have hp : (m.plan (src t) (ix t)).isSome := by rw [ctl.mask, ht, hi]; exact h
    refine ⟨⟨t, hp⟩, (enc _).inj _ _ ((m.spec ⟨t, hp⟩).2.1.trans ht) rfl ?_⟩
    rw [ctl.mate]
    change (rows (src t)).control.2 (pos t) = _
    rw [ht, hi]
    exact x.control_involutive _
  · rintro ⟨i, rfl⟩
    rw [(m.spec i).2.1, ctl.back, ← ctl.mask]
    exact i.property

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end
