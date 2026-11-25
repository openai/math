import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix
import OAI.LinearAlgebra.MatrixExponent.Packing.Budget
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort

section
/-! # Matching by source and occurrence rank -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring
open Finset
open scoped Classical

abbrev RowFmt (h k : ℕ) := Format.pair (.vec h .bit) (.pair (.vec h .bit)
  (.pair (.vec h (.addr k)) (.pair (.vec h (.addr k)) (.vec h (.addr k)))))

abbrev Rows (h k : ℕ) :=
  (B h → Bool) × (B h → Bool) × (B h → B k) × (B h → B k) × (B h → B k)

namespace Rows
variable {h k : ℕ} (x : Rows h k)

abbrev active := x.1
abbrev thick := x.2.1
abbrev src := x.2.2.1
abbrev item := x.2.2.2.1
abbrev dest := x.2.2.2.2

def isThin (i : B h) : Prop := x.active i = true ∧ x.thick i = false
def isThick (i : B h) : Prop := x.active i = true ∧ x.thick i = true

def key (i : B h) := (x.active i, x.thick i, x.src i)

/-- Only contiguity of the relevant runs matters, not the order of the runs. -/
structure sorted : Prop where
  source : ∀ i j k, i ≤ j → j ≤ k →
    x.isThin i → x.isThin k → x.src i = x.src k → x.isThin j ∧ x.src j = x.src i
  item : ∀ i j k, i ≤ j → j ≤ k →
    x.isThin i → x.isThin k → x.src i = x.src k → x.item i = x.item k → x.item j = x.item i
  bin : ∀ i j k, i ≤ j → j ≤ k →
    x.isThick i → x.isThick k → x.src i = x.src k → x.dest i = x.dest k → x.dest j = x.dest i

def friends (friend : B h → B h) : Prop :=
  ∀ i, x.isThin i →
    (∀ j, x.isThick j → x.src j = x.src i → Control.rank x.key j = Control.rank x.key i →
      friend i = j) ∧
    (friend i ≠ i → x.isThick (friend i) ∧ x.src (friend i) = x.src i ∧
      Control.rank x.key (friend i) = Control.rank x.key i)

def passes (friend : B h → B h) (i : B h) : Prop :=
  x.isThin i ∧ friend i ≠ i ∧
    ∀ j, x.isThin j → x.src j = x.src i → x.item j = x.item i →
      friend j ≠ j ∧ x.dest (friend j) = x.dest (friend i)

variable {friend : B h → B h}

theorem eligible_iff (hf : x.friends friend) {i : B h} (hi : x.isThin i) :
    friend i ≠ i ↔ Control.rank x.key i < Control.histogram x.key (true, true, x.src i) none := by
  rw [← Control.rank_range]
  constructor
  · intro he
    obtain ⟨ht, hs, hr⟩ := (hf i hi).2 he
    exact ⟨friend i, Prod.ext ht.1 (Prod.ext ht.2 hs), hr⟩
  · rintro ⟨j, he, hr⟩
    obtain ⟨ha, ht, hs⟩ := by simpa only [key, Prod.mk.injEq] using he
    rw [(hf i hi).1 j ⟨ha, ht⟩ hs hr]
    intro e
    rw [e, hi.2] at ht
    cases ht

theorem friend_injective (hf : x.friends friend) : Set.InjOn friend {i | x.passes friend i} := by
  intro i hi j hj he
  obtain ⟨_, si, ri⟩ := (hf i hi.1).2 hi.2.1
  obtain ⟨_, sj, rj⟩ := (hf j hj.1).2 hj.2.1
  rw [he] at si ri
  apply Control.rank_injective x.key
  exact Prod.ext (Prod.ext (hi.1.1.trans hj.1.1.symm)
    (Prod.ext (hi.1.2.trans hj.1.2.symm) (si.symm.trans sj))) (ri.symm.trans rj)

def small (b : ℕ) : Prop :=
  ∀ s t, (univ.filter fun i => x.isThin i ∧ x.src i = s ∧ x.item i = t).card ≤ b

/-- A fixed window suffices to check all occurrences of the thin item. -/
theorem item_span (hs : x.sorted) {b : ℕ} (hb : x.small b) {i j : B h}
    (hi : x.isThin i) (hj : x.isThin j) (he : x.src i = x.src j) (ht : x.item i = x.item j) :
    j.val < i.val + b := by
  by_cases hle : i ≤ j
  · have bound : (Icc i j).card ≤ b := by
      refine le_trans (card_le_card ?_) (hb (x.src i) (x.item i))
      intro p hp
      obtain ⟨h₁, h₂⟩ := mem_Icc.mp hp
      obtain ⟨htp, hep⟩ := hs.source _ _ _ h₁ h₂ hi hj he
      exact mem_filter.mpr ⟨mem_univ _, htp, hep, hs.item _ _ _ h₁ h₂ hi hj he ht⟩
    rw [Fin.card_Icc] at bound
    omega
  · exact (Nat.lt_of_not_ge hle).trans_le (Nat.le_add_right _ _)

end Rows
end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-! # Counting eligible rows by source -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
open Finset Control
open scoped Classical

variable {h k : ℕ} (x : Rows h k) {friend : B h → B h}

/-- Within each source the eligible thin rows are in bijection with
the ranks attained by both thin and thick rows. -/
theorem eligible_count (hf : x.friends friend) (s : B k) :
    min (univ.filter (fun i => x.isThin i ∧ x.src i = s)).card
      (univ.filter (fun i => x.isThick i ∧ x.src i = s)).card =
      (univ.filter (fun i => (x.isThin i ∧ friend i ≠ i) ∧ x.src i = s)).card := by
  let S := univ.filter fun i => (x.isThin i ∧ friend i ≠ i) ∧ x.src i = s
  let n (t : Bool) := histogram x.key (true, t, s) none
  have hm (i : B h) : i ∈ S ↔ x.key i = (true, false, s) ∧ rank x.key i < n true := by
    simp only [S, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hi, he⟩, hs⟩
      exact ⟨Prod.ext hi.1 (Prod.ext hi.2 hs), by simpa [n, hs] using (x.eligible_iff hf hi).mp he⟩
    · rintro ⟨hk, hr⟩
      obtain ⟨ha, ht, hs⟩ := by simpa only [key, Prod.mk.injEq] using hk
      exact ⟨⟨⟨ha, ht⟩, (x.eligible_iff hf ⟨ha, ht⟩).mpr (by simpa [hs, n] using hr)⟩, hs⟩
  have hi : Set.InjOn (rank x.key) ↑S := by
    intro i hi j hj e
    exact rank_injective x.key (Prod.ext (((hm i).mp hi).1.trans ((hm j).mp hj).1.symm) e)
  have he : S.image (rank x.key) = range (min (n false) (n true)) := by
    ext r
    simp only [mem_image, hm, mem_range, lt_min_iff]
    constructor
    · rintro ⟨i, ⟨hk, hb⟩, rfl⟩
      exact ⟨(rank_range _ _ _).mp ⟨i, hk, rfl⟩, hb⟩
    · rintro ⟨ha, hb⟩
      obtain ⟨i, hk, rfl⟩ := (rank_range _ _ _).mpr ha
      exact ⟨i, ⟨hk, hb⟩, rfl⟩
  change _ = S.card
  rw [← card_image_of_injOn hi, he, card_range]
  simp only [n, histogram_none, key, Prod.mk.injEq, isThin, isThick, and_assoc]

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

section
/-! # A local array encoding the outgoing units of a single source tag -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
open Packing

variable {E P : Type} {r h k : ℕ}

/-- Tags need only distinguish items and destinations within the colony.
Other source tags may use the same array. -/
structure Represents (x : Rows h k) (src dst : E → P) (ix : E → Cell r)
    (c : Color r) (p : P) (pos : E → B h) (tag : B k) : Prop where
  inj : ∀ e f, src e = p → src f = p → pos e = pos f → e = f
  active : ∀ e, src e = p → x.active (pos e) = true
  onto : ∀ i, x.active i = true → x.src i = tag → ∃ e, src e = p ∧ pos e = i
  source : ∀ e, src e = p → x.src (pos e) = tag
  thick : ∀ e, src e = p → (x.thick (pos e) = true ↔ Packing.thick c (ix e))
  dest : ∀ e f, src e = p → src f = p → (x.dest (pos e) = x.dest (pos f) ↔ dst e = dst f)
  item : ∀ e f, src e = p → src f = p → (x.item (pos e) = x.item (pos f) ↔ ix e = ix f)

namespace Represents
variable {x : Rows h k} {src dst : E → P} {ix : E → Cell r} {c : Color r}
  {p : P} {pos : E → B h} {tag : B k} (z : x.Represents src dst ix c p pos tag)

include z

theorem isThin (e : E) (he : src e = p) : x.isThin (pos e) ↔ ¬Packing.thick c (ix e) := by
  simp only [Rows.isThin, z.active e he, true_and, ← z.thick e he]
  cases x.thick (pos e) <;> decide

theorem isThick (e : E) (he : src e = p) : x.isThick (pos e) ↔ Packing.thick c (ix e) := by
  simp only [Rows.isThick, z.active e he, true_and, z.thick e he]

end Represents
end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

/-! # Whole-item matching by an ordered list of friends -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
open Finset
open scoped Classical

variable {h k : ℕ} (x : Rows h k) {friend : B h → B h}

/-- Within each thin source run, the eligible positions form a prefix,
and their friends occur in order in the thick source run. -/
private theorem earlier (hf : x.friends friend) {i j : B h} (hij : i ≤ j)
    (hi : x.isThin i) (hj : x.isThin j) (he : x.src i = x.src j) (hne : friend j ≠ j) :
    friend i ≠ i ∧ friend i ≤ friend j := by
  rcases hij.eq_or_lt with rfl | hlt
  · exact ⟨hne, le_rfl⟩
  have hk : x.key i = x.key j := Prod.ext (hi.1.trans hj.1.symm) (Prod.ext (hi.2.trans hj.2.symm) he)
  have hr := Control.rank_mono x.key hk hlt
  have hni : friend i ≠ i := by
    rw [x.eligible_iff hf hi, he]
    exact hr.trans ((x.eligible_iff hf hj).mp hne)
  refine ⟨hni, le_of_not_gt ?_⟩
  intro hji
  obtain ⟨ti, si, ri⟩ := (hf i hi).2 hni
  obtain ⟨tj, sj, rj⟩ := (hf j hj).2 hne
  have hfkey : x.key (friend i) = x.key (friend j) :=
    Prod.ext (ti.1.trans tj.1.symm) (Prod.ext (ti.2.trans tj.2.symm) (si.trans (he.trans sj.symm)))
  exact (Control.rank_mono x.key hfkey.symm hji).not_ge (ri.trans_le (hr.le.trans_eq rj.symm))

private abbrev Thin (s : B k) := {i // x.isThin i ∧ x.src i = s}

variable {s : B k}

private def block (i : x.Thin s) := (x.src i.val, x.item i.val)

private def bucket (friend : B h → B h) (i : x.Thin s) :=
  if friend i.val ≠ i.val then some (x.src i.val, x.dest (friend i.val)) else none

private theorem bucket_some (i : x.Thin s) : (x.bucket friend i).isSome ↔ friend i.val ≠ i.val := by
  by_cases he : friend i.val = i.val <;> simp [bucket, he]

private theorem bucket_interval (hs : x.sorted) (hf : x.friends friend)
    (i j k : x.Thin s) (hij : i ≤ j) (hjk : j ≤ k)
    (he : x.bucket friend i = x.bucket friend k) (hi : (x.bucket friend i).isSome) :
    x.bucket friend j = x.bucket friend i := by
  have ni := (x.bucket_some i).mp hi
  have nk := (x.bucket_some k).mp (he ▸ hi)
  simp only [bucket, ite_eq_left ni, ite_eq_left nk, Option.some.injEq, Prod.mk.injEq] at he
  have sj := (hs.source _ _ _ hij hjk i.property.1 k.property.1 he.1).2
  obtain ⟨nj, fjk⟩ := x.earlier hf hjk j.property.1 k.property.1 (sj.trans he.1) nk
  have fij := (x.earlier hf hij i.property.1 j.property.1 sj.symm nj).2
  obtain ⟨ti, si, _⟩ := (hf _ i.property.1).2 ni
  obtain ⟨tk, sk, _⟩ := (hf _ k.property.1).2 nk
  have d := hs.bin _ _ _ fij fjk ti tk (si.trans (he.1.trans sk.symm)) he.2
  simp only [bucket, ite_eq_left ni, ite_eq_left nj, sj, d]

private theorem pass_of_plan (i : x.Thin s) (hp : (Packing.plan x.block (x.bucket friend) i).isSome) :
    x.passes friend i.val := by
  unfold Packing.plan at hp
  split_ifs at hp with hg
  · have hi := (x.bucket_some i).mp hp
    refine ⟨i.property.1, hi, ?_⟩
    intro j hj hs ht
    have e := hg ⟨j, hj, hs.trans i.property.2⟩ (Prod.ext hs ht)
    have hn := (x.bucket_some ⟨j, hj, hs.trans i.property.2⟩).mp (e.symm ▸ hp)
    simp only [bucket, ite_eq_left hi, ite_eq_left hn, Option.some.injEq, Prod.mk.injEq] at e
    exact ⟨hn, e.2⟩
  · cases hp

theorem matching_count (hs : x.sorted) (hf : x.friends friend) (s : B k) {b : ℕ}
    (hb : ∀ t, (univ.filter fun i => x.isThin i ∧ x.src i = s ∧ x.item i = t).card ≤ b) :
    min (univ.filter fun i => x.isThin i ∧ x.src i = s).card
      (univ.filter fun i => x.isThick i ∧ x.src i = s).card ≤
      (univ.filter fun i => x.passes friend i ∧ x.src i = s).card +
        b * ((univ.filter fun i => x.isThick i ∧ x.src i = s).image
          fun i => (x.src i, x.dest i)).card := by
  let bins := (univ.filter fun i => x.isThick i ∧ x.src i = s).image fun i => (x.src i, x.dest i)
  let eligible := univ.filter fun i : x.Thin s => (x.bucket friend i).isSome
  have block_interval (i j k : x.Thin s) (hij : i ≤ j) (hjk : j ≤ k)
      (he : x.block i = x.block k) : x.block j = x.block i :=
    Prod.ext (hs.source _ _ _ hij hjk i.property.1 k.property.1 (congrArg Prod.fst he)).2
      (hs.item _ _ _ hij hjk i.property.1 k.property.1 (congrArg Prod.fst he) (congrArg Prod.snd he))
  have pre (i j : x.Thin s) (hij : i ≤ j) (he : x.block i = x.block j)
      (hj : (x.bucket friend j).isSome) : (x.bucket friend i).isSome :=
    (x.bucket_some i).mpr (x.earlier hf hij i.property.1 j.property.1
      (congrArg Prod.fst he) ((x.bucket_some j).mp hj)).1
  have size (p : B k × B k) : (univ.filter fun i : x.Thin s => x.block i = p).card ≤ b := by
    apply le_trans _ (hb p.2)
    apply card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
    intro i hi
    have he := (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _, i.property.1, i.property.2, congrArg Prod.snd he⟩
  have H := Packing.straddles x.block (x.bucket friend) block_interval (x.bucket_interval hs hf)
    pre b size
  have elig : eligible.card = (univ.filter fun i => (x.isThin i ∧ friend i ≠ i) ∧ x.src i = s).card := by
    apply card_bij (fun i _ => i.val)
    · intro i hi
      exact mem_filter.mpr ⟨mem_univ _, ⟨i.property.1, (x.bucket_some i).mp (mem_filter.mp hi).2⟩, i.property.2⟩
    · exact fun _ _ _ _ he => Subtype.ext he
    · intro i hi
      obtain ⟨_, ⟨ht, hn⟩, hh⟩ := mem_filter.mp hi
      exact ⟨⟨i, ht, hh⟩, mem_filter.mpr ⟨mem_univ _, (x.bucket_some _).mpr hn⟩, rfl⟩
  have passed : (univ.filter fun i : x.Thin s => (Packing.plan x.block (x.bucket friend) i).isSome).card ≤
      (univ.filter fun i => x.passes friend i ∧ x.src i = s).card := by
    apply card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
    exact fun i hi => mem_filter.mpr ⟨mem_univ _, x.pass_of_plan i (mem_filter.mp hi).2, i.property.2⟩
  have used : (eligible.image (x.bucket friend)).card ≤ bins.card := by
    apply le_trans _ (card_image_le (s := bins) (f := some))
    apply card_le_card
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    have hn := (x.bucket_some i).mp (mem_filter.mp hi).2
    obtain ⟨ht, he, _⟩ := (hf _ i.property.1).2 hn
    rw [bucket, ite_eq_left hn, ← he]
    exact mem_image_of_mem _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, ht, he.trans i.property.2⟩))
  rw [x.eligible_count hf s, ← elig]
  exact H.trans (Nat.add_le_add passed (Nat.mul_le_mul_left b used))

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows
end

section
/-! # Transferring the array matching bound to one source colony -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring.Rows.Represents
open Finset Packing
open scoped Classical

variable {E P : Type} [Fintype E] {r h k : ℕ} {src dst : E → P}
  {ix : E → Cell r} {c : Color r} {p : P} {pos : E → B h} {x : Rows h k}
  {tag : B k} (z : x.Represents src dst ix c p pos tag)

include z

private theorem count (q : B h → Prop) (t : E → Prop) [DecidablePred q] [DecidablePred t]
    (active : ∀ i, q i → x.active i = true ∧ x.src i = tag)
    (spec : ∀ e, src e = p → (q (pos e) ↔ t e)) :
    (univ.filter q).card = (univ.filter fun e => src e = p ∧ t e).card := by
  symm
  apply card_bij (fun e _ => pos e)
  · intro e he
    obtain ⟨_, hs, ht⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, (spec e hs).mpr ht⟩
  · exact fun e he f hf eq => z.inj _ _ (mem_filter.mp he).2.1 (mem_filter.mp hf).2.1 eq
  · intro i hi
    obtain ⟨e, he, rfl⟩ := z.onto _ (active _ (mem_filter.mp hi).2).1
      (active _ (mem_filter.mp hi).2).2
    exact ⟨e, mem_filter.mpr ⟨mem_univ _, he, (spec e he).mp (mem_filter.mp hi).2⟩, rfl⟩

theorem small (b : ℕ)
    (hsize : ∀ t, (univ.filter fun e => src e = p ∧ ix e = t).card ≤ b) :
    ∀ t, (univ.filter fun i => x.isThin i ∧ x.src i = tag ∧ x.item i = t).card ≤ b := by
  intro t
  let q := fun i => x.isThin i ∧ x.src i = tag ∧ x.item i = t
  change (univ.filter q).card ≤ b
  rw [z.count q (q ∘ pos) (fun _ hi => ⟨hi.1.1, hi.2.1⟩) (fun _ _ => Iff.rfl)]
  by_cases he : ∃ e, src e = p ∧ q (pos e)
  · obtain ⟨e, he, hq⟩ := he
    refine le_trans (card_le_card ?_) (hsize (ix e))
    intro f hf
    obtain ⟨_, hf, hq'⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_univ _, hf, (z.item _ _ hf he).mp (hq'.2.2.trans hq.2.2.symm)⟩
  · simp only [not_exists] at he
    simp [he]

private theorem bins :
    ((univ.filter fun i => x.isThick i ∧ x.src i = tag).image fun i => (x.src i, x.dest i)).card ≤
      ((univ.filter fun e => src e = p).image dst).card := by
  let A := (univ.filter fun i => x.isThick i ∧ x.src i = tag).image fun i => (x.src i, x.dest i)
  let D := (univ.filter fun e => src e = p).image dst
  have repr (a : A) : ∃ e, src e = p ∧ (tag, x.dest (pos e)) = a.val := by
    obtain ⟨i, hi, heq⟩ := mem_image.mp a.property
    obtain ⟨e, he, rfl⟩ := z.onto _ (mem_filter.mp hi).2.1.1 (mem_filter.mp hi).2.2
    exact ⟨e, he, by simpa only [z.source e he] using heq⟩
  choose e he hval using repr
  let f (a : A) : D := ⟨dst (e a), mem_image_of_mem dst (mem_filter.mpr ⟨mem_univ _, he a⟩)⟩
  have hinj : Function.Injective f := by
    intro a b eq
    apply Subtype.ext
    rw [← hval a, ← hval b, (z.dest _ _ (he a) (he b)).mpr (congrArg Subtype.val eq)]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem local_count {fr : B h → B h} (hs : x.sorted) (hf : x.friends fr) (b K : ℕ)
    (hsize : ∀ t, (univ.filter fun e => src e = p ∧ ix e = t).card ≤ b)
    (hd : ((univ.filter fun e => src e = p).image dst).card ≤ K) :
    min (univ.filter fun e => src e = p ∧ ¬Packing.thick c (ix e)).card
        (univ.filter fun e => src e = p ∧ Packing.thick c (ix e)).card ≤
      (univ.filter fun e => src e = p ∧ x.passes fr (pos e)).card + b * K := by
  have H := x.matching_count hs hf tag (z.small b hsize)
  have thin := z.count (fun i => x.isThin i ∧ x.src i = tag) (fun e => ¬Packing.thick c (ix e))
    (fun _ hi => ⟨hi.1.1, hi.2⟩) (fun e he => by simp only [z.source e he, and_true, z.isThin e he])
  have thick := z.count (fun i => x.isThick i ∧ x.src i = tag) (fun e => Packing.thick c (ix e))
    (fun _ hi => ⟨hi.1.1, hi.2⟩) (fun e he => by simp only [z.source e he, and_true, z.isThick e he])
  have passed := z.count (fun i => x.passes fr i ∧ x.src i = tag) (fun e => x.passes fr (pos e))
    (fun _ hi => ⟨hi.1.1.1, hi.2⟩) (fun e he => by simp [z.source e he])
  rw [thin, thick, passed] at H
  exact H.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (z.bins.trans hd)) _)

end OAI.LinearAlgebra.MatrixExponent.Coloring.Rows.Represents
end

section
/-!
# Occurrence ranks by stable sorting and pointer doubling

In sorted order, each position points to its predecessor with the same
key, or to itself at a boundary. After doubling `h` times all pointers
give the start of their run.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring
open Finset

variable {h k : ℕ}

def previous (i : B h) : B h := ⟨i.val - 1, by have := i.isLt; omega⟩

def back (f : B h → B k) (i : B h) := if f (previous i) = f i then previous i else i

def leader (f : B h → B k) : B h → B h := (fun g : B h → B h => g ∘ g)^[h] (back f)

theorem leader_eq (f : B h → B k) : leader f = (back f)^[2 ^ h] := by
  have go (n : ℕ) : (fun g : B h → B h => g ∘ g)^[n] (back f) = (back f)^[2 ^ n] := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_two, Function.iterate_add]
  exact go h

theorem leader_spec (f : B h → B k) (hf : Monotone f) (i : B h) :
    f (leader f i) = f i ∧ ∀ j, f j = f i → leader f i ≤ j := by
  let s := univ.filter fun j => f j = f i
  have hn : s.Nonempty := ⟨i, by simp [s]⟩
  let l := s.min' hn
  have he : f l = f i := (mem_filter.mp (min'_mem _ hn)).2
  have hl (j : B h) (hj : f j = f i) : l ≤ j := min'_le _ _ (by simpa [s])
  have range (j : B h) (lo : l ≤ j) (hi : j ≤ i) : f j = f i :=
    le_antisymm (hf hi) (he ▸ hf lo)
  have hb (j : B h) (lo : l ≤ j) (hi : j ≤ i) :
      (back f j).val = max l.val (j.val - 1) := by
    unfold back
    split_ifs with hj
    · have h := hl (previous j) (hj.trans (range j lo hi))
      exact (max_eq_right (show l.val ≤ j.val - 1 from h)).symm
    · have h : previous j < l := by
        by_contra! h
        exact hj ((range (previous j) h (le_trans (show previous j ≤ j from Nat.sub_le _ _) hi)).trans (range j lo hi).symm)
      have hl : l.val ≤ j.val := lo
      have ht : j.val - 1 < l.val := h
      omega
  have li := hl i rfl
  have go (n : ℕ) : ((back f)^[n] i).val = max l.val (i.val - n) := by
    induction n with
    | zero => simpa using (max_eq_right (show l.val ≤ i.val from li)).symm
    | succ n ih =>
      have h₁ : l.val ≤ ((back f)^[n] i).val := ih.symm ▸ le_max_left _ _
      have h₂ : ((back f)^[n] i).val ≤ i.val := ih.symm ▸ max_le li (Nat.sub_le _ _)
      rw [Function.iterate_succ_apply', hb _ h₁ h₂, ih]
      omega
  have eq : leader f i = l := by
    apply Fin.ext
    rw [leader_eq, go]
    have := i.isLt
    omega
  exact eq.symm ▸ ⟨he, hl⟩

theorem rank_sorted (f : B h → B k) (hf : Monotone f) (i : B h) :
    (i - leader f i).val = Control.rank f i := by
  obtain ⟨he, hl⟩ := leader_spec f hf i
  have hz : (univ.filter fun j => f j = f i ∧ j < i) = Ico (leader f i) i := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_Ico]
    exact ⟨fun h => ⟨hl j h.1, h.2⟩, fun h => ⟨le_antisymm (hf h.2.le) (he ▸ hf h.1), h.2⟩⟩
  rw [Control.rank, Control.histogram_some, hz, Fin.card_Ico]
  exact Fin.sub_val_of_le (hl _ rfl)

/-- Stably sort all keys. -/
abbrev order (f : B h → B k) := permutation f (fun _ => true)

theorem order_le (f : B h → B k) {i j : B h} (h : i ≤ j) :
    f (order f i) < f (order f j) ∨ (f (order f i) = f (order f j) ∧ order f i ≤ order f j) := by
  have e := Tuple.monotone_sort (fun i => toLex (false, toLex (f i, i))) h
  rcases Prod.Lex.toLex_le_toLex.mp e with he | ⟨_, he⟩
  · exact (lt_irrefl _ he).elim
  · exact Prod.Lex.toLex_le_toLex.mp he

theorem order_mono (f : B h → B k) : Monotone (f ∘ order f) :=
  fun _ _ h => (order_le f h).elim LT.lt.le (fun e => e.1.le)

theorem rank_order (f : B h → B k) (i : B h) :
    Control.rank (f ∘ order f) i = Control.rank f (order f i) := by
  simp only [Control.rank, Control.histogram_some]
  apply card_equiv (order f)
  intro j
  simp only [mem_filter, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨e, h⟩
    have hle := ((order_le f h.le).resolve_left (not_lt.mpr e.ge)).2
    exact ⟨e, hle.lt_of_ne ((order f).injective.ne h.ne)⟩
  · rintro ⟨e, h⟩
    refine ⟨e, lt_of_not_ge fun hj => ?_⟩
    exact h.not_ge ((order_le f hj).resolve_left (not_lt.mpr e.le)).2

def groupRank (f : B h → B k) : B h → B h :=
  (fun i => i - leader (f ∘ order f) i) ∘ (order f).symm

theorem groupRank_val (f : B h → B k) (i : B h) : (groupRank f i).val = Control.rank f i := by
  simp only [groupRank, Function.comp_apply, rank_sorted _ (order_mono f), rank_order,
    Equiv.apply_symm_apply]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end
