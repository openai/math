import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Union
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Sort
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting

/-!
# Connectivity of the ordinary information carried by moving stations

Selectors are indexed by their cell, and the fresh wire created by a
crossing is indexed by the current stack length. Carrying information
to the neighboring cell extends each footprint along a seam.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
open Relation
open scoped Classical
variable {V E : Type}

abbrev TraceSet (V : Type) := V → Finset (V ⊕ ℕ)

def available (n : ℕ) : V ⊕ ℕ → Prop
  | .inl _ => True
  | .inr j => j < n

def path (src dst : E → V) (u : TraceSet V) (j : V ⊕ ℕ) :=
  EqvGen (fun a b => j ∈ u a ∧ j ∈ u b ∧ ∃ e, src e = a ∧ dst e = b)

structure Tracks (src dst : E → V) (u : TraceSet V) (n : ℕ) : Prop where
  present : ∀ j, (∃ v, j ∈ u v) ↔ available n j
  connected : ∀ j v w, j ∈ u v → j ∈ u w → path src dst u j v w

def carry (u : TraceSet V) (n : ℕ) (s : Finset (V ⊕ ℕ)) (v w : V) : TraceSet V :=
  fun z => if z = v ∨ z = w then insert (.inr n) (u z ∪ s) else u z

variable {src dst : E → V} {u : TraceSet V} {n : ℕ} {s : Finset (V ⊕ ℕ)} {v w : V}

theorem carry_mono (z : V) : u z ⊆ carry u n s v w z := by
  unfold carry
  split_ifs
  · exact fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
  · exact Finset.Subset.refl _

theorem tracks_init : Tracks src dst (fun v => {Sum.inl v}) 0 := by
  constructor
  · rintro (v|j)
    · exact ⟨fun _ => trivial, fun _ => ⟨v, by simp⟩⟩
    · simp [available]
  · intro j v w hv hw
    have : v = w := Sum.inl_injective ((Finset.mem_singleton.mp hv).symm.trans
      (Finset.mem_singleton.mp hw))
    subst w
    exact .refl _

theorem Tracks.carry (h : Tracks src dst u n) (hs : s ⊆ u v) (e : E)
    (adj : (src e = v ∧ dst e = w) ∨ (src e = w ∧ dst e = v)) :
    Tracks src dst (carry u n s v w) (n + 1) := by
  let u' := Surface.carry u n s v w
  have entered (j : V ⊕ ℕ) (z : V) (hz : j ∈ u' z) :
      j ∈ u z ∨ (z = v ∨ z = w) ∧ (j = .inr n ∨ j ∈ s) := by
    unfold u' Surface.carry at hz
    split_ifs at hz with ht
    · simp only [Finset.mem_insert, Finset.mem_union] at hz
      tauto
    · exact Or.inl hz
  have both (j : V ⊕ ℕ) (hj : j = .inr n ∨ j ∈ s) : j ∈ u' v ∧ j ∈ u' w := by
    simp only [u', Surface.carry, true_or, or_true, ↓reduceIte, Finset.mem_insert, Finset.mem_union]
    tauto
  have along (j : V ⊕ ℕ) (hj : j = .inr n ∨ j ∈ s) (z : V) (hz : z = v ∨ z = w) :
      path src dst u' j z v := by
    rcases hz with rfl|rfl
    · exact .refl _
    · obtain ⟨hv, hw⟩ := both j hj
      rcases adj with f|f
      · exact .symm _ _ (.rel _ _ ⟨hv, hw, e, f⟩)
      · exact .rel _ _ ⟨hw, hv, e, f⟩
  have earlier (j : V ⊕ ℕ) (x y : V) (hx : j ∈ u x) (hy : j ∈ u y) :
      path src dst u' j x y :=
    EqvGen.mono (fun a b h => ⟨carry_mono _ h.1, carry_mono _ h.2.1, h.2.2⟩) _ _
      (h.connected j x y hx hy)
  have fresh (z : V) : Sum.inr n ∉ u z := fun hj =>
    Nat.lt_irrefl n ((h.present _).mp ⟨z, hj⟩)
  constructor
  · intro j
    have hc : available (n + 1) j ↔ available n j ∨ j = .inr n := by
      cases j <;> simp [available]; omega
    rw [hc, ← h.present]
    constructor
    · rintro ⟨z, hz⟩
      rcases entered j z hz with hh|⟨_, hh|hh⟩
      · exact .inl ⟨z, hh⟩
      · exact .inr hh
      · exact .inl ⟨v, hs hh⟩
    · rintro (⟨z, hz⟩|hj)
      · exact ⟨z, carry_mono z hz⟩
      · exact ⟨v, (both _ (.inl hj)).1⟩
  · intro j x y hx hy
    by_cases hj : j = .inr n ∨ j ∈ s
    · have toSource (z : V) (hz : j ∈ u' z) : path src dst u' j z v := by
        rcases entered j z hz with hh|⟨hh, _⟩
        · rcases hj with rfl|hj
          · exact (fresh z hh).elim
          · exact earlier _ _ _ hh (hs hj)
        · exact along _ hj _ hh
      exact .trans _ _ _ (toSource x hx) (.symm _ _ (toSource y hy))
    · exact earlier _ _ _ ((entered _ _ hx).resolve_right (fun h => hj h.2))
        ((entered _ _ hy).resolve_right (fun h => hj h.2))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Cells of a network and their nonempty oriented seams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

structure Grid (V E C : Type) where
  src : E → V
  dst : E → V
  cell : V → C
  stationRank : V → ℕ := fun _ => 0
  cellRank : C → ℕ := fun _ => 0
  packetRank : E → ℕ := fun _ => 0

namespace Grid
open Finset
open scoped Classical

variable {V E C : Type} (g : Grid V E C)

abbrev Seam := {p : C × C // p.1 ≠ p.2 ∧ ∃ e, g.cell (g.src e) = p.1 ∧ g.cell (g.dst e) = p.2}

def seamRank (v : g.Seam) := Nat.pair (g.cellRank v.val.1) (g.cellRank v.val.2)

def stations [Fintype V] (c : C) := univ.filter fun v => g.cell v = c

def ports [Fintype C] (c : C) := univ.filter fun s : g.Seam => s.val.1 = c ∨ s.val.2 = c

def uses [Fintype E] (v : V) := univ.filter fun e => g.src e = v ∨ g.dst e = v

def carries [Fintype E] (s : g.Seam) :=
  univ.filter fun e => g.cell (g.src e) = s.val.1 ∧ g.cell (g.dst e) = s.val.2

end Grid
end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-! # Counting port incidences in a grid of stations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
open Finset
open scoped Classical

variable {V E C : Type} [Fintype C] (g : Grid V E C)

/-- Each crossing wire along a port charges its unique endpoint in this cell. -/
theorem carries_le_uses [Fintype V] [Fintype E] (c : C) :
    ∑ s ∈ g.ports c, (g.carries s).card ≤ ∑ v ∈ g.stations c, (g.uses v).card := by
  rw [← card_sigma, ← card_sigma]
  let charge (p : Σ _ : g.Seam, E) : Σ _ : V, E :=
    ⟨if p.1.val.1 = c then g.src p.2 else g.dst p.2, p.2⟩
  apply card_le_card_of_injOn charge
  · rintro ⟨s, e⟩ he
    obtain ⟨hs, ha, hb⟩ : (s.val.1 = c ∨ s.val.2 = c) ∧
        g.cell (g.src e) = s.val.1 ∧ g.cell (g.dst e) = s.val.2 := by
      simpa only [mem_coe, mem_sigma, ports, carries, mem_filter_univ] using he
    by_cases hd : s.val.1 = c
    · simp [charge, hd, stations, uses, ha]
    · simp [charge, hd, stations, uses, hb, hs.resolve_left hd]
  · rintro ⟨s, e⟩ he ⟨t, a⟩ ha eq
    have ee : e = a := congrArg (fun p => p.2) eq
    subst a
    have hs := (mem_filter.mp (mem_sigma.mp he).2).2
    have ht := (mem_filter.mp (mem_sigma.mp ha).2).2
    have st : s = t := Subtype.ext (Prod.ext (hs.1.symm.trans ht.1) (hs.2.symm.trans ht.2))
    cases st
    rfl

/-- Each neighboring cell contributes at most two oriented ports. -/
theorem ports_bound (N : C → Finset C) (sym : ∀ c d, d ∈ N c → c ∈ N d)
    (adj : ∀ e, g.cell (g.src e) ≠ g.cell (g.dst e) → g.cell (g.dst e) ∈ N (g.cell (g.src e)))
    (c : C) : (g.ports c).card ≤ 2 * (N c).card := by
  calc
    _ ≤ (({c} ×ˢ N c) ∪ (N c ×ˢ {c})).card := by
      apply card_le_card_of_injOn Subtype.val _ Subtype.val_injective.injOn
      intro s hs
      obtain ⟨hne, e, ha, hb⟩ := s.property
      have hn : s.val.2 ∈ N s.val.1 := by rw [← ha, ← hb] at hne ⊢; exact adj e hne
      rcases (mem_filter.mp hs).2 with rfl | rfl
      · exact mem_union_left _ (mem_product.mpr ⟨mem_singleton_self _, hn⟩)
      · exact mem_union_right _ (mem_product.mpr ⟨sym _ _ hn, mem_singleton_self _⟩)
    _ ≤ _ := by simpa [Nat.two_mul] using card_union_le ({c} ×ˢ N c) (N c ×ˢ {c})

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

/-! # Numbering a finite set by a local key -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid

open Finset
open scoped Classical
variable {A B : Type}

/-- Use increasing key order where the keys distinguish the elements.
Unordered inputs still admit the same contraction proofs. -/
def number (f : A → ℕ) (s : Finset A) : Fin s.card ≃ ↥s :=
  if h : Function.Injective (fun v : s => f v.val) then
    letI := LinearOrder.lift' (fun v : s => f v.val) h
    (Fintype.orderIsoFinOfCardEq s (by simp)).toEquiv
  else Fintype.equivOfCardEq (by simp)

theorem number_lt {f : A → ℕ} {s : Finset A} (hf : Set.InjOn f s) (i j : Fin s.card) :
    f (number f s i).val < f (number f s j).val ↔ i < j := by
  have h : Function.Injective (fun v : s => f v.val) :=
    fun i j e => Subtype.ext (hf i.property j.property e)
  unfold number
  rw [dite_eq_left h]
  let _ := LinearOrder.lift' (fun v : s => f v.val) h
  exact (Fintype.orderIsoFinOfCardEq s (by simp)).lt_iff_lt

/-- Absolute element names disappear after numbering. The ordered
list of keys depends only on the unordered set of keys. -/
theorem number_keys {f : A → ℕ} {s : Finset A} (hf : Set.InjOn f s) :
    List.ofFn (fun i => f (number f s i).val) = (s.image f).sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun _ _ _ _ => le_antisymm)
  · rw [List.pairwise_ofFn]
    intro i j h
    exact ((number_lt hf i j).mpr h).le
  · exact pairwise_sort _ _
  · apply (List.perm_ext_iff_of_nodup ?_ (sort_nodup _ _)).mpr
    · intro k
      simp only [List.mem_ofFn, mem_sort, mem_image]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨_, (number f s i).property, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨(number f s).symm ⟨x, hx⟩, by simp⟩
    exact List.nodup_ofFn.mpr fun i j h => (number f s).injective
      (Subtype.ext (hf (number f s i).property (number f s j).property h))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

section
/-! # Transporting stationwise properties through a scene update -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Function
open scoped Classical
variable {F T V E X : Type} [Field F] {r t P : ℕ} {s : Stage F r t T V E X}

omit [Field F] in
theorem all_put {v : V} {c : s.Ct} {Q : V → s.St → Prop}
    (old : ∀ z, ∀ x ∈ (s.scene.cell z).stations, Q z x)
    (new : ∀ x ∈ c.stations, Q v x) :
    ∀ z, ∀ x ∈ ((s.put v c).scene.cell z).stations, Q z x := by
  intro z
  change ∀ x ∈ (update s.scene.cell v c z).stations, Q z x
  by_cases h : z = v
  · subst z; rw [update_self]; exact new
  · rw [update_of_ne h]; exact old z

theorem all_advance {u : s.St} {a : Passage P u} {v w : V} {j : E} {L R : s.Sock}
    {S : Lower F r} {i : a.Branch}
    (hv : s.scene.cell v = (L.plug j a.z).insert u) (hw : s.scene.cell w = R.plug j a.y)
    {Q : V → Station F r t (Tag V T) (Stack X t s.hidden × Level t u.b) → Prop}
    (old : ∀ z, ∀ x ∈ (s.scene.cell z).stations, Q z (x.pull Prod.fst id))
    (leave : Q v (a.leaves (Tag.leave s.hidden.length) i))
    (take : Q w (a.arrives (u.label.take s.hidden.length) S i)) :
    ∀ z, ∀ x ∈ ((s.advance a v w j L R S i).scene.cell z).stations, Q z x := by
  intro z
  change ∀ x ∈ (update (update (fun z => (s.scene.cell z).pull Prod.fst id) v
    (a.left L j (Tag.leave s.hidden.length) i)) w
    (a.right R j (u.label.take s.hidden.length) S i) z).stations, Q z x
  by_cases h : z = w
  · subst z
    rw [update_self]
    simp only [Passage.right, Cell.insert, Cell.pull, List.forall_mem_cons, List.forall_mem_map]
    exact ⟨take, fun x hx => old w x (by rwa [hw])⟩
  rw [update_of_ne h]
  by_cases h' : z = v
  · subst z
    rw [update_self]
    simp only [Passage.left, Cell.insert, Cell.pull, List.forall_mem_cons, List.forall_mem_map]
    exact ⟨leave, fun x hx => old v x (by rw [hv]; exact List.mem_cons_of_mem _ hx)⟩
  simp only [update_of_ne h', Cell.pull, List.forall_mem_map]
  exact old z

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-! # Information that a station may read -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset
open scoped Classical
variable {F T V E X : Type} {r t : ℕ}

def base : (ns : List ℕ) → Stack X t ns → X
  | [], x => x
  | _ :: ns, x => base ns x.1

/-- Agreement on one ordinary key. Natural-number keys are introduced
sequentially and their values are homogeneous states. -/
def Observe (keys : V → X → X → Prop) :
    (ns : List ℕ) → V ⊕ ℕ → Stack X t ns → Stack X t ns → Prop
  | [], .inl i, x, y => keys i x y
  | [], .inr _, _, _ => True
  | _ :: ns, j, x, y => Observe keys ns j x.1 y.1 ∧ (j = .inr ns.length → x.2 = y.2)

structure Reads (keys : V → X → X → Prop) (ext : T → X → X → Prop)
    (l : List ℕ) (seen : Finset (V ⊕ ℕ)) (a : Station F r t (Tag V T) (Stack X t l)) : Prop where
  named : a.label.name ≠ none → a.label.role = .collector
  within : a.label.reads ⊆ seen
  respects : ∀ x y, (∀ j ∈ a.label.reads, Observe keys l j x y) →
    (∀ i, a.label.name = some i → ext i (base l x) (base l y)) → a.table x = a.table y

def Controls (s : Stage F r t T V E X) (keys : V → X → X → Prop) (ext : T → X → X → Prop) : Prop :=
  ∀ v, ∀ a ∈ (s.scene.cell v).stations, Reads keys ext s.hidden (s.footprint v) a

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# Propagation of ordinary information

Merging takes the union of the reads. A crossing transfers those reads
and creates one independent key for the mover's former private state.
The near-side residue needs only that new key.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset
open scoped Classical
variable {F T V E X : Type} [Field F] {r t P g H U : ℕ}
  {s s' : Stage F r t T V E X} {keys : V → X → X → Prop} {ext : T → X → X → Prop}
  {l : List ℕ} {u v : Station F r t (Tag V T) (Stack X t l)} {seen : Finset (V ⊕ ℕ)}

omit [Field F] in
theorem Reads.unnamed (h : Reads keys ext l seen u) (h' : u.label.role ≠ .collector) :
    u.label.name = none := by
  by_contra hn
  exact h' (h.named hn)

omit [Field F] in
theorem Reads.join_name (h : Reads keys ext l seen u) (k : Reads keys ext l seen v)
    (hv : v.label.role ≠ .collector) : (u.label.join v.label).name = u.label.name := by
  unfold Tag.join
  split_ifs with hu
  · rfl
  · exact (k.unnamed hv).trans (h.unnamed hu).symm

theorem Reads.merge (h : Reads keys ext l seen u) (k : Reads keys ext l seen v)
    (hv : v.label.role ≠ .collector) (q : ℤ × ℤ) :
    Reads keys ext l seen (mergeAt u v (u.label.join v.label) q) := by
  have join := h.join_name k hv
  have union : (u.label.join v.label).reads = u.label.reads ∪ v.label.reads := by
    unfold Tag.join; split_ifs <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · change (u.label.join v.label).name ≠ none → (u.label.join v.label).role = .collector
    rw [join]
    intro hn
    simp [Tag.join, h.named hn]
  · change (u.label.join v.label).reads ⊆ seen
    rw [union]
    exact union_subset h.within k.within
  · intro x y hr he
    change ∀ j ∈ (u.label.join v.label).reads, _ at hr
    rw [union] at hr
    change ∀ i, (u.label.join v.label).name = some i → _ at he
    rw [join] at he
    have h₁ := h.respects x y (fun j hj => hr j (mem_union_left _ hj)) he
    have h₂ := k.respects x y (fun j hj => hr j (mem_union_right _ hj))
      (by simp [k.unnamed hv])
    unfold mergeAt Surface.merge
    simp only [jointWeight, h₁, h₂]

theorem Step.controls (h : Step P g H U s s') (hc : s.Controls keys ext) :
    s'.Controls keys ext := by
  cases h with
  | perm v ls hv => exact all_put hc (fun a ha => hc v a (hv.mem_iff.mpr ha))
  | expire v c u hv ha ready =>
    refine all_put (Q := fun z => Reads keys ext s.hidden (s.footprint z)) (c := c.insert {u with label := {u.label with role := .collector}}) hc ?_
    have h := hc v
    rw [hv] at h
    simp only [Cell.insert, List.forall_mem_cons] at h ⊢
    exact ⟨⟨fun _ => rfl, h.1.within, h.1.respects⟩, h.2⟩
  | merge v c a b n hv ha ready j q hq bound =>
    refine all_put (Q := fun z => Reads keys ext s.hidden (s.footprint z)) hc ?_
    have h := hc v
    rw [hv] at h
    simp only [Cell.insert, List.forall_mem_cons] at h ⊢
    exact ⟨h.1.merge h.2.1 (by simp [ha]) q, h.2.2⟩
  | cross v w j L R u a S i n hv hw ne he hh ha hn ready =>
    let f := carry s.footprint s.hidden.length u.label.reads v w
    have hu := hc v u (by simp [hv, Cell.insert])
    have hn' := hu.unnamed (by simp [ha])
    refine all_advance hv hw (Q := fun z => Reads keys ext (u.b :: s.hidden) (f z)) ?_ ?_ ?_
    · intro z b hb
      have h := hc z b hb
      refine ⟨h.named, h.within.trans (carry_mono z), ?_⟩
      intro x y hr he
      exact h.respects x.1 y.1 (fun j hj => (hr j hj).1) he
    · refine ⟨fun h => (h rfl).elim, ?_, ?_⟩
      · change {Sum.inr s.hidden.length} ⊆ f v
        simp [f, carry]
      · intro x y hr _
        have e := (hr (.inr s.hidden.length) (mem_singleton_self _)).2 rfl
        unfold Passage.leaves residue
        simp only [e]
    · refine ⟨fun h => (h hn').elim, ?_, ?_⟩
      · change insert (.inr s.hidden.length) u.label.reads ⊆ f w
        simp [f, carry]
      · intro x y hr he
        have e := (hr (.inr s.hidden.length) (mem_insert_self _ _)).2 rfl
        have e' := hu.respects x.1 y.1 (fun j hj => (hr j (mem_insert_of_mem hj)).1) he
        unfold Passage.arrives transfer
        simp only [e, e']

theorem Step.tracks {src dst : E → V} (h : Step P g H U s s')
    (hs : s.Layout src dst g) (hc : s.Controls keys ext)
    (hp : Tracks src dst s.footprint s.hidden.length) :
    Tracks src dst s'.footprint s'.hidden.length := by
  cases h with
  | perm => exact hp
  | expire => exact hp
  | merge => exact hp
  | cross v w j L R u a S i n hv hw ne he hh ha hn ready =>
    have hu := hc v u (by simp [hv, Cell.insert])
    apply hp.carry hu.within j
    have hl := (hs.incident v j).mp (by simp [ports, hv, Cell.insert, Socket.plug])
    have hr := (hs.incident w j).mp (by simp [ports, hw, Socket.plug])
    grind

theorem Reach.controls (h : s.Reach P g H U s') (hc : s.Controls keys ext) :
    s'.Controls keys ext := by
  induction h with
  | refl => exact hc
  | tail _ step ih => exact step.controls ih

theorem Reach.tracks {src dst : E → V} (h : s.Reach P g H U s') (hs : s.Layout src dst g)
    (hc : s.Controls keys ext) (hp : Tracks src dst s.footprint s.hidden.length) :
    Tracks src dst s'.footprint s'.hidden.length := by
  suffices s'.Layout src dst g ∧ Tracks src dst s'.footprint s'.hidden.length from this.2
  induction h with
  | refl => exact ⟨hs, hp⟩
  | tail h step ih => exact ⟨step.layout ih.1, step.tracks ih.1 (Reach.controls h hc) ih.2⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# Bounding the number of ordinary keys at a cell

A fresh private state becomes local to the departure cell. The only
non-collector allowed to carry keys from elsewhere is the current
mover. Its number of nonlocal keys grows linearly in its crossing
count, independently of the number of untouched auxiliary marks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset Function
open scoped Classical
variable {F T V E X : Type} {r t P g H U L : ℕ}
  {s s' : Stage F r t T V E X}

def visits (s : Stage F r t T V E X) (v : V) := ∑ e ∈ s.edges v, s.hits e

def loadLimit (U L : ℕ) := (U + 1) * (L + 2) + 1

private def Watch (L : ℕ) (home : Finset (V ⊕ ℕ)) (tag : Tag V T) :=
  tag.role ≠ .collector → (tag.reads \ home).card ≤ tag.role.clock * (L + 2)

def Load (s : Stage F r t T V E X) (U L : ℕ) : Prop :=
  ∃ home : TraceSet V,
    (∀ v, (home v).card ≤ s.visits v + 1) ∧
    (∀ v, (s.footprint v).card ≤ s.visits v * loadLimit U L + 1) ∧
    ∀ v, ∀ a ∈ (s.scene.cell v).stations, Watch L (home v) a.label

variable {home home' : Finset (V ⊕ ℕ)} {a b : Tag V T}

private theorem Watch.mono (h : Watch L home a) (hh : home ⊆ home') : Watch L home' a :=
  fun hn => (card_le_card (sdiff_subset_sdiff (Subset.refl _) hh)).trans (h hn)

private theorem Watch.merge (ha : Watch L home a) (hb : Watch L home b)
    (h : a.role.clock = 0) : Watch L home (a.join b) := by
  by_cases hn : a.role = .collector
  · simp [Watch, Tag.join, hn]
  have he : a.reads \ home = ∅ := card_eq_zero.mp (by simpa [h] using ha hn)
  have hs : (a.reads ∪ b.reads) \ home = b.reads \ home := by
    ext x
    have h := sdiff_eq_empty_iff_subset.mp he
    simp only [mem_sdiff, mem_union]
    grind
  simpa only [Watch, Tag.join, hn, ↓reduceIte, hs] using hb

private theorem Watch.size (h : Watch L home a) (hn : a.role ≠ .collector)
    (hh : home.card ≤ L + 1) : a.reads.card + 1 ≤ (a.role.clock + 1) * (L + 2) := by
  have he : a.reads ⊆ (a.reads \ home) ∪ home := by intro x hx; simp [hx]
  have := (card_le_card he).trans (card_union_le _ _)
  have := h hn
  rw [add_mul, one_mul]
  omega

theorem init_load {keys : V → X → X → Prop} {ext : T → X → X → Prop}
    (hc : s.Controls keys ext) (hi : ∀ v, s.footprint v = {Sum.inl v}) : s.Load U L := by
  refine ⟨s.footprint, fun v => ?_, fun v => ?_, fun v a ha _ => ?_⟩
  · simp [hi]
  · simp [hi]
  · simp [sdiff_eq_empty_iff_subset.mpr (hc v a ha).within]

variable [Field F]

theorem Step.load (h : Step P g H U s s') (hc : s.Load U L)
    (hvis : ∀ v, s.visits v ≤ L) : s'.Load U L := by
  obtain ⟨pool, hp, hseen, hw⟩ := hc
  have visits' (v) : s'.visits v = ∑ e ∈ s.edges v, s'.hits e := by rw [visits, h.edges_eq]
  cases h with
  | perm v ls hs =>
    refine ⟨pool, fun z => ?_, fun z => ?_, all_put hw (fun a ha => hw v a (hs.mem_iff.mpr ha))⟩
    · rw [visits']; exact hp z
    · rw [visits']; exact hseen z
  | expire v c u hv =>
    refine ⟨pool, fun z => ?_, fun z => ?_, ?_⟩
    · rw [visits']; exact hp z
    · rw [visits']; exact hseen z
    · refine all_put (Q := fun z a => Watch L (pool z) a.label)
        (c := c.insert {u with label := {u.label with role := .collector}}) hw ?_
      have h := hw v
      rw [hv] at h
      simp only [Cell.insert, List.forall_mem_cons] at h ⊢
      exact ⟨fun hn => (hn rfl).elim, h.2⟩
  | merge v c a b n hv ha ready j q hq bound =>
    refine ⟨pool, fun z => ?_, fun z => ?_, ?_⟩
    · rw [visits']; exact hp z
    · rw [visits']; exact hseen z
    · refine all_put (Q := fun z a => Watch L (pool z) a.label) hw ?_
      have h := hw v
      rw [hv] at h
      simp only [Cell.insert, List.forall_mem_cons] at h ⊢
      exact ⟨h.1.merge h.2.1 (ready.1 a (by simp)), h.2.2⟩
  | cross v w j A B u a S i n hv hw' ne he hh ha hn ready =>
    let s₁ := s.advance a v w j A B S i
    let next := update pool v (insert (.inr s.hidden.length) (pool v))
    have inc (z : V) : s₁.visits z = s.visits z + if j ∈ s.edges z then 1 else 0 := by
      rw [visits']
      have e (k) : s₁.hits k = s.hits k + if k = j then 1 else 0 := by
        by_cases h : k = j <;> simp [s₁, advance, h]
      change (∑ k ∈ s.edges z, s₁.hits k) = _
      simp only [e, sum_add_distrib, sum_ite_eq', visits]
    have near (z : V) (hz : z = v ∨ z = w) : s₁.visits z = s.visits z + 1 := by
      rw [inc, ite_eq_left]
      rcases hz with rfl|rfl
      · simp [edges, hv, Socket.plug, Cell.insert]
      · simp [edges, hw', Socket.plug]
    have mono (z : V) : s.visits z ≤ s₁.visits z := by rw [inc]; omega
    have hu := (hw v u (by simp [hv, Cell.insert])).size (by simp [ha])
      ((hp v).trans (Nat.add_le_add_right (hvis v) 1))
    have hu' : u.label.reads.card + 1 ≤ loadLimit U L := by
      rw [ha, Role.clock] at hu
      unfold loadLimit
      exact hu.trans ((Nat.mul_le_mul_right _ (Nat.succ_le_succ hn.le)).trans (Nat.le_succ _))
    change s₁.Load U L
    refine ⟨next, ?_, ?_, ?_⟩
    · intro z
      by_cases hz : z = v
      · subst z; dsimp only [next]; rw [update_self, near v (.inl rfl)]
        exact (card_insert_le _ _).trans (Nat.add_le_add_right (hp v) 1)
      · dsimp only [next]; rw [update_of_ne hz]
        exact (hp z).trans (Nat.add_le_add_right (mono z) 1)
    · intro z
      change (carry _ _ _ v w z).card ≤ _
      unfold carry
      split_ifs with hz
      · rw [near z hz, add_mul, one_mul]
        have h₀ := card_insert_le (Sum.inr s.hidden.length) (s.footprint z ∪ u.label.reads)
        have h₁ := card_union_le (s.footprint z) u.label.reads
        have h₂ := hseen z
        omega
      · exact (hseen z).trans (by gcongr; exact mono z)
    · refine all_advance hv hw' (Q := fun z x => Watch L (next z) x.label) ?_ ?_ ?_
      · intro z x hx
        refine (hw z x hx).mono ?_
        by_cases h : z = v <;> simp [next, h]
      · change Watch L (next v) (Tag.leave _)
        have he : {Sum.inr s.hidden.length} ⊆ next v := by simp [next]
        simp [Watch, Tag.leave, sdiff_eq_empty_iff_subset.mpr he]
      · intro _
        change ((insert (Sum.inr s.hidden.length) u.label.reads) \ next w).card ≤ _
        exact ((card_le_card sdiff_subset).trans (card_insert_le _ _)).trans hu

theorem Reach.footprint_bound (h : s.Reach P g H U s') (hc : s.Load U L)
    (hvis : ∀ a, s.Reach P g H U a → ∀ v, a.visits v ≤ L) (v : V) :
    (s'.footprint v).card ≤ L * loadLimit U L + 1 := by
  have hs : s'.Load U L := by
    induction h with
    | refl => exact hc
    | tail h step ih => exact step.load ih (hvis _ h)
  exact (hs.choose_spec.2.1 v).trans (by gcongr; exact hvis _ h _)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# Station names stay in their original cells

Only collectors carry names. Moving a station can therefore neither
displace a name nor duplicate one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Function
open scoped Classical

variable {F T V E X Y : Type} {r t P g H U : ℕ}

private def labels (c : Cell F r t (Tag V T) E X) :=
  c.stations.filterMap (fun a => a.label.name)

private theorem labels_insert (c : Cell F r t (Tag V T) E X) (a : Station F r t (Tag V T) X) :
    labels (c.insert a) = a.label.name.toList ++ labels c := by
  unfold labels Cell.insert
  simp only [List.filterMap_cons]
  cases a.label.name <;> rfl

private theorem labels_pull (c : Cell F r t (Tag V T) E X) (π : Y → X) :
    labels (c.pull π id) = labels c := by
  simp only [labels, Cell.pull, List.filterMap_map]
  rfl

def names (s : Stage F r t T V E X) (v : V) := labels (s.scene.cell v)

theorem mem_names (s : Stage F r t T V E X) (v : V) (i : T) :
    i ∈ s.names v ↔ ∃ a ∈ (s.scene.cell v).stations, a.label.name = some i :=
  List.mem_filterMap

variable {s s' : Stage F r t T V E X} {keys : V → X → X → Prop} {ext : T → X → X → Prop}

private theorem names_put {v : V} {c : s.Ct} (z : V)
    (h : (labels c).Perm (s.names v)) : ((s.put v c).names z).Perm (s.names z) := by
  change (labels (update s.scene.cell v c z)).Perm _
  by_cases e : z = v
  · subst z; rwa [update_self]
  · rw [update_of_ne e]; exact .refl _

variable [Field F]

theorem Step.names (h : s.Step P g H U s') (hc : s.Controls keys ext) (z : V) :
    (s'.names z).Perm (s.names z) := by
  cases h with
  | perm v ls hl =>
    apply names_put
    exact hl.symm.filterMap _
  | expire v c u hv ha ready =>
    change ((s.put v _).names z).Perm _
    apply names_put
    rw [Stage.names, hv, labels_insert, labels_insert]
  | merge v c a b n hv ha ready j q hq bound =>
    have h := hc v
    rw [hv] at h
    simp only [Cell.insert, List.forall_mem_cons] at h
    have hn := h.2.1.unnamed (by simp [ha])
    have hj := h.1.join_name h.2.1 (by simp [ha])
    apply names_put
    rw [Stage.names, hv, labels_insert, labels_insert, labels_insert]
    change ((a.label.join b.label).name.toList ++ _).Perm _
    rw [hj, hn]
    rfl
  | cross v w j L R u a S i n hv hw ne he hh ha hn ready =>
    have hu := hc v u (by simp [hv, Cell.insert])
    have hn := hu.unnamed (by simp [ha])
    change (labels (update (update (fun z => (s.scene.cell z).pull Prod.fst id) v
      (a.left L j (Tag.leave s.hidden.length) i)) w
      (a.right R j (u.label.take s.hidden.length) S i) z)).Perm (labels (s.scene.cell z))
    by_cases h : z = w
    · subst z
      rw [update_self, hw, Passage.right, labels_insert, labels_pull]
      change (u.label.name.toList ++ _).Perm _
      rw [hn]
      rfl
    rw [update_of_ne h]
    by_cases h' : z = v
    · subst z
      rw [update_self, hv, Passage.left, labels_insert, labels_insert, labels_pull, hn]
      rfl
    · rw [update_of_ne h', labels_pull]

theorem Reach.names (h : s.Reach P g H U s') (hc : s.Controls keys ext) (z : V) :
    (s'.names z).Perm (s.names z) := by
  induction h with
  | refl => exact .refl _
  | tail h step ih => exact (step.names (Reach.controls h hc) z).trans ih

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end
