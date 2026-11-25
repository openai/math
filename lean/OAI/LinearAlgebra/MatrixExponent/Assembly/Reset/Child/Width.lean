import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation
import OAI.LinearAlgebra.MatrixExponent.Packing.HostReset

/-!
# Reset splits depend on one group and a bounded neighborhood

Each propagation increases the depth by a positive amount. It never
leaves the current group. An edge with a delay at least the remaining
height can be omitted even when other neighbors can cause splits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Packing Finset
open scoped Classical

variable {h a : ℕ} (ha : a ≤ h) (π : Equiv.Perm (Cell h)) (s : Cell a)

def InGroup (x : Cell h) : Prop := ancestor ha (π x) = s

theorem load_eq {l m : Cell h → ℝ} (hl : ∀ x, InGroup ha π s x → l x = m x)
    {i : ℕ} (hi : a ≤ i) {z : Cell i} (hz : ancestor hi z = s) :
    load l π i z = load m π i z := by
  unfold load
  split
  · refine sum_congr rfl fun x _ => ?_
    split
    · rename_i he
      exact hl x ((congrArg (ancestor hi) he).trans hz)
    · rfl
  · rfl

variable {V W : Type} {N : V → Finset V} {N' : W → Finset W}
  {d : V → V → ℕ} {d' : W → W → ℕ} {l : V → Cell h → ℝ} {l' : W → Cell h → ℝ}

abbrev High (l : V → Cell h → ℝ) (π : Equiv.Perm (Cell h)) (v : V) (i : ℕ) (z : Cell i) :=
  2 < load (l v) π i z

theorem high_lt (hl : ∀ v x, l v x ≤ 1) {v : V} {i : ℕ} {z : Cell i}
    (hq : High l π v i z) : i < h := by
  unfold High load at hq
  split at hq
  · rename_i hi
    exact heavy.lt (hl v) ⟨hi, lt_trans (by norm_num) hq⟩
  · norm_num at hq

/-- Matching local rows along walks of length strictly less than the
number of remaining bits suffices. -/
structure Forward (R : ℕ → V → W → Prop) (N : V → Finset V) (N' : W → Finset W)
    (d : V → V → ℕ) (d' : W → W → ℕ) (l : V → Cell h → ℝ) (l' : W → Cell h → ℝ) : Prop where
  item : ∀ v x, l v x ≤ 1
  values : ∀ k v w, R k v w → k < h - a → ∀ x, InGroup ha π s x → l v x = l' w x
  edges : ∀ k v w, R k v w → k < h - a → ∀ t ∈ N v, 2 * d v t < h - a →
    0 < d v t ∧ ∃ t' ∈ N' w, d v t = d' w t' ∧ R (k + 1) t t'

variable {π s ha} {R : ℕ → V → W → Prop}

private theorem move {v w : W} {i k : ℕ} (he : w ∈ N' v) (hk : k = d' v w)
    (j : Cell (i + 2 * k)) (hg : Spread N' d' (High l' π) w _ j) :
    Spread N' d' (High l' π) v i (ancestor (Nat.le_add_right ..) j) := by
  subst k
  exact .move he j hg

theorem Forward.spread (hf : Forward ha π s R N N' d d' l l') {v : V} {i : ℕ} {z : Cell i}
    (hm : Spread N d (High l π) v i z) :
    ∀ {k w}, R k v w → (hi : a + k ≤ i) → ancestor (by omega : a ≤ i) z = s →
      Spread N' d' (High l' π) w i z := by
  have bound : ∀ v i z, High l π v i z → i < h := fun _ _ _ => high_lt π hf.item
  induction hm with
  | @start v i z hm =>
    intro k w hr hi hz
    have ht := bound v i z hm
    exact .start (show 2 < load (l' w) π i z by
      rw [← load_eq ha π s (hf.values k v w hr (by omega)) (by omega) hz]
      exact hm)
  | @move v t i he z hm ih =>
    intro k w hr hi hz
    have ht := hm.depth bound
    obtain ⟨hd, u, hu, heq, hR⟩ := hf.edges k v w hr (by omega) t he (by omega)
    exact move hu heq z (ih hR (by omega) hz)

variable {v : V} {w : W} {base : V → ℕ} {base' : W → ℕ}

theorem split_eq {R' : ℕ → W → V → Prop}
    (hf : Forward ha π s R N N' (fun x y => 8 * d x y) (fun x y => 8 * d' x y) l l')
    (hg : Forward ha π s R' N' N (fun x y => 8 * d' x y) (fun x y => 8 * d x y) l' l)
    (hr : R 0 v w) (hr' : R' 0 w v) (hb : a ≤ base v) (he : base v = base' w)
    (x : Cell h) (hx : InGroup ha π s x) (i : ℕ) (hi : i ≤ h) :
    ResetSplit N d base l π v i (ancestor hi (π x)) ↔
      ResetSplit N' d' base' l' π w i (ancestor hi (π x)) := by
  unfold ResetSplit
  rw [← he]
  by_cases ht : i < base v
  · exact ⟨fun _ => .inl ht, fun _ => .inl ht⟩
  simp only [ht, false_or]
  exact ⟨fun hm => hf.spread hm hr (by omega) hx, fun hm => hg.spread hm hr' (by omega) hx⟩

theorem depth_eq {M M' : (i : ℕ) → Cell i → Prop} (x : Cell h)
    (he : ∀ i (hi : i ≤ h), M i (ancestor hi x) ↔ M' i (ancestor hi x)) :
    leafDepth M x = leafDepth M' x := by
  unfold leafDepth
  congr! 2 with i
  exact forall_congr' (fun hi => not_congr (he i hi.le))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# Comparing reset neighborhoods

At a host the only names needed for switch pins and reserved links
are the positions of its neighbors. The host itself also has a
position, whether or not it is a neighbor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Finset Packing
open scoped Classical

variable {V W A A' K : Type} {b d h Y : ℕ}

private def numbering (s : Finset K) (x : K) : ℕ :=
  if hx : x ∈ s then (Fintype.equivFin ↥s ⟨x, hx⟩).val else 0

def rank [Fintype A] (key : A ↪ K) (bound : Fintype.card A ≤ b) : A ↪ Fin b where
  toFun x := ⟨numbering (univ.map key) (key x), by
    rw [numbering, dite_eq_left (mem_map_of_mem key (mem_univ x))]
    exact (Fin.isLt _).trans_le (by simpa using bound)⟩
  inj' x y h := by
    have eq := congrArg Fin.val h
    dsimp only at eq
    rw [numbering, numbering, dite_eq_left (mem_map_of_mem key (mem_univ x)),
      dite_eq_left (mem_map_of_mem key (mem_univ y))] at eq
    exact key.injective (congrArg Subtype.val ((Fintype.equivFin _).injective (Fin.ext eq)))

theorem rank_eq [Fintype A] [Fintype A'] {key : A ↪ K} {key' : A' ↪ K}
    {bound : Fintype.card A ≤ b} {bound' : Fintype.card A' ≤ b} {x : A} {y : A'}
    (sur : ∀ a, ∃ a', key a = key' a') (inv : ∀ a', ∃ a, key' a' = key a)
    (he : key x = key' y) :
    rank key bound x = rank key' bound' y := by
  have hs : univ.map key = univ.map key' := by
    ext t
    simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨a', he⟩ := sur a
      exact ⟨a', he.symm⟩
    · rintro ⟨a', rfl⟩
      obtain ⟨a, he⟩ := inv a'
      exact ⟨a, he.symm⟩
  exact Fin.ext (congrArg₂ numbering hs he)

structure Chart (C : V → Finset V) (d : ℕ) where
  label : V → V → Option (Fin (2 ^ d))
  self : ∀ v, label v v = none
  inj : ∀ v, Set.InjOn (label v) (↑(insert v (C v)))

namespace Chart
variable {C : V → Finset V} {D : W → Finset W} (s : Chart C d) (t : Chart D d)

def Maps (v : V) (w : W) : Prop :=
  ∀ x ∈ C v, ∃ y ∈ D w, s.label v x = t.label w y

theorem same_root {v x : V} {w y : W} (hx : x ∈ insert v (C v)) (hy : y ∈ insert w (D w))
    (he : s.label v x = t.label w y) : x = v ↔ y = w := by
  constructor
  · intro h; apply t.inj w hy (mem_insert_self _ _); rw [← he, h, s.self, t.self]
  · intro h; apply s.inj v hx (mem_insert_self _ _); rw [he, h, s.self, t.self]

variable [Fintype V] [Fintype W] {Δ : ℕ}

theorem near_host {x y : Site V h} (he : y ∈ near C Δ x) : y.1 ∈ insert x.1 (C x.1) := by
  rcases (mem_near ..).mp he with rfl | he
  · exact mem_insert_self _ _
  · exact mem_insert_of_mem he.1

theorem Maps.near {v : V} {w : W} (hs : s.Maps t v w) (x : Schedule.Address h)
    (y : Site V h) (hy : y ∈ near C Δ (v, x)) :
    ∃ z, (z, y.2) ∈ near D Δ (w, x) ∧ s.label v y.1 = t.label w z := by
  rcases (mem_near ..).mp hy with rfl | ⟨hy, h⟩
  · exact ⟨w, near_self _ _ _, (s.self v).trans (t.self w).symm⟩
  obtain ⟨z, hz, he⟩ := hs _ hy
  exact ⟨z, (mem_near ..).mpr (.inr ⟨hz, h⟩), he⟩

def treeKey (x : Site V h × Fin Y) :
    ↥(terminalNear C Δ Y x) ↪ Option (Fin (2 ^ d)) × Schedule.Address h × Fin Y where
  toFun y := (s.label x.1.1 y.val.1.1, y.val.1.2, y.val.2)
  inj' a b h := by
    obtain ⟨hq, ht⟩ := Prod.mk.inj h
    have hu := s.inj _ (near_host (mem_product.mp a.property).1)
      (near_host (mem_product.mp b.property).1) hq
    exact Subtype.ext (Prod.ext (Prod.ext hu (Prod.mk.inj ht).1) (Prod.mk.inj ht).2)

def treePin (hΔ : 0 < Δ) (hc : ∀ v, (C v).card ≤ Δ) (x : Site V h × Fin Y) :
    ↥(terminalNear C Δ Y x) ↪ Fin (terminalWidth Δ Y) :=
  rank (s.treeKey x) (by simpa using terminal_card C Δ Y hΔ hc x)

private theorem treeKey_maps {v : V} {w : W} (hs : s.Maps t v w)
    (x : Schedule.Address h) (i : Fin Y) (q : ↥(terminalNear C Δ Y ((v, x), i))) :
    ∃ r : ↥(terminalNear D Δ Y ((w, x), i)), s.treeKey ((v, x), i) q = t.treeKey ((w, x), i) r := by
  obtain ⟨z, hz, he⟩ := Maps.near s t hs x _ (mem_product.mp q.property).1
  exact ⟨⟨((z, q.val.1.2), q.val.2), mem_product.mpr ⟨hz, mem_univ _⟩⟩, Prod.ext he rfl⟩

theorem treePin_eq {v : V} {w : W} (hs : s.Maps t v w) (ht : t.Maps s w v)
    (hΔ : 0 < Δ) (hc : ∀ v, (C v).card ≤ Δ) (hd : ∀ w, (D w).card ≤ Δ)
    (x : Schedule.Address h) (i : Fin Y) (q : ↥(terminalNear C Δ Y ((v, x), i)))
    (r : ↥(terminalNear D Δ Y ((w, x), i))) (he : s.treeKey ((v, x), i) q = t.treeKey ((w, x), i) r) :
    s.treePin hΔ hc _ q = t.treePin hΔ hd _ r :=
  rank_eq (s.treeKey_maps t hs x i) (t.treeKey_maps s ht x i) he

end Chart
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

section
/-! # Number of child host and neighbor address bits -/

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
open Packing
variable {F : Type} [Field F] {Y l : ℕ}

noncomputable def extra (P : Rotor F Y l) (Δ n : ℕ) := n + Nat.clog 2 (resetPositions P Δ)

noncomputable def width (D Y : ℕ) (full : Bool) := if full then Nat.clog 2 (4 + terminalWidth D Y) else 2

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Child
end

/-! # Common numbering of the output terminals for all reset groups -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Chart
open Packing Finset
open scoped Classical

variable {V W : Type} {C : V → Finset V} {D : W → Finset W} {h Y d : ℕ}

theorem partner_mem (sym : ∀ v w, w ∈ C v → v ∈ C w) (q : CoreContact C) (t : Bool) :
    unitEnds q (!t) ∈ C (unitEnds q t) := by
  cases t
  · exact q.property
  · exact sym _ _ q.property

theorem contact_ext (q r : CoreContact C) (t : Bool)
    (hq : unitEnds q t = unitEnds r t) (hr : unitEnds q (!t) = unitEnds r (!t)) : q = r := by
  cases t
  · exact Subtype.ext (Prod.ext hq hr)
  · exact Subtype.ext (Prod.ext hr hq)

abbrev Address := Σ i : ℕ, Cell i
abbrev PlugKey (d : ℕ) := Bool × Option (Fin (2 ^ d)) × Address × ℕ

def address {base : V → ℕ} (z : Link base (unitEnds (C := C))) : Address := ⟨_, z.2⟩

theorem address_inj {base : V → ℕ} {p q : Link base (unitEnds (C := C))}
    (he : p.1 = q.1) (hz : address p = address q) : p = q := Sigma.ext he (Sigma.mk.inj hz).2

variable (s : Chart C d) (sym : ∀ v w, w ∈ C v → v ∈ C w) {base : V → ℕ}
    (hb : ∀ v, base v ≤ h) (cap : CoreContact C → ℝ)

abbrev Ports (Y : ℕ) (x : Site V h) := Slots base unitEnds hb cap Y x

def plugKey (x : Site V h) : Ports hb cap Y x ↪ PlugKey d where
  toFun p := (p.1.val.2, s.label x.1 (unitEnds p.1.val.1.1 (!p.1.val.2)), address p.1.val.1, p.2.val)
  inj' := by
    rintro ⟨⟨⟨i, t⟩, hi⟩, a⟩ ⟨⟨⟨j, t'⟩, hj⟩, b⟩ he
    change (t, _, _, _) = (t', _, _, _) at he
    obtain ⟨rfl, he⟩ := Prod.mk.inj he
    obtain ⟨he, h⟩ := Prod.mk.inj he
    obtain ⟨h, h'⟩ := Prod.mk.inj h
    have hv : unitEnds i.1 t = x.1 := congrArg (fun z : Site V _ => z.1) hi
    have hw : unitEnds j.1 t = x.1 := congrArg (fun z : Site V _ => z.1) hj
    have hm : unitEnds i.1 (!t) = unitEnds j.1 (!t) := s.inj _
      (mem_insert_of_mem (hv ▸ partner_mem sym i.1 t)) (mem_insert_of_mem (hw ▸ partner_mem sym j.1 t)) he
    have := address_inj (contact_ext _ _ t (hv.trans hw.symm) hm) h
    subst j
    cases Fin.ext h'
    rfl

def plugs [Fintype V] (bound : ∀ x, Nonempty (Ports hb cap Y x ↪ Fin Y)) (x : Site V h) :
    Ports hb cap Y x ↪ Fin Y :=
  rank (s.plugKey sym hb cap x) (by simpa using Fintype.card_le_of_embedding (bound x).some)

variable (s' : Chart D d) (sym' : ∀ v w, w ∈ D v → v ∈ D w) {base' : W → ℕ}
    (hb' : ∀ v, base' v ≤ h) (cap' : CoreContact D → ℝ)

def Matches (base : V → ℕ) (base' : W → ℕ) (q : CoreContact C) (r : CoreContact D) :=
  ∀ b, base (unitEnds q b) = base' (unitEnds r b)

theorem Matches.depth {q : CoreContact C} {r : CoreContact D} (hm : Matches base base' q r) :
    contactDepth base unitEnds q = contactDepth base' unitEnds r :=
  congrArg₂ max (hm false) (hm true)

private theorem prefix_eq {i j k l : ℕ} (a : Cell k) (b : Cell l)
    (hi : i ≤ k) (hj : j ≤ l) (hk : i ≤ h) (hl : j ≤ h)
    (e : i = j) (f : (⟨k, a⟩ : Address) = ⟨l, b⟩) :
    (⟨⟨i, Nat.lt_succ_of_le hk⟩, ancestor hi a⟩ : Schedule.Address h) =
      ⟨⟨j, Nat.lt_succ_of_le hl⟩, ancestor hj b⟩ := by cases e; cases f; rfl

theorem Matches.site {z : Link base (unitEnds (C := C))} {z' : Link base' (unitEnds (C := D))}
    (hm : Matches base base' z.1 z'.1) (ha : address z = address z') (t : Bool) :
    (outLeaf base unitEnds hb z t).2 = (outLeaf base' unitEnds hb' z' t).2 :=
  prefix_eq z.2 z'.2 (le_contactDepth _ _ _ _) (le_contactDepth _ _ _ _) (hb _) (hb' _) (hm t) ha

def Reserves (base : V → ℕ) (base' : W → ℕ) (v : V) (w : W) : Prop :=
  ∀ (q : CoreContact C) t, unitEnds q t = v → ∃ r : CoreContact D,
    unitEnds r t = w ∧ s.label v (unitEnds q (!t)) = s'.label w (unitEnds r (!t)) ∧
    Matches base base' q r ∧ cap q = cap' r

theorem link_exists (z : Link base (unitEnds (C := C))) (c : CoreContact D)
    (hm : Matches base base' z.1 c) :
    ∃ z' : Link base' unitEnds, z'.1 = c ∧ address z = address z' := by
  exact ⟨⟨c, cast (congrArg Cell hm.depth) z.2⟩, rfl,
    Sigma.ext hm.depth (cast_heq _ _).symm⟩

theorem key_maps {v : V} {w : W} (hs : s.Reserves cap s' cap' base base' v w)
    (x : Schedule.Address h) (p : Ports hb cap Y (v, x)) :
    ∃ q : Ports hb' cap' Y (w, x), s.plugKey sym hb cap _ p = s'.plugKey sym' hb' cap' _ q := by
  obtain ⟨⟨⟨z, t⟩, hz⟩, i⟩ := p
  obtain ⟨c, hc, he, hm, hy⟩ := hs z.1 t (congrArg (fun z : Site V h => z.1) hz)
  obtain ⟨u, rfl, ha⟩ := link_exists z c hm
  have hloc : outLeaf base' unitEnds hb' u t = (w, x) :=
    Prod.ext hc ((Matches.site hb hb' hm ha t).symm.trans (congrArg Prod.snd hz))
  have hi : i.val < ⌈cap' u.1 * Y / 8⌉₊ := hy ▸ i.isLt
  exact ⟨⟨⟨(u, t), hloc⟩, ⟨i.val, hi⟩⟩, Prod.ext rfl (Prod.ext he (Prod.ext ha rfl))⟩

theorem plugs_eq [Fintype V] [Fintype W] {v : V} {w : W}
    (hs : s.Reserves cap s' cap' base base' v w) (ht : s'.Reserves cap' s cap base' base w v)
    (bound : ∀ x, Nonempty (Ports hb cap Y x ↪ Fin Y))
    (bound' : ∀ x, Nonempty (Ports hb' cap' Y x ↪ Fin Y))
    (x : Schedule.Address h) (p : Ports hb cap Y (v, x)) (q : Ports hb' cap' Y (w, x))
    (he : s.plugKey sym hb cap _ p = s'.plugKey sym' hb' cap' _ q) :
    s.plugs sym hb cap bound _ p = s'.plugs sym' hb' cap' bound' _ q :=
  rank_eq (s.key_maps sym hb cap s' sym' hb' cap' hs x)
    (s'.key_maps sym' hb' cap' s sym hb cap ht x) he

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Chart
end

/-!
# Testing exceptional contacts with local data

Capacity depends on one total over all blocks. Given that scalar,
testing a particular base reads only the loads in its own group.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Packing
open scoped Classical

variable {h a : ℕ} {ha : a ≤ h} {s : Cell a} {π : Equiv.Perm (Cell h)}

private def overfull (π : Equiv.Perm (Cell h)) (x : Cell h) {i k : ℕ} (hi : i ≤ h)
    (hk : i ≤ k) (cap : ℝ) (m : Cell h → ℝ) : Prop :=
  ∃ z : Cell k, ancestor hk z = ancestor hi (π x) ∧ cap < load m π k z

private theorem overfull_eq {x : Cell h} (hx : InGroup ha π s x)
    {i i' k k' : ℕ} (hi : i ≤ h) (hk : i ≤ k) (hi' : i' ≤ h) (hk' : i' ≤ k')
    (hm : a ≤ i) (e : i = i') (f : k = k')
    {c c' : ℝ} (hc : c = c') {m m' : Cell h → ℝ}
    (hw : ∀ y, InGroup ha π s y → m y = m' y) :
    overfull π x hi hk c m ↔ overfull π x hi' hk' c' m' := by
  subst i'; subst k'; subst c'
  unfold overfull
  apply exists_congr
  intro z
  by_cases hz : ancestor hk z = ancestor hi (π x)
  · have hs : ancestor (hm.trans hk) z = s := (congrArg (ancestor hm) hz).trans hx
    rw [load_eq ha π s hw (hm.trans hk) hs]
  · simp [hz]

variable {V W A A' : Type} {N : V → Finset V} {N' : W → Finset W}
  {d : V → V → ℕ} {d' : W → W → ℕ} {l : V → Cell h → ℝ} {l' : W → Cell h → ℝ}
  {v : V} {w : W} {base : V → ℕ} {base' : W → ℕ}
  {ends : A → Bool → V} {ends' : A' → Bool → W}
  {y : A → Cell h → ℝ} {y' : A' → Cell h → ℝ} {g g' : ℝ}

private def pressure (N : V → Finset V) (d : V → V → ℕ) (l : V → Cell h → ℝ)
    (π : Equiv.Perm (Cell h)) (v : V) {i : ℕ} (hi : i ≤ h) (x : Cell h) : Prop :=
  Spread N (fun p q => 8 * d p q) (High l π) v i (ancestor hi (π x))

private theorem failed_iff (hb : ∀ v, base v ≤ h) (x : Cell h) :
    BadBase N d base (contactDepth base ends) (contactEnd base ends) l y g π (prefixSite base hb π (v, x)) ↔
      pressure N d l π v (hb v) x ∨ ∃ c t, ends c t = v ∧
        overfull π x (hb (ends c t)) (le_contactDepth base ends c t)
          (mean (y c) (contactDepth base ends c) + 1 / g) (y c) := by
  unfold BadBase prefixSite pressure
  apply or_congr_right
  constructor
  · rintro ⟨⟨c, z⟩, t, hc, he⟩
    have hv : ends c t = v := congrArg Sigma.fst he
    subst v
    exact ⟨c, t, rfl, z, eq_of_heq (Sigma.mk.inj he).2, hc⟩
  · rintro ⟨c, t, rfl, z, he, hc⟩
    exact ⟨⟨c, z⟩, t, hc, congrArg (Sigma.mk (ends c t)) he⟩

/-- Match the incident contacts and their multiplicities at every block
in the group, as well as their aggregate capacities. -/
def Contacts (ha : a ≤ h) (π : Equiv.Perm (Cell h)) (s : Cell a)
    (base : V → ℕ) (ends : A → Bool → V) (y : A → Cell h → ℝ) (cap : A → ℝ)
    (base' : W → ℕ) (ends' : A' → Bool → W) (y' : A' → Cell h → ℝ) (cap' : A' → ℝ)
    (v : V) (w : W) : Prop :=
  ∀ c t, ends c t = v → ∃ c', ends' c' t = w ∧
    contactDepth base ends c = contactDepth base' ends' c' ∧ cap c = cap' c' ∧
    ∀ x, InGroup ha π s x → y c x = y' c' x

private theorem pressure_mono {R : ℕ → V → W → Prop}
    (hf : Forward ha π s R N N' (fun v w => 8 * d v w) (fun v w => 8 * d' v w) l l')
    (hr : R 0 v w) {i i' : ℕ} (hi : i ≤ h) (hi' : i' ≤ h) (ho : a ≤ i) (he : i = i')
    {x : Cell h} (hx : InGroup ha π s x) (p : pressure N d l π v hi x) :
    pressure N' d' l' π w hi' x := by
  subst i'
  exact hf.spread p hr ho hx

theorem Forward.failed {R : ℕ → V → W → Prop}
    (hf : Forward ha π s R N N' (fun v w => 8 * d v w) (fun v w => 8 * d' v w) l l')
    (hr : R 0 v w) (ho : a ≤ base v) (he : base v = base' w) (hb : ∀ v, base v ≤ h)
    (hb' : ∀ w, base' w ≤ h) (hc : Contacts ha π s base ends y
      (fun c => mean (y c) (contactDepth base ends c) + 1 / g) base' ends' y'
      (fun c' => mean (y' c') (contactDepth base' ends' c') + 1 / g') v w)
    {x : Cell h} (hx : InGroup ha π s x) :
    BadBase N d base (contactDepth base ends) (contactEnd base ends) l y g π (prefixSite base hb π (v, x)) →
      BadBase N' d' base' (contactDepth base' ends') (contactEnd base' ends') l' y' g' π
        (prefixSite base' hb' π (w, x)) := by
  rw [failed_iff, failed_iff]
  rintro (hp|⟨c, t, rfl, hc'⟩)
  · exact .inl (pressure_mono hf hr _ _ ho he hx hp)
  · obtain ⟨c', rfl, he', hcap, hy⟩ := hc c t rfl
    exact .inr ⟨c', t, rfl, (overfull_eq hx _ _ _ _ ho he he' hcap hy).mp hc'⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end
