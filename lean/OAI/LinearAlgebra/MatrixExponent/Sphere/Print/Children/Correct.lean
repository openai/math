import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Presentation
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Traces
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting

/-! # Addressing child hosts by a parent and a fixed trie slot -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical

abbrev Header (m e : ℕ) := Format.vec m (.pair .bit (.vec e .bit))
abbrev Tape (m e : ℕ) := (Neighborhood.Rows m e).pair (Header m e)
abbrev Part (M D k d : ℕ) := Node (Sharing.Slot M D k) (Sharing.radius k * d)
abbrev degree (e w : ℕ) := (e + 1) * 1 + w

def parts (V : Type) (M D k d : ℕ) : Host V M D k d ≃ V × Part M D k d where
  toFun v := ((root v).1, lift Prod.snd v)
  invFun j := lift (Prod.mk j.1) j.2
  left_inv v := by cases v <;> rfl
  right_inv j := by rcases j with ⟨v, s|s⟩ <;> rfl

variable {V : Type} {M D k d m e w : ℕ}

def hop (g : B m → B e → B m) (i j : B m) : B ((e + 1) * 1) :=
  if i = j then 0 else if h : ∃ z, Neighborhood.expand 1 g i z = j then h.choose else 0

@[simp] theorem hop_self (g : B m → B e → B m) (i : B m) : hop g i i = 0 := ite_eq_left rfl

theorem expand_hop {g : B m → B e → B m} {i j : B m} (h : Neighborhood.Reach g 1 i j) :
    Neighborhood.expand 1 g i (hop g i j) = j := by
  by_cases he : i = j
  · subst j
    rw [hop_self, Neighborhood.origin]
  obtain hh := Neighborhood.mem.mpr h
  rw [hop, ite_eq_right he, dite_eq_left hh]
  exact hh.choose_spec

structure Shows (adj : V → Finset V) (old : V ↪ B m) (r : (Tape m e).obj) : Prop where
  live : ∀ i, (r.2 i).1 = true ↔ i ∈ Set.range old
  closed : ∀ v j, r.1 (old v) j ∈ Set.range old
  reciprocal : ∀ v j, r.1 v j ≠ v → ∃! i, r.1 (r.1 v j) i = v
  edge : ∀ v z, v ≠ z → (z ∈ adj v ↔ ∃ j, r.1 (old v) j = old z ∧ (r.2 (old v)).2 j = true)

variable (old : V ↪ B m) (slot : Part M D k d ↪ B w)

def host : Host V M D k d ↪ B (m + w) :=
  (parts V M D k d).toEmbedding.trans ((old.prodMap slot).trans (Match.rowIndex m w).symm.toEmbedding)

def idx (g : B m → B e → B m) (x y : Host V M D k d) : B (degree e w) :=
  (Match.rowIndex _ w).symm (hop g (old (root x).1) (old (root y).1), slot (lift Prod.snd y))

@[simp] theorem host_split (x : Host V M D k d) :
    Match.rowIndex m w (host old slot x) = (old (root x).1, slot (lift Prod.snd x)) :=
  (Match.rowIndex _ _).apply_symm_apply _

@[simp] theorem idx_split (g : B m → B e → B m) (x y : Host V M D k d) :
    Match.rowIndex ((e + 1) * 1) w (idx old slot g x y) =
      (hop g (old (root x).1) (old (root y).1), slot (lift Prod.snd y)) :=
  (Match.rowIndex _ _).apply_symm_apply _

variable {old} {adj : V → Finset V} {r : (Tape m e).obj} (p : Shows adj old r)

include p in
theorem Shows.reach {v z : V} (he : z ∈ insert v (adj v)) : Neighborhood.Reach r.1 1 (old v) (old z) := by
  rcases Finset.mem_insert.mp he with rfl | he
  · exact Neighborhood.Reach.refl ..
  by_cases h : v = z
  · subst z; exact Neighborhood.Reach.refl ..
  obtain ⟨j, hj, _⟩ := (p.edge _ _ h).mp he
  exact ⟨_, Or.inr ⟨j, hj⟩, rfl⟩

def Shows.steer (hb : 2 ^ ((e + 1) * 1) ≤ D ^ k + 1) : Sharing.Steering adj (D ^ k) where
  rank v z := (hop r.1 (old v) (old z)).castLE hb
  inject v x hx y hy eq := by
    have hh : hop r.1 (old v) (old x) = hop r.1 (old v) (old y) := Fin.castLE_injective hb eq
    exact old.injective ((expand_hop (p.reach hx)).symm.trans (hh ▸ expand_hop (p.reach hy)))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # Reading one-hop contacts and their return columns from short masks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}

abbrev hops (e : ℕ) := (e + 1) * 1
abbrev comparisons (a b : ℕ) := Format.vec a (.vec b (.vec a .bit))
abbrev Info (e : ℕ) := Format.pair (.pair .bit (.vec e .bit))
  (.pair (comparisons (hops e) e) (comparisons (hops e) (hops e)))
abbrev Query (m e : ℕ) := (Neighborhood.Rows m (hops e)).pair (.vec m (Info e))

def prepare (r : (Tape m e).obj) : (Query m e).obj :=
  let g := Neighborhood.expand 1 r.1
  (g, fun v => (r.2 v, Neighborhood.maskRows g r.1 v, Neighborhood.maskRows g g v))

def contact (x : (Info e).obj) (i : B (hops e)) : Prop :=
  i = 0 ∨ (x.2.2 0 0 i = false ∧ ∃ j, x.2.1 0 j i = true ∧ x.1.2 j = true)

def back (x : (Info e).obj) (i : B (hops e)) : B (hops e) :=
  if x.2.2 i 0 0 then 0 else if h : ∃ j, x.2.2 i j 0 = true then h.choose else 0

variable {adj : V → Finset V} {old : V ↪ B m} {r : (Tape m e).obj} (p : Shows adj old r)
  {v z : V} {i : B (hops e)}

include p in
theorem Shows.closed_expand (v : V) (i : B (hops e)) :
    Neighborhood.expand 1 r.1 (old v) i ∈ Set.range old := by
  obtain ⟨y, he, hy⟩ := (Neighborhood.mem
    (g := r.1) (r := 1) (x := old v)).mp ⟨i, rfl⟩
  change y = Neighborhood.expand 1 r.1 (old v) i at hy
  rw [← hy]
  rcases he with rfl|⟨j, rfl⟩
  · exact ⟨v, rfl⟩
  · exact p.closed v j

include p in
theorem Shows.contact_eq (he : Neighborhood.expand 1 r.1 (old v) i = old z) :
    contact ((prepare r).2 (old v)) i ↔
      z ∈ insert v (adj v) ∧ i = hop r.1 (old v) (old z) := by
  simp only [contact, prepare, Neighborhood.maskRows, Neighborhood.origin, he, decide_eq_true_eq,
    decide_eq_false_iff_not, old.injective.eq_iff]
  by_cases h : v = z
  · subst z
    simp
  have hi : i ≠ 0 := by
    rintro rfl
    exact h (old.injective (Neighborhood.origin.symm.trans he))
  have hk : i = hop r.1 (old v) (old z) :=
    Neighborhood.unique he (expand_hop (Neighborhood.mem.mp ⟨i, he⟩))
      (fun e => h (old.injective e.symm))
  rw [← p.edge _ _ h, Finset.mem_insert]
  exact ⟨fun he => ⟨.inr (he.resolve_left hi).2, hk⟩,
    fun he => .inr ⟨h, he.1.resolve_left (Ne.symm h)⟩⟩

theorem back_eq (v : B m) (i : B (hops e)) :
    back ((prepare r).2 v) i = hop r.1 (Neighborhood.expand 1 r.1 v i) v := by
  simp only [back, prepare, Neighborhood.maskRows, Neighborhood.origin, decide_eq_true_eq, hop]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # Testing a trie edge from two slots and a pair of short hop codes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}

def fixed : Part M D k d → Prop := Sum.elim Sharing.frozenSlot (fun _ => False)

variable (hD : D = 2 ^ d) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ (hops e) ≤ D ^ k + 1)

def link (f : (Info e).obj) (j : B (hops e)) (x y : Part M D k d) : Prop :=
  contact f j ∧ traceAdj (j = 0 ∧ root x = root y)
    (Sharing.frozenSlot (root x)) (Sharing.frozenSlot (root y))
    (Sharing.Geo.steeringCode hD hd hc (j.castLE hb, root y))
    (Sharing.Geo.steeringCode hD hd hc ((back f j).castLE hb, root x))
    (lift (fun _ => ()) x) (lift (fun _ => ()) y)

theorem root_part (x : Host V M D k d) : root (lift Prod.snd x) = (root x).2 := by
  cases x <;> rfl

theorem shape_part (x : Host V M D k d) :
    lift (fun _ => ()) (lift Prod.snd x) = lift (fun _ => ()) x := by cases x <;> rfl

variable {F T X E Z K : Type} {r t : ℕ}
    {C : Z → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
    {S : Sharing C a b Y} {h W₀ R g : ℕ} {W : ℝ} {P : Rounds.Input F a b h D W₀ R g W}
    {old : P.V ↪ B m} {u : (Tape m e).obj} (G : S.Geo P k)
    (p : Shows P.adj old u) (hs : G.steer = p.steer hb)
local notation "T₀" => (G.tree hD hd)
local notation "H" => Host P.V M D k d

theorem fixed_iff (x : H) : fixed (lift Prod.snd x) ↔ (T₀).fixed x := by
  cases x <;> rfl

theorem adj_root {x y : H} (he : y ∈ (T₀).adj x) : (root y).1 ∈ insert (root x).1 (P.adj (root x).1) :=
  (Finset.mem_product.mp (adj_near T₀ (fun _ => Finset.mem_product.mpr
    ⟨Finset.mem_insert_self .., Finset.mem_univ _⟩) he)).1

include hs in
theorem link_iff (x y : H) (i : B (hops e))
    (he : Neighborhood.expand 1 u.1 (old (root x).1) i = old (root y).1) :
    link hD hd hc hb ((prepare u).2 (old (root x).1)) i (lift Prod.snd x) (lift Prod.snd y) ↔
      y ∈ (T₀).adj x ∧ i = hop u.1 (old (root x).1) (old (root y).1) := by
  unfold link
  rw [p.contact_eq he, back_eq, he, root_part, root_part, shape_part, shape_part]
  have near (h : (root y).1 ∈ insert (root x).1 (P.adj (root x).1))
      (hi : i = hop u.1 (old (root x).1) (old (root y).1)) :
      y ∈ (T₀).adj x ↔ traceAdj (i = 0 ∧ (root x).2 = (root y).2)
        (Sharing.frozenSlot (root x).2) (Sharing.frozenSlot (root y).2)
        (Sharing.Geo.steeringCode hD hd hc (i.castLE hb, (root y).2))
        (Sharing.Geo.steeringCode hD hd hc ((hop u.1 (old (root y).1) (old (root x).1)).castLE hb, (root x).2))
        (lift (fun _ => ()) x) (lift (fun _ => ()) y) := by
    have hsame : (root x = root y) ↔ i = 0 ∧ (root x).2 = (root y).2 := by
      constructor
      · intro eq
        rw [hi, eq, hop_self]
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, hz⟩
        exact Prod.ext (old.injective (Neighborhood.origin.symm.trans he)) hz
    have code (a b : Bench P.V M D k) :
        (T₀).code a b = Sharing.Geo.steeringCode hD hd hc
          ((hop u.1 (old a.1) (old b.1)).castLE hb, b.2) := by
      change Sharing.Geo.steeringCode hD hd hc (G.steer.rank a.1 b.1, b.2) = _
      rw [hs]; rfl
    rw [adj_iff T₀ (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩), hsame, code, code, hi]
  constructor
  · rintro ⟨⟨h, hi⟩, eq⟩
    exact ⟨(near h hi).mpr eq, hi⟩
  · rintro ⟨h, hi⟩
    have hr := adj_root hD hd G h
    exact ⟨⟨hr, hi⟩, (near hr hi).mp h⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # Graph headers of the expanded trie -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}
open Assembly.History.Reset
variable (slot : Part M D k d ↪ B w)
  (hD : D = 2 ^ d) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ (hops e) ≤ D ^ k + 1)

def valid (f : (Info e).obj) (s : B w) : Prop := f.1.1 = true ∧ s ∈ Set.range slot

def frozen (s : B w) : Prop := ∃ z, slot z = s ∧ fixed z

@[simp] theorem frozen_slot (x : Part M D k d) : frozen slot (slot x) ↔ fixed x := by
  simp [frozen, slot.injective.eq_iff]

def enabled (f : (Info e).obj) (s : B w) (j : B (degree e w)) : Prop :=
  let v := Match.rowIndex (hops e) w j
  f.1.1 = true ∧ ∃ x y, slot x = s ∧ slot y = v.2 ∧ link hD hd hc hb f v.1 x y

def record (f : (Info e).obj) (s : B w) : (Child.Suffix (hops e) w (degree e w)).obj :=
  ((decide (valid slot f s), decide (frozen slot s)), fun j =>
    let v := Match.rowIndex (hops e) w j
    if enabled slot hD hd hc hb f s j then
      ((true, decide (¬frozen slot s ∧ ¬frozen slot v.2)), BatchDescent.Trail.hop _ (some v.1), v.2)
    else ((false, false), BatchDescent.Trail.hop _ none, s))

def entries (u : (Tape m e).obj) : (Child.Input m (hops e) w (degree e w)).obj :=
  ((prepare u).1, fun i => record slot hD hd hc hb
    ((prepare u).2 (Match.rowIndex m w i).1) (Match.rowIndex m w i).2)

def graph (u : (Tape m e).obj) : (Child.Graph (m + w) (degree e w)).obj :=
  Child.build _ _ _ _ (entries slot hD hd hc hb u)

variable {old : V ↪ B m} {u : (Tape m e).obj} {adj : V → Finset V} (p : Shows adj old u)
local notation "net" => graph slot hD hd hc hb u
local notation "entry" => entries slot hD hd hc hb u
local notation "split" => Match.rowIndex m w
local notation "addr" => host old slot

include p in
theorem valid_iff (x : B (m + w)) :
    valid slot ((prepare u).2 (split x).1) (split x).2 ↔ x ∈ Set.range addr := by
  change (u.2 _).1 = true ∧ _ ↔ _
  rw [p.live]
  constructor
  · rintro ⟨⟨v, hv⟩, ⟨s, hs⟩⟩
    refine ⟨(parts V M D k d).symm (v, s), (split).injective ?_⟩
    have eq := (parts V M D k d).apply_symm_apply (v, s)
    rw [host_split]
    exact (congrArg (Prod.map old slot) eq).trans (Prod.ext hv hs)
  · rintro ⟨i, rfl⟩
    rw [host_split]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

include p in
theorem live (x : B (m + w)) : ((net).2 x).1.1 = true ↔ x ∈ Set.range addr := by
  change decide (valid slot ((prepare u).2 (split x).1) (split x).2) = true ↔ _
  rw [decide_eq_true_eq, valid_iff slot p]

theorem fixed_slot (x : Host V M D k d) :
    ((net).2 (addr x)).1.2 = true ↔ fixed (lift Prod.snd x) := by
  change decide (frozen slot (split (addr x)).2) = true ↔ _
  rw [decide_eq_true_eq, host_split, frozen_slot]

def used (x : B (m + w)) (j : B (degree e w)) :=
  enabled slot hD hd hc hb ((prepare u).2 (split x).1) (split x).2 j

theorem spare (x : B (m + w)) (j : B (degree e w)) (hj : ¬used slot hD hd hc hb (u:=u) x j) :
    (net).1 x j = x ∧ ((net).2 x).2 j = (false, false) := by
  have he : ((entry).2 x).2 j = ((false, false), BatchDescent.Trail.hop _ none, (split x).2) :=
    ite_eq_right hj
  exact ⟨Child.build_stay entry x j (congrArg Prod.snd he), congrArg Prod.fst he⟩

include p in
theorem idle (x : B (m + w)) (hx : x ∉ Set.range addr) (j : B (degree e w)) :
    (net).1 x j = x := by
  refine (spare slot hD hd hc hb x j ?_).1
  rintro ⟨hv, s, t, he, _⟩
  exact hx ((valid_iff slot p x).mp ⟨hv, s, he⟩)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # The enabled columns are exactly the incident trie edges -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}
open Assembly.History.Reset
variable (slot : Part M D k d ↪ B w)
  (hD : D = 2 ^ d) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ (hops e) ≤ D ^ k + 1)
variable {F T X E Z K : Type} {r t : ℕ}
    {C : Z → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
    {S : Sharing C a b Y} {h W₀ R g : ℕ} {W : ℝ} {P : Rounds.Input F a b h D W₀ R g W}
    {old : P.V ↪ B m} {u : (Tape m e).obj} (G : S.Geo P k)
    (p : Shows P.adj old u) (hs : G.steer = p.steer hb)
local notation "T₀" => (G.tree hD hd)
local notation "H" => Host P.V M D k d
local notation "net" => graph slot hD hd hc hb u
local notation "entry" => entries slot hD hd hc hb u
local notation "split" => Match.rowIndex m w
local notation "col" => Match.rowIndex (hops e) w
local notation "addr" => host old slot
local notation "ix" => idx old slot (Prod.fst u)
local notation "test" => used slot hD hd hc hb (u:=u)

include hs in
theorem columns (x : H) (j : B (degree e w)) :
    test (addr x) j ↔ ∃ y ∈ (T₀).adj x, ix x y = j := by
  unfold used enabled
  rw [host_split]
  have live := (p.live _).mpr ⟨(root x).1, rfl⟩
  constructor
  · rintro ⟨_, v, z, hv, hz, hl⟩
    have eq : v = lift Prod.snd x := slot.injective hv
    subst v
    obtain ⟨i, hi⟩ := p.closed_expand (root x).1 (col j).1
    let y := (parts P.V M D k d).symm (i, z)
    have hr : ((root y).1, lift Prod.snd y) = (i, z) := (parts P.V M D k d).apply_symm_apply _
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hr
    have he : Neighborhood.expand 1 u.1 (old (root x).1) (col j).1 = old (root y).1 := by rw [h₁, hi]
    obtain ⟨hadj, hh⟩ := (link_iff hD hd hc hb G p hs x y (col j).1 he).mp (h₂.symm ▸ hl)
    refine ⟨y, hadj, (col).injective ?_⟩
    rw [idx_split, h₂, hz, ← hh]
  · rintro ⟨y, hy, rfl⟩
    rw [idx_split]
    have he := expand_hop (p.reach (adj_root hD hd G hy))
    exact ⟨live, _, _, rfl, rfl, (link_iff hD hd hc hb G p hs x y _ he).mpr ⟨hy, rfl⟩⟩

include hs in
theorem used_column (x y : H) (hy : y ∈ (T₀).adj x) :
    (net).1 (addr x) (ix x y) = addr y ∧
      ((net).2 (addr x)).2 (ix x y) = (true, decide (y ∈ (T₀).core x)) := by
  have used := (columns slot hD hd hc hb G p hs x _).mpr ⟨y, hy, rfl⟩
  have he : ((entry).2 (addr x)).2 (ix x y) =
      ((true, decide (¬frozen slot (split (addr x)).2 ∧ ¬frozen slot (col (ix x y)).2)),
        BatchDescent.Trail.hop _ (some (col (ix x y)).1), (col (ix x y)).2) := ite_eq_left used
  rw [host_split, idx_split] at he
  constructor
  · have hx := Child.build_hop entry (addr x) (ix x y) _ _ (congrArg Prod.snd he)
    dsimp only [Option.elim] at hx
    rw [host_split] at hx
    refine hx.trans ?_
    apply (split).symm_apply_eq.mpr
    rw [host_split]
    exact Prod.ext (expand_hop (p.reach (adj_root hD hd G hy))) rfl
  · refine (congrArg Prod.fst he).trans ?_
    simp only [frozen_slot, fixed_iff hD hd G, Trie.core, Finset.mem_filter, hy, true_and]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # Replicating each block label with its static child address -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}
open Assembly.History.Reset
variable (slot : Part M D k d ↪ B w)
  (hD : D = 2 ^ d) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ (hops e) ≤ D ^ k + 1)

abbrev input (m e h l : ℕ) := Format.pair (Fmt.rows m e h (.addr l)) (Header m e)
abbrev labels (m h l w : ℕ) := Format.vec (m + w) (.vec h (.addr (l + w)))

abbrev output (m e h l w : ℕ) := Format.pair (Fmt.rows (m + w) (degree e w) h (.addr (l + w)))
  (.vec (m + w) (.pair (.pair .bit .bit) (.pair (Group.Flags (degree e w)) (.vec h (.addr (l + w))))))

variable {h l : ℕ}

def tape (r : (input m e h l).obj) : (Tape m e).obj := (fun i => (r.1 i).1, r.2)

def label (w : ℕ) (r : (input m e h l).obj) : (labels m h l w).obj :=
  fun i j => let v := Match.rowIndex m w i
    (Match.rowIndex l w).symm ((r.1 v.1).2 j, v.2)

def join (x : (Format.pair (Child.Graph (m + w) (degree e w)) (labels m h l w)).obj) :
    (output m e h l w).obj :=
  (fun i => (x.1.1 i, x.2 i), fun i => ((x.1.2 i).1, (x.1.2 i).2, x.2 i))

def write (r : (input m e h l).obj) : (output m e h l w).obj :=
  join (graph slot hD hd hc hb (tape r), label w r)

theorem label_at (r : (input m e h l).obj) (i : B (m + w)) (j : B h) :
    Match.rowIndex l w (label w r i j) =
      ((r.1 (Match.rowIndex m w i).1).2 j, (Match.rowIndex m w i).2) :=
  (Match.rowIndex l w).apply_symm_apply _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # Correctness of the printed host graph -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
open Assembly Coloring OAI.LinearAlgebra.MatrixExponent.Sphere.Layout
open scoped Classical
variable {V : Type} {M D k d m e w : ℕ}
open Assembly.History.Reset
variable (slot : Part M D k d ↪ B w)
  (hD : D = 2 ^ d) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ (hops e) ≤ D ^ k + 1)
variable {F T X E Z K : Type} {r t : ℕ}
    {C : Z → Surface.Cell F (M * r) (M * t) T E X} {a b : Wire} {Y : Alphabet K}
    {S : Sharing C a b Y} {h W₀ R g : ℕ} {W : ℝ} {P : Rounds.Input F a b h D W₀ R g W}
    {old : P.V ↪ B m} {u : (Tape m e).obj} (G : S.Geo P k)
    (p : Shows P.adj old u) (hs : G.steer = p.steer hb)
local notation "T₀" => (G.tree hD hd)
local notation "H" => Host P.V M D k d
local notation "net" => graph slot hD hd hc hb u
local notation "addr" => host old slot
local notation "ix" => idx old slot (Prod.fst u)
local notation "test" => used slot hD hd hc hb (u:=u)

include hs

private theorem classify (x : H) (j : B (degree e w)) :
    (∃ y ∈ (T₀).adj x, ix x y = j) ∨
      ((net).1 (addr x) j = addr x ∧ ((net).2 (addr x)).2 j = (false, false)) := by
  by_cases h : test (addr x) j
  · exact .inl ((columns slot hD hd hc hb G p hs _ _).mp h)
  · exact .inr (spare slot hD hd hc hb _ _ h)

local notation "data" => used_column slot hD hd hc hb G p hs
local notation "inspect" => classify slot hD hd hc hb G p hs

theorem closed (v : H) (j : B (degree e w)) : (net).1 (addr v) j ∈ Set.range addr := by
  rcases inspect v j with ⟨z, hz, rfl⟩|⟨he, _⟩
  · exact ⟨z, (data _ _ hz).1.symm⟩
  · exact ⟨v, he.symm⟩

theorem reciprocal (i : B (m + w)) (j : B (degree e w)) (hn : (net).1 i j ≠ i) :
    ∃! t, (net).1 ((net).1 i j) t = i := by
  by_cases hi : i ∈ Set.range addr
  swap
  · exact (hn (idle slot hD hd hc hb p i hi j)).elim
  obtain ⟨v, rfl⟩ := hi
  rcases inspect v j with ⟨z, hz, rfl⟩|⟨he, _⟩
  swap
  · exact (hn he).elim
  rw [(data _ _ hz).1] at hn ⊢
  refine ⟨ix z v, (data _ _ ((T₀).adj_symm hz)).1, fun j he => ?_⟩
  rcases inspect z j with ⟨t, ht, rfl⟩|⟨hh, _⟩
  · exact congrArg (ix z) ((addr).injective ((data _ _ ht).1.symm.trans he))
  · exact (hn (hh.symm.trans he)).elim

theorem edge (v z : H) :
    z ∈ (T₀).adj v ↔ ∃ j, (net).1 (addr v) j = addr z ∧ (((net).2 (addr v)).2 j).1 = true := by
  constructor
  · intro h
    exact ⟨ix v z, (data _ _ h).1, congrArg Prod.fst (data _ _ h).2⟩
  rintro ⟨j, he, h⟩
  rcases inspect v j with ⟨t, ht, rfl⟩|⟨_, hh⟩
  · exact (addr).injective ((data _ _ ht).1.symm.trans he) ▸ ht
  · rw [hh] at h; cases h

theorem core (v z : H) :
    z ∈ (T₀).core v ↔ ∃ j, (net).1 (addr v) j = addr z ∧ (((net).2 (addr v)).2 j).2 = true := by
  constructor
  · intro h
    have hd := data _ _ (Finset.mem_filter.mp h).1
    exact ⟨ix v z, hd.1, by rw [hd.2]; exact decide_eq_true h⟩
  rintro ⟨j, he, h⟩
  rcases inspect v j with ⟨t, ht, rfl⟩|⟨_, hh⟩
  · have e := (addr).injective ((data _ _ ht).1.symm.trans he)
    subst z
    rw [(data _ _ ht).2] at h
    exact of_decide_eq_true h
  · rw [hh] at h; cases h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children
end

/-! # Short bundle names from a colored atlas and local key aliases -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place item)
open scoped Classical

variable {F T V E X K : Type} [Fintype V] {r t M n B d h R q g : ℕ}
  {Y : Alphabet V} {a b : Wire} (s : Stage F (M * r) (M * t) T V E X) (A : Key.Source Y a b s)
  (c : Atlas V E B d h) (π : Palette c R q) (β : V ⊕ ℕ → K)

def coordinate (hc : ∀ v, (s.scene.cell v).stations.length ≤ n) (i : Place s.scene.cell) :
    Bool × Fin n := (decide ((item s.scene.cell i).label.role = .collector), Fin.castLE (hc i.1) i.2)

def marking (hc : ∀ v, (s.scene.cell v).stations.length ≤ n)
    (hs : A.src = c.src) (ht : A.dst = c.dst) (hR : 2 ≤ R) (hl : s.Layout c.src c.dst g)
    (hd : Distinct (c.near 1) s β) : Marking (Key.share s A) (Fin q) (Bool × Fin n) K where
  mark := π.mark
  number := coordinate s hc
  key := β ∘ Key.name s.hidden
  atCell i j h he := by
    obtain ⟨v, i⟩ := i
    obtain ⟨w, j⟩ := j
    change v = w at h
    subst w
    have eq : i = j := Fin.ext (congrArg (fun p : Bool × Fin n => p.2.val) he)
    rw [eq]
  atKey v j hj k hk he := (Key.name s.hidden).injective <|
    hd v v (.refl ..) _ (Key.mem_filter.mp hj) _ (Key.mem_filter.mp hk) he
  across e i j hi hj he := by
    apply (Key.name s.hidden).injective
    have h' : c.near 1 (A.src e) (A.dst e) := by rw [hs, ht]; exact c.near_edge e
    exact hd _ _ h' _ (Key.mem_filter.mp hi) _ (Key.mem_filter.mp hj) he
  marks e he := by
    apply π.distinguish _ he
    change c.near R (A.src e) (A.dst e)
    rw [hs, ht]
    exact (c.near_edge e).mono (by omega)
  seams v e f he hf eq := by
    have pair (j : E) (hj : uses (Key.share s A) v j) :
        c.near 1 v (A.src j) ∧ c.near 1 v (A.dst j) := by
      change A.src j = v ∨ A.dst j = v at hj
      rw [hs, ht] at hj ⊢
      rcases hj with rfl|rfl
      · exact ⟨.refl .., c.near_edge _⟩
      · exact ⟨(c.near_edge _).symm, .refl ..⟩
    have h₁ := π.injective_at hR (pair e he).1 (pair f hf).1 (Prod.mk.inj eq).1
    have h₂ := π.injective_at hR (pair e he).2 (pair f hf).2 (Prod.mk.inj eq).2
    rw [hs] at h₁
    rw [ht] at h₂
    exact c.links (Prod.ext h₁ h₂)
  ports v e he := by
    change A.src e = v ∨ A.dst e = v at he
    rw [hs, ht] at he
    obtain ⟨⟨j, z⟩, hj, rfl⟩ := List.mem_map.mp ((hl.incident v e).mpr he)
    exact ⟨z, hj⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end
