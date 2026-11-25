import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation
import OAI.LinearAlgebra.MatrixExponent.Assembly.Mixer.Apply

/-!
# Reading contact loads from local patterns

The neighbor list may repeat the host itself. Choose one column per
oriented core contact, using the occupied column whenever there are
demands. All other columns contribute zero to the mixer score.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Finset Coloring Packing
open scoped Classical

def Pattern.uses {F : Type} {d k e : ℕ} (P : Pattern F d k e) (j : B d) :
    Finset (B e) := univ.filter fun s => (P.outgoing s).1 = true ∧ (P.outgoing s).2.1 = j

namespace Template.Encodes

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  {D : Template F} {G : HostNet F L D.scheme.h u} {r : D.format.obj} (p : D.Encodes r G)
  (hu : 0 < u)

def contactCol (c : CoreContact G.C) : B D.scheme.d :=
  let j := p.post.index c.val.1 c.val.2
  if D.nav r (p.post.host c.val.1) j = p.post.host c.val.2 then j
  else ((p.core _ _).mp c.property).choose

theorem nav_contact (c : CoreContact G.C) :
    D.nav r (p.post.host c.val.1) (p.contactCol c) = p.post.host c.val.2 := by
  unfold contactCol
  dsimp only
  split_ifs with he
  · exact he
  · exact ((p.core _ _).mp c.property).choose_spec.1

def contactLoc (c : CoreContact G.C) := (p.post.host c.val.1, p.contactCol c)

theorem contact_inj : Function.Injective p.contactLoc := by
  intro c z he
  obtain ⟨hs, ht⟩ := Prod.mk.inj he
  have hp := p.nav_contact c
  rw [hs, ht, p.nav_contact] at hp
  exact Subtype.ext (Prod.ext (p.post.host.injective hs) (p.post.host.injective hp.symm))

include hu in
theorem col_unit (i : G.E) : p.contactCol ((coreDemands G.ix G.edge).contact i) =
    p.post.index (G.src i) (G.dst i) := ite_eq_left (p.post.target hu i)

def usedCol (v : G.V) (b : Cell D.scheme.h) (j : B D.scheme.d) :=
  (D.scheme.decode ((r.1 (p.post.host v)).2 (cellIndex _ b))).uses j

include hu in
theorem used_iff (v : G.V) (b : Cell D.scheme.h) (j : B D.scheme.d) (s : B D.scheme.e) :
    s ∈ p.usedCol v b j ↔ ∃ i, G.src i = v ∧ G.ix i = b ∧ p.post.stub i false = s ∧
      p.contactCol ((coreDemands G.ix G.edge).contact i) = j := by
  unfold usedCol Pattern.uses
  rw [mem_filter, ← p.block]
  simp only [mem_univ, true_and]
  change (p.post.localStub v b s).1 = true ∧ (p.post.localStub v b s).2.1 = j ↔ _
  rw [p.post.active hu]
  constructor
  · rintro ⟨⟨i, rfl, rfl, rfl⟩, hh⟩
    rw [p.post.local_slot] at hh
    exact ⟨i, rfl, rfl, rfl, (p.col_unit hu i).trans hh⟩
  · rintro ⟨i, rfl, rfl, rfl, hc⟩
    exact ⟨⟨i, rfl, rfl, rfl⟩, (congrArg Prod.fst (p.post.local_slot i)).trans
      ((p.col_unit hu i).symm.trans hc)⟩

include hu in
theorem unused (v : G.V) (b : Cell D.scheme.h) (j : B D.scheme.d)
    (idle : (p.post.host v, j) ∉ Set.range p.contactLoc) : p.usedCol v b j = ∅ := by
  apply eq_empty_of_forall_notMem
  intro s hs
  obtain ⟨i, hv, _, _, hj⟩ := (p.used_iff hu _ _ _ _).mp hs
  exact idle ⟨(coreDemands G.ix G.edge).contact i, Prod.ext (congrArg p.post.host hv) hj⟩

include hu in
theorem contact_load (c : CoreContact G.C) (b : Cell D.scheme.h) (w : ℝ) :
    (coreDemands G.ix G.edge).amounts w c b = (p.usedCol c.val.1 b (p.contactCol c)).card * w := by
  let J := coreDemands G.ix G.edge
  let A := univ.filter fun i => J.edge i = (c, b)
  have hi (i : G.E) (he : i ∈ A) : G.src i = c.val.1 ∧ G.ix i = b := by
    obtain ⟨hc, hb⟩ := Prod.mk.inj (mem_filter.mp he).2
    exact ⟨congrArg (fun t => t.val.1) hc, hb⟩
  have hs : A.card = (p.usedCol c.val.1 b (p.contactCol c)).card := by
    apply card_bij (fun i _ => p.post.stub i false)
    · intro i he
      apply (p.used_iff hu _ _ _ _).mpr
      exact ⟨i, (hi i he).1, (hi i he).2, rfl, congrArg p.contactCol (Prod.mk.inj (mem_filter.mp he).2).1⟩
    · intro i h₁ j h₂ he
      apply p.post.distinct hu
      simp only [Scheme.Posting.span, Scheme.spanAt, Scheme.side, Bool.cond_false,
        (hi i h₁).1, (hi i h₁).2, (hi j h₂).1, (hi j h₂).2, he]
    · intro s hs
      obtain ⟨i, hv, hb, he, hc⟩ := (p.used_iff hu _ _ _ _).mp hs
      refine ⟨i, mem_filter.mpr ⟨mem_univ _, Prod.ext ?_ hb⟩, he⟩
      exact p.contact_inj (Prod.ext (congrArg p.post.host hv) hc)
  unfold Demands.amounts push
  rw [← hs, ← nsmul_eq_mul, ← sum_const]
  unfold A J
  rw [sum_filter]
  exact sum_congr rfl (fun i _ => by split_ifs <;> rfl)

end Template.Encodes
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Position and contact rows for the reset

Flatten a host and a short column index. Reserve one column for
the load of the position and one per neighboring host for outgoing
demands. All duplicate and unused contact columns have zero load.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing Finset
open scoped Classical

variable {F : Type} (D : Template F)

abbrev widthCols := D.scheme.d + 1
abbrev profileBits := D.scheme.ℓ + D.count
abbrev profileShape (k : ℕ) := Mixing.Records D.scheme.m D.widthCols D.scheme.h k D.profileBits

def heads {k : ℕ} (on : Bool) (a : B k) (near : B D.scheme.d → B k)
    (i : B D.widthCols) : (Mixing.Header k).obj :=
  ((halves D.scheme.d).symm i).elim (fun j => (on && decide (j = 0), false, a))
    (fun j => (on, true, max a (near j)))

def profile {k : ℕ} (r : D.format.obj) (base : B D.scheme.m → B k) : (D.profileShape k).obj :=
  fun v => (D.heads (D.live r v) (base v) (base ∘ D.nav r v),
    fun i => (Match.rowIndex D.scheme.ℓ D.count).symm ((r.1 v).2 i, D.counter r v i))

def getLoad (u Z d : ℕ) (x : B D.profileBits) (i : B D.widthCols) : B d :=
  let p := Match.rowIndex D.scheme.ℓ D.count x
  Fin.ofNat _ <| ((halves D.scheme.d).symm i).elim
    (fun _ => ⌊D.load p.2 * Z⌋₊)
    (fun j => ((D.scheme.decode p.1).uses j).card * u * Z)

def col (v : B D.scheme.m) (j : B D.scheme.d ⊕ B D.scheme.d) :=
  (Match.rowIndex D.scheme.m D.widthCols).symm (v, halves D.scheme.d j)

theorem header_col {k : ℕ} (r : D.format.obj) (base : B D.scheme.m → B k) v j :
    Mixing.header (D.profile r base) (D.col v j) =
      j.elim (fun i => (D.live r v && decide (i = 0), false, base v))
        (fun i => (D.live r v, true, max (base v) (base (D.nav r v i)))) := by
  simp [Mixing.header, profile, col, heads]

theorem digit_col {k : ℕ} (r : D.format.obj) (base : B D.scheme.m → B k) u Z d v j b :
    (Mixing.digit (D.getLoad u Z d) (D.profile r base) (D.col v j) b).val =
      (j.elim (fun _ => ⌊D.load (D.counter r v b) * Z⌋₊)
        (fun i => ((D.scheme.decode ((r.1 v).2 b)).uses i).card * u * Z)) % 2 ^ d := by
  simp [Mixing.digit, profile, col, getLoad]

namespace Encodes

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u k : ℕ}
  {D : Template F} {G : HostNet F L D.scheme.h u} {r : D.format.obj} (p : D.Encodes r G)

def rowId : G.V ⊕ CoreContact G.C ↪ B (D.scheme.m + D.widthCols) where
  toFun := Sum.elim (fun v => D.col (p.post.host v) (.inl 0))
    (fun c => D.col (p.contactLoc c).1 (.inr (p.contactLoc c).2))
  inj' := by
    rintro (v|c) (w|e) he <;>
      simp only [Sum.elim_inl, Sum.elim_inr, col, Equiv.symm_apply_eq, Equiv.apply_symm_apply,
        Prod.mk.injEq, (halves D.scheme.d).injective.eq_iff, reduceCtorEq, and_false] at he
    · exact congrArg Sum.inl (p.post.host.injective he.1)
    · exact congrArg Sum.inr (p.contact_inj (Prod.ext he.1 (Sum.inr.inj he.2)))

def depth (b : B D.scheme.m → B k) (v : G.V) := (b (p.post.host v)).val

theorem header_node (b : B D.scheme.m → B k) (v : G.V) :
    Mixing.header (D.profile r b) (p.rowId (.inl v)) = (true, false, b (p.post.host v)) := by
  change Mixing.header _ (D.col (p.post.host v) (.inl 0)) = _
  simp [D.header_col, (p.live _).mpr ⟨v, rfl⟩]

theorem header_link (b : B D.scheme.m → B k) (c : CoreContact G.C) :
    Mixing.header (D.profile r b) (p.rowId (.inr c)) =
      (true, true, max (b (p.post.host c.val.1)) (b (p.post.host c.val.2))) := by
  change Mixing.header _ (D.col (p.post.host c.val.1) (.inr (p.contactCol c))) = _
  simp [D.header_col, (p.live _).mpr ⟨c.val.1, rfl⟩, p.nav_contact]

theorem idle_col (hu : 0 < u) (b : B D.scheme.m → B k) (Z d : ℕ) (i : B (D.scheme.m + D.widthCols))
    (hi : i ∉ Set.range p.rowId) :
    (Mixing.header (D.profile r b) i).1 = false ∨
      ∀ z, (Mixing.digit (D.getLoad u Z d) (D.profile r b) i (cellIndex _ z)).val = 0 := by
  obtain ⟨⟨v, j⟩, rfl⟩ := (Match.rowIndex _ _).symm.surjective i
  obtain ⟨q, rfl⟩ := (halves _).surjective j
  change D.col v q ∉ Set.range p.rowId at hi
  change (Mixing.header _ (D.col v q)).1 = false ∨ _
  rw [D.header_col]
  by_cases hl : D.live r v = true
  swap
  · left
    cases q <;> simp [Bool.eq_false_iff.mpr hl]
  obtain ⟨w, rfl⟩ := (p.live _).mp hl
  cases q with
  | inl j =>
    have hn : j ≠ 0 := by rintro rfl; exact hi ⟨.inl w, rfl⟩
    left; simp [hn]
  | inr j =>
    right
    intro z
    have hn : (p.post.host w, j) ∉ Set.range p.contactLoc := by
      rintro ⟨c, hc⟩
      exact hi ⟨.inr c, congrArg (fun t : B D.scheme.m × B D.scheme.d => D.col t.1 (.inr t.2)) hc⟩
    change (Mixing.digit _ _ (D.col _ (.inr j)) _).val = _
    rw [D.digit_col]
    change ((p.usedCol w z j).card * u * Z) % 2 ^ d = 0
    simp [p.unused hu _ _ _ hn]

end Encodes
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Correctness of load extraction from a posting -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
open Coloring Packing Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u k d Z : ℕ}
  {D : Template F} {G : HostNet F L D.scheme.h u} {r : D.format.obj} (p : D.Encodes r G)
  (hu : 0 < u) (b : B D.scheme.m → B k)

omit [Field F] in
include hu in
theorem amounts_le (c : CoreContact G.C) (z : Cell D.scheme.h) :
    (coreDemands G.ix G.edge).amounts u c z ≤ G.load c.val.1 z := by
  refine ((coreDemands G.ix G.edge).amount_le u (by positivity) c false z).trans ?_
  unfold Demands.incident
  rw [← degree_push]
  exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load _ _)

theorem digit_self (v : G.V) (z : Cell D.scheme.h)
    (bound : ∃ n : B d, G.load v z * Z = n.val) :
    (Mixing.digit (D.getLoad u Z d) (D.profile r b) (p.rowId (.inl v)) (cellIndex _ z)).val =
      G.load v z * Z := by
  obtain ⟨n, hn⟩ := bound
  change ((Mixing.digit _ _ (D.col _ (.inl 0)) _).val : ℝ) = _
  rw [D.digit_col, Sum.elim_inl, ← p.block, p.load, hn, Nat.floor_natCast, Nat.mod_eq_of_lt n.isLt]

include hu in
theorem digit_link (c : CoreContact G.C) (z : Cell D.scheme.h)
    (bound : ∃ n : B d, G.load c.val.1 z * Z = n.val) :
    (Mixing.digit (D.getLoad u Z d) (D.profile r b) (p.rowId (.inr c)) (cellIndex _ z)).val =
      (coreDemands G.ix G.edge).amounts u c z * Z := by
  obtain ⟨n, hn⟩ := bound
  let j := (p.usedCol c.val.1 z (p.contactCol c)).card
  have hc : (coreDemands G.ix G.edge).amounts u c z = j * (u : ℝ) := p.contact_load hu c z u
  have hj : j * u * Z < 2 ^ d := by
    have h' := mul_le_mul_of_nonneg_right (amounts_le hu c z) (Nat.cast_nonneg (α := ℝ) Z)
    rw [hc, hn] at h'
    have : j * u * Z ≤ n.val := by exact_mod_cast h'
    exact this.trans_lt n.isLt
  change ((Mixing.digit _ _ (D.col _ (.inr (p.contactCol c))) _).val : ℝ) = _
  rw [D.digit_col, Sum.elim_inr, hc]
  change ((j * u * Z % 2 ^ d : ℕ) : ℝ) = _
  simp only [Nat.mod_eq_of_lt hj, Nat.cast_mul]

include hu in
theorem profiled (hk : D.scheme.h < 2 ^ k) (depths : ∀ v, p.depth b v ≤ D.scheme.h)
    (g : ℕ) (hg : 4 * g ^ 2 < 2 ^ d) (hw : 6 * 2 ^ D.scheme.h < 2 ^ d) (hZ : 0 < Z)
    (bound : ∀ v z, ∃ n : B d, G.load v z * Z = n.val) (W : ℝ) (hW : 0 < W) :
    let E := coreDemands G.ix G.edge
    Mixing.Encodes (p.depth b) (contactDepth (p.depth b) E.ends) (fun v z => G.load v z / W)
      (E.amounts (u / W)) g hk (Mixing.rows g (D.getLoad u Z d) (D.profile r b)) p.rowId (1 / (Z * W)) := by
  intro E
  have hq c : contactDepth (p.depth b) E.ends c ≤ D.scheme.h := max_le (depths _) (depths _)
  apply Mixing.encodes _ _ _ _ _ _ _ _ _ _ depths hq hg hw
  · intro v
    exact p.header_node b v
  · intro c
    exact p.header_link b c
  · exact p.idle_col hu b Z d
  · intro i z
    have ht : (Z : ℝ) ≠ 0 := by positivity
    cases i with
    | inl v =>
      rw [p.digit_self b v z (bound v z)]
      change G.load v z / W = _
      field_simp
    | inr c =>
      rw [p.digit_link hu b c z (bound c.val.1 z)]
      change E.amounts (u / W) c z = _
      unfold Demands.amounts
      rw [push_div]
      dsimp only [E]
      field_simp

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
end

/-!
# Computing base depths from the navigation masks

A port may repeat its own host address. Take the maximum of all
reported lower bounds. Missing tethers are harmless when their
delay exceeds the entire range of possible base depths.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing
open Coloring Packing Finset
open scoped Classical

variable {m d k : ℕ}

def update (Δ D : ℕ) (marks : (Group.Flags d).obj) (start : ℕ) (neighbor : B d → ℕ) :=
  max start (univ.sup fun j => if (marks j).2 then neighbor j - 32 * Nat.clog 2 (2 * Δ)
    else if (marks j).1 then neighbor j - 32 * Nat.clog 2 (2 * D) else 0)

def wave (Δ D : ℕ) (nav : B m → B d → B m) (flags : B m → (Group.Flags d).obj)
    (start : B m → B k) : ℕ → B m → B k
  | 0 => start
  | n + 1 => fun v => Fin.ofNat _ (update Δ D (flags v) (start v).val
      (fun j => (wave Δ D nav flags start n (nav v j)).val))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Mixing

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
open Coloring Packing Finset
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u k : ℕ}
  {A : Template F} {G : HostNet F L A.scheme.h u} {r : A.format.obj} (p : A.Encodes r G)
  {a Δ D : ℕ}

private theorem update_eq (hle : Δ ≤ D) (late : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
    (v : G.V) (l : ℕ) (lo : a ≤ l) (f : B A.scheme.m → ℕ) (high : ∀ w, f (p.post.host w) ≤ A.scheme.h) :
    Mixing.update Δ D (A.flags r (p.post.host v)) l (f ∘ A.nav r (p.post.host v)) =
      max l ((G.N v).sup fun z => f (p.post.host z) - 8 * resetDelay G.C Δ D v z) := by
  let M := A.flags r (p.post.host v)
  let N := A.nav r (p.post.host v)
  let cost j := if (M j).2 then f (N j) - 32 * Nat.clog 2 (2 * Δ)
    else if (M j).1 then f (N j) - 32 * Nat.clog 2 (2 * D) else 0
  let due z := f (p.post.host z) - 8 * resetDelay G.C Δ D v z
  change max l (univ.sup cost) = max l ((G.N v).sup due)
  have edge i z (hz : N i = p.post.host z) (hi : (M i).1 = true) : z ∈ G.N v := by
    have he := (p.edge v z).mpr ⟨i, hz, hi⟩
    unfold Template.adj at he
    split_ifs at he
    · exact he
    · exact G.sub _ he
  have core i z (hz : N i = p.post.host z) (hi : (M i).2 = true) : z ∈ G.C v :=
    (p.core v z).mpr ⟨i, hz, hi⟩
  have low := Nat.clog_mono_right 2 (Nat.mul_le_mul_left 2 hle)
  apply le_antisymm
  · refine max_le_max_left l (Finset.sup_le fun i _ => ?_)
    obtain ⟨z, hz⟩ := p.closed v i
    have eq : N i = p.post.host z := hz.symm
    unfold cost
    rw [eq]
    split_ifs with hc he
    · have hh := core i z eq hc
      apply le_trans _ (le_sup (f := due) (G.sub _ hh))
      simp only [due, resetDelay, ite_eq_left hh]
      omega
    · apply le_trans _ (le_sup (f := due) (edge i z eq he))
      unfold due resetDelay
      split_ifs <;> omega
    · exact Nat.zero_le _
  refine max_le (le_max_left _ _) (Finset.sup_le fun z hz => ?_)
  by_cases hc : z ∈ G.C v
  · obtain ⟨i, hi, hm⟩ := (p.core v z).mp hc
    refine le_trans ?_ ((le_sup (f := cost) (mem_univ i)).trans (le_max_right _ _))
    change N i = _ at hi
    change (M i).2 = true at hm
    simp only [due, resetDelay, ite_eq_left hc, cost, hm, ite_true, hi]
    omega
  by_cases full : A.full = true
  · obtain ⟨i, hi, hm⟩ := (p.edge v z).mp (by simpa [Template.adj, full] using hz)
    refine le_trans ?_ ((le_sup (f := cost) (mem_univ i)).trans (le_max_right _ _))
    change N i = _ at hi
    change (M i).1 = true at hm
    simp only [due, resetDelay, ite_eq_right hc, cost, hm, ite_true, hi]
    split_ifs <;> omega
  · apply le_max_of_le_left
    have ht := late (Bool.eq_false_iff.mpr full)
    have := high z
    simp only [due, resetDelay, ite_eq_right hc]
    omega

theorem wave_eq (hle : Δ ≤ D) (late : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
    (hk : A.scheme.h < 2 ^ k) (l : G.V → ℕ) (s : B A.scheme.m → B k)
    (bounds : ∀ v, a ≤ l v ∧ l v ≤ A.scheme.h) (init : ∀ v, (s (p.post.host v)).val = l v)
    (n : ℕ) (v : G.V) :
    (Mixing.wave Δ D (A.nav r) (A.flags r) s n (p.post.host v)).val =
      iterateDepth G.N (resetDelay G.C Δ D) l n v := by
  let iter := iterateDepth G.N (resetDelay G.C Δ D) l
  have bound n v : iter n v ≤ A.scheme.h :=
    depth_bounded _ _ _ (fun _ => A.scheme.h) (fun v => (bounds v).2)
      (fun _ _ _ => Nat.le_add_right _ _) n v
  induction n generalizing v with
  | zero => exact init v
  | succ n ih =>
    let f j := (Mixing.wave Δ D (A.nav r) (A.flags r) s n j).val
    have hm := p.update_eq hle late v (l v) (bounds v).1 f (fun w => (ih w).trans_le (bound n w))
    change Mixing.update Δ D _ _ (f ∘ _) % 2 ^ k = _
    rw [init, hm]
    simp only [f, ih]
    exact Nat.mod_eq_of_lt ((bound (n + 1) v).trans_lt hk)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Encodes
end

/-!
# Exact summaries of a posted network

The counter and the pattern of a single occurrence determine its
scaled load and its unit counts by outgoing contact. The initial
base depth is read from the sum of these short load words.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template

open Coloring Packing Finset
open scoped Classical

variable {F : Type} (A : Template F)

abbrev CounterBits := A.scheme.e + 1
abbrev CountBits := A.CounterBits + A.scheme.h
abbrev MixSource := Format.pair (.addr A.scheme.ℓ) (.addr A.count)
abbrev Summand (d : ℕ) := Format.pair (.addr d) (Mixing.Num A.scheme.d A.CounterBits)
abbrev Statistics (k : ℕ) := Format.pair (.addr k) (Mixing.Num A.scheme.d A.CountBits)

def source (r : A.format.obj) (v : B A.scheme.m) (i : B A.scheme.h) : A.MixSource.obj :=
  ((r.1 v).2 i, A.counter r v i)

def summand (Z d : ℕ) (t : A.MixSource.obj) : (A.Summand d).obj :=
  (Fin.ofNat _ ⌊A.load t.2 * Z⌋₊, fun j => ⟨((A.scheme.decode t.1).uses j).card, by
    refine (card_le_univ _).trans_lt ?_
    rw [Fintype.card_fin, CounterBits, pow_succ]
    have : 0 < (2 : ℕ) ^ A.scheme.e := by positivity
    omega⟩)

def request (a Z k : ℕ) (W : ℝ) {d : ℕ} (t : B d) : B k :=
  Fin.ofNat _ (requested a (t.val / ((Z : ℝ) * W)))

def summary (a Z k d : ℕ) (W : ℝ) (x : B A.scheme.h → A.MixSource.obj) : (A.Statistics k).obj :=
  (request a Z k W (total A.scheme.h d (fun i => (A.summand Z d (x i)).1)),
   Mixing.collect fun i => (A.summand Z d (x i)).2)

def unitCount (r : A.format.obj) (v : B A.scheme.m) (j : B A.scheme.d) : B A.CountBits :=
  (A.summary 0 0 0 0 0 (A.source r v)).2 j

def startDepth (a Z k d : ℕ) (W : ℝ) (r : A.format.obj) (v : B A.scheme.m) :=
  (A.summary a Z k d W (A.source r v)).1

def baseDepth (a t Δ D Z k d : ℕ) (W : ℝ) (r : A.format.obj) :=
  Mixing.wave Δ D (A.nav r) (A.flags r) (A.startDepth a Z k d W r) (A.scheme.h - t - a)

namespace Encodes
variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u k d Z : ℕ}
  {A : Template F} {G : HostNet F L A.scheme.h u} {r : A.format.obj} (p : A.Encodes r G)

theorem unit_count (v : G.V) (j : B A.scheme.d) :
    (A.unitCount r (p.post.host v) j).val = ∑ b, (p.usedCol v b j).card := by
  change (∑ b, ((A.scheme.decode ((r.1 (p.post.host v)).2 b)).uses j).card) = _
  rw [← (cellIndex _).sum_comp]
  rfl

theorem amount_total (hu : 0 < u) (c : CoreContact G.C) (w : ℝ) :
    (∑ z, (coreDemands G.ix G.edge).amounts w c z) =
      (A.unitCount r (p.post.host c.val.1) (p.contactCol c)).val * w := by
  rw [p.unit_count, Nat.cast_sum, sum_mul]
  exact sum_congr rfl (fun z _ => p.contact_load hu c z w)

theorem requested_eq (a : ℕ) (hk : A.scheme.h < 2 ^ k) (hZ : 0 < Z) (W : ℝ) (hW : 0 < W)
    (bound : ∀ v z, ∃ n : B d, G.load v z * Z = n.val)
    (req : ∀ v, requested a (∑ z, G.load v z / W) ≤ A.scheme.h) (v : G.V) :
    (A.startDepth a Z k d W r (p.post.host v)).val = requested a (∑ z, G.load v z / W) := by
  let s b := (A.summand Z d (A.source r (p.post.host v) b)).1
  have eq z : ((s (cellIndex _ z)).val : ℝ) = G.load v z * Z := by
    obtain ⟨n, hn⟩ := bound v z
    change ((⌊A.load (A.counter r _ (cellIndex _ z)) * Z⌋₊ % 2 ^ d : ℕ) : ℝ) = _
    rw [← p.block, p.load, hn, Nat.floor_natCast, Nat.mod_eq_of_lt n.isLt]
  have he : (total _ d s).val / ((Z : ℝ) * W) = ∑ z, G.load v z / W := by
    change (↑(∑ i, (s i).val) : ℝ) / _ = _
    rw [Nat.cast_sum, ← (cellIndex _).sum_comp, sum_div]
    apply sum_congr rfl
    intro z _
    rw [eq]
    field_simp
  change requested a ((total _ d s).val / ((Z : ℝ) * W)) % 2 ^ k = _
  rw [he, Nat.mod_eq_of_lt ((req _).trans_lt hk)]

theorem depths_eq {a t Δ D : ℕ} (hΔ : 0 < Δ) (hle : Δ ≤ D)
    (late : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D))
    (hk : A.scheme.h < 2 ^ k) (gap : a + t ≤ A.scheme.h) (hZ : 0 < Z) (W : ℝ) (hW : 0 < W)
    (bound : ∀ v z, ∃ n : B d, G.load v z * Z = n.val)
    (caps : ∀ v z, G.load v z / W ≤ 1 / (2 : ℝ) ^ t)
    (hc : ∀ v, (G.C v).card ≤ Δ) (hd : ∀ v, (G.N v).card ≤ D) :
    p.depth (A.baseDepth a t Δ D Z k d W r) =
      Mixing.depths G.N (resetDelay G.C Δ D) a t (fun v z => G.load v z / W) := by
  let l := fun v z => G.load v z / W
  have hb := (Mixing.depths_spec (delay := resetDelay G.C Δ D)
    (edge_weight_sum G.N G.C Δ D 4 hΔ (hΔ.trans_le hle) G.ns G.cs hd hc (by decide))
    gap l (fun v z => ⟨div_nonneg (G.load_nonneg v z) hW.le, caps v z⟩)).1
  have up v : requested a (∑ z, l v z) ≤ A.scheme.h :=
    ((requested_le _ _ _).mpr ⟨(hb v).1, (hb v).2.2⟩).trans ((hb v).2.1.trans (Nat.sub_le _ _))
  funext v
  exact p.wave_eq hle late hk _ _ (fun v => ⟨le_max_left _ _, up v⟩)
    (p.requested_eq a hk hZ W hW bound up) _ _

end Encodes
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Selecting a valid reset schedule from a template -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template

open Packing Coloring Finset
open scoped Classical

variable {F : Type} (A : Template F)

def mixerChoice (a t Δ D u g Z k d : ℕ) (hk : A.scheme.h < 2 ^ k) (W : ℝ) (r : A.format.obj) :=
  Mixing.choose hk (Mixing.rows g (A.getLoad u Z d) (A.profile r (A.baseDepth a t Δ D Z k d W r)))

namespace Encodes

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u : ℕ}
  {A : Template F} {G : HostNet F L A.scheme.h u} {r : A.format.obj} (p : A.Encodes r G)

/-- Number-format and graph bounds required by the reset controller. -/
structure Fits (a t Δ D g Z k d : ℕ) (W ε : ℝ) : Prop where
  corePos : 0 < Δ
  full : Δ ≤ D
  late : A.full = false → A.scheme.h - a ≤ 32 * Nat.clog 2 (2 * D)
  gap : a + t ≤ A.scheme.h
  depth : A.scheme.h < 2 ^ k
  integer : ∀ v z, ∃ n : B d, G.load v z * Z = n.val
  denominator : 0 < Z
  width : 0 < u
  margin : 0 < g
  widthLimit : 4 * g ^ 2 < 2 ^ d
  weightLimit : 6 * 2 ^ A.scheme.h < 2 ^ d
  capacity : 0 < W
  bound : ∀ v z, G.load v z / W ≤ 1 / (2 : ℝ) ^ t
  cdeg : ∀ v, (G.C v).card ≤ Δ
  ndeg : ∀ v, (G.N v).card ≤ D
  small : 144 * resetWeight t / (2 : ℝ) ^ t + 4 * (g : ℝ) ^ 2 / (2 : ℝ) ^ t ≤ ε

variable {a t Δ D g Z k d : ℕ} {W ε : ℝ}
  (ok : Fits (G := G) a t Δ D g Z k d W ε)

def resetSchedule : Schedule (coreDemands G.ix G.edge) G.N (resetDelay G.C Δ D) a t
    (fun v z => G.load v z / W) ((u : ℝ) / W) g ε := by
  let b := A.baseDepth a t Δ D Z k d W r
  let l := fun v z => G.load v z / W
  let delay := resetDelay G.C Δ D
  have budget := edge_weight_sum G.N G.C Δ D 4 ok.corePos (ok.corePos.trans_le ok.full)
    G.ns G.cs ok.ndeg ok.cdeg (by decide)
  have hl v z : 0 ≤ l v z ∧ l v z ≤ 1 / (2 : ℝ) ^ t :=
    ⟨div_nonneg (G.load_nonneg v z) ok.capacity.le, ok.bound v z⟩
  have hb := (Mixing.depths_spec (delay := delay) budget ok.gap l hl).1
  have eq := p.depths_eq ok.corePos ok.full ok.late ok.depth ok.gap ok.denominator W ok.capacity
    ok.integer ok.bound ok.cdeg ok.ndeg
  have depth v : p.depth b v ≤ A.scheme.h :=
    (congrFun eq v).trans_le ((hb v).2.1.trans (Nat.sub_le _ _))
  have enc := p.profiled ok.width b ok.depth depth g ok.widthLimit ok.weightLimit
    ok.denominator ok.integer W ok.capacity
  rw [show p.depth b = _ from eq] at enc
  refine Mixing.schedule _ G.N delay a t l _ _ ε ok.depth _ enc budget ok.gap hl
    ?_ (div_pos (Nat.cast_pos.mpr ok.width) ok.capacity) (Nat.cast_pos.mpr ok.margin) ok.small
  intro v z
  unfold Demands.incident
  rw [push_div, ← degree_push]
  exact div_le_div_of_nonneg_right
    ((le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load v z)) ok.capacity.le

theorem reset_mixer : (p.resetSchedule ok).π = menu _ (A.mixerChoice a t Δ D u g Z k d ok.depth W r) :=
  rfl

theorem reset_depth (v : G.V) :
    (p.resetSchedule ok).base v = (A.baseDepth a t Δ D Z k d W r (p.post.host v)).val :=
  congrFun (p.depths_eq ok.corePos ok.full ok.late ok.depth ok.gap ok.denominator W ok.capacity
    ok.integer ok.bound ok.cdeg ok.ndeg).symm v

theorem reset_capacity (c : CoreContact G.C) :
    (p.resetSchedule ok).capacity c =
      (A.unitCount r (p.post.host c.val.1) (p.contactCol c)).val * (u / W) /
        (2 : ℝ) ^ (contactDepth (p.resetSchedule ok).base unitEnds c) + 1 / g := by
  unfold Schedule.capacity mean
  rw [p.amount_total ok.width]
  rfl

end Encodes
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end
