import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks
import OAI.LinearAlgebra.MatrixExponent.Packing.Suffix

/-! # Bounding the number of hidden spans by earlier incidences -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
open Finset Packing
open scoped Classical

private theorem loops {E V : Type} [Fintype E] (f : E → V × V) (v : V) :
    Fintype.card {e // f e = (v, v)} ≤ degree f v := by
  rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter, degree_sum]
  apply sum_le_sum
  intro e _
  by_cases he : f e = (v, v) <;> simp [he, arityCost]

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z : ℕ}
  (P : Gadget F) (G : HostNet F L h (P.b * z))
  {Δ D k : ℕ} {B : ℝ} (g : Grouping G.N G.C Δ D k B G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)
  (v : Site G.V h)

private theorem degree_ends :
    degree (ends g m P i) v = 2 * degree (g.oldContact m (g.layout m P i)) v +
      degree (g.contact (b := P.b) (f := g.profile m i) m (g.layout m P i)) v := by
  let f := g.oldContact m (g.layout m P i)
  rw [degree_sum, degree_sum, degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type,
    ← add_assoc, ← sum_add_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  change arityCost v ((f j).1, (f j).1) + arityCost v ((f j).2, (f j).2) = 2 * arityCost v (f j)
  simp only [arityCost]
  omega

theorem hidden_bound (hB : 0 ≤ B) :
    Fintype.card (Hidden g m P i v) * (z : ℝ) ≤ 10 * (near G.C Δ v).card * ((2 : ℝ) ^ k * B) := by
  let col := g.layout m P i
  let n := degree (g.oldContact m col) v
  have hi : Fintype.card (Hidden g m P i v) ≤ 10 * P.b * n := calc
    _ ≤ degree (ends g m P i) v := by convert! loops (ends g m P i) v using 2
    _ = _ := degree_ends P G g m i v
    _ ≤ 2 * n + 8 * P.b * n := Nat.add_le_add_left
      (g.contact_degree m P.b (g.profile m i) (fun e => P.cost _ (i e).2.property) col v) _
    _ ≤ _ := by
      have ht := Nat.le_mul_of_pos_left n P.pos
      rw [mul_assoc 8, mul_assoc 10]
      omega
  let f (p : G.V × Cell h) := g.route m col p.1 p.2
  have hn : (n : ℝ) * (P.b * z : ℕ) ≤ (near G.C Δ v).card * ((2 : ℝ) ^ k * B) := by
    refine le_trans ?_ (g.route_load m G.cs G.sub G.edge G.load_nonneg hB col v)
    change degree (fun e => Prod.map f f (G.pair e)) v * ((P.b * z : ℕ) : ℝ) ≤ _
    rw [degree_map, Nat.cast_sum, sum_mul]
    apply sum_le_sum
    intro p _
    by_cases he : g.route m col p.1 p.2 = v
    · simp only [f, ite_eq_left he]
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load _ _)
    · simp [f, he]
  calc
    _ ≤ ((10 * P.b * n : ℕ) : ℝ) * z :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) (Nat.cast_nonneg _)
    _ = 10 * ((n : ℝ) * (P.b * z : ℕ)) := by push_cast; ring
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hn (by norm_num)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround
end

/-!
# Packing the active factors of a contracted station

Each argument names a whole visible or hidden span. Empty and
unused arguments need no pointer. The arbitrary enumerations of
atoms and hidden spans do not affect the decoded value.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History
open Coloring Packing
open scoped Classical

theorem menu_read {F L : Type} [Field F] {s l d : ℕ} (a : L → Atom F)
    (names : L ↪ B l) (index : ∀ i, (a i).Span ↪ B s) (len : B d → ℕ)
    (i : L) (x : Positions ((menu a names index len).width (names i)) → Bool) :
    (menu a names index len).value (names i) x = (a i).weight
      (fun j t => x ⟨index i j, t.cast (menu_width a names index len i j).symm⟩) := by
  let u j k := if h : k < (menu a names index len).width (names i) j then x ⟨j, ⟨k, h⟩⟩ else false
  have h := menu_value a names index len i u
  have he : (fun j => u j.1 j.2.val) = x := by
    funext j
    simp [u, j.2.isLt]
  rw [he] at h
  refine h.trans (congrArg _ (funext fun j => funext fun t => ?_))
  have hu : t.val < (menu a names index len).width (names i) (index i j) := by
    rw [menu_width]
    exact t.isLt
  exact dite_eq_left hu

namespace Subround

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z : ℕ}
  (P : Gadget F) (G : HostNet F L h (P.b * z))
  {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r G.diagram) (hz : 0 < z)
  (v : Site G.V h)

abbrev Receipt := ↥(G.receipts g m (g.layout m P i) v)

structure Bundle (c : ℕ) where
  label : Receipt P G g m i v → Kind S P c
  arg (t : Receipt P G g m i v) :
    AtomMap g m P G.units hz i p v (kind S P z hz (label t)) t.val

variable {P G g m i p hz v}
local notation "J" => Receipt P G g m i v
local notation "H" => Hidden g m P i v
local notation "V" => Visible g m P G.units i p v
local notation "W" => PortMap.Port g m P G.units i p v
local notation "Q" => cluster g m P G.units hz i

theorem anchor_eq (t : G.Atom g m) : G.anchor g m (g.layout m P i) t = (Q).owner t := by
  rcases t with a | (b | c) <;> rfl

def includeAtom (hz : 0 < z) : J ↪ {u // (cluster g m P G.units hz i).owner u = v} where
  toFun t := ⟨t.val, (anchor_eq _).symm.trans (Finset.mem_filter.mp t.2).2.2⟩
  inj' _ _ h := Subtype.ext (Subtype.mk.inj h)

theorem idle_atoms
    (neutral : ∀ u, G.diagram.arity u = 0 → ∀ x, Transcript.sample (G.diagram.table u) x = 1)
    (t : {u // (Q).owner u = v}) (ht : t ∉ Set.range (includeAtom hz)) (w : Bit Q → Bool) :
    factor Q t.val w = 1 := by
  have hn : ¬ G.live g m t.val := by
    intro h
    have he : t.val ∈ G.receipts g m (g.layout m P i) v :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, (anchor_eq _).trans t.property⟩
    exact ht ⟨⟨_, he⟩, rfl⟩
  rcases t with ⟨u | (e | r), _⟩
  · rw [old_factor]
    exact neutral u (Nat.eq_zero_of_not_pos hn) _
  · exact (hn trivial).elim
  · exact unpaired_idle g m P G.units hz i w r (fun e h => hn ⟨e, .inl h⟩) (fun e h => hn ⟨e, .inr h⟩)

namespace Bundle
variable {c e l s d : ℕ} (b : Bundle P G g m i p hz v c)
  (names : Kind S P c ↪ B l) (index : ∀ a : Kind S P c, (kind S P z hz a).Span ↪ B s)
  (seat : Visible g m P G.units i p v ↪ B e) (size : Hidden g m P i v → B d)

def ptr (t : J) : B s → B e ⊕ H :=
  Function.extend (index (b.label t))
    (fun j => if h : 0 < (kind S P z hz (b.label t)).width j then
      ((b.arg t).slot j h).map seat id else .inl 0) (fun _ => .inl 0)

def packed : Packed J H e l s d where
  tag t := names (b.label t)
  width := size
  ptr t j := (b.ptr index seat t j, 0)

theorem ptr_at (t : J) (j : (kind S P z hz (b.label t)).Span) (h : 0 < (kind S P z hz (b.label t)).width j) :
    b.ptr index seat t (index (b.label t) j) = ((b.arg t).slot j h).map seat id := by
  rw [ptr, (index _).injective.extend_apply, dite_eq_left h]

variable (len : B d → ℕ) (w : B e → ℕ) (h₀ : len 0 = 0)
    (hi : ∀ q : Hidden g m P i v, len (size q) = segmentWidth g m P i z q.val)
    (ho : ∀ q : Visible g m P G.units i p v, w (seat q) = visibleWidth g m P i p z q.val)
local notation "pack" => b.packed names index seat size
local notation "M" => menu (kind S P z hz) names index len

include hi ho in
theorem capacity (q : W) :
    (pack).cap M w (q.map seat id, 0) = PortMap.width g m P G.units i p v q := by
  cases q with
  | inl q => exact ho q
  | inr q => exact hi q

include h₀ hi ho in
theorem fits : (pack).Fits M w := by
  intro t j a
  have ha := a.isLt
  change a.val < (M).width (names (b.label t)) j at ha
  have hj : j ∈ Set.range (index (b.label t)) := by
    by_contra h
    have h' := menu_empty (kind S P z hz) names index len (b.label t) j h
    omega
  obtain ⟨q, rfl⟩ := hj
  have hq := menu_width (kind S P z hz) names index len (b.label t) q
  have hp : 0 < (kind S P z hz (b.label t)).width q := by omega
  change len 0 + a.val < (pack).cap M w (b.ptr index seat t _, 0)
  rw [h₀, zero_add, ptr_at _ _ _ _ _ hp, capacity _ _ _ _ _ _ _ hi ho, (b.arg t).size]
  exact ha.trans_eq hq

end Bundle
end Subround
end OAI.LinearAlgebra.MatrixExponent.Assembly.History
end

/-!
# Accounting for old histories

There is at most one old station at an occurrence. Each next
contraction receives a disjoint set of the old labels, even if
many of its local pointers refer to the same label.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
open Finset
open scoped Classical

variable {T F : Type} [Fintype T] {x y : Wire} {L : Fringe x y T} {h u : ℕ}
  (G : HostNet F L h u) {Δ D k : ℕ} {B : ℝ} (g : Grouping G.N G.C Δ D k B G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix)
  (col : Bool) (w : Site G.V h)

theorem receipts_live (a : G.Atom g m) (h : a ∈ G.receipts g m col w) : G.live g m a :=
  (mem_filter.mp h).2.1

def previous (cost : G.V × Cell h → ℝ) : G.Atom g m → ℝ :=
  Sum.elim (cost ∘ G.units.place) (fun _ => 0)

theorem carried_size (one : Function.Injective G.units.place)
    (cost : G.V × Cell h → ℝ) (hc : ∀ t, 0 ≤ cost t)
    (sizes : ↥(G.receipts g m col w) → ℕ)
    (hsizes : ∀ i : ↥(G.receipts g m col w), (sizes i : ℝ) ≤ G.previous g m cost i) :
    (∑ i, sizes i : ℕ) ≤ push (fun t => g.route m col t.1 t.2) cost w := by
  let f (t : G.V × Cell h) := if g.route m col t.1 t.2 = w then cost t else 0
  have hf (t) : 0 ≤ f t := by unfold f; split <;> first | exact hc t | exact le_rfl
  have he (i : ↥(G.receipts g m col w)) : G.previous g m cost i = G.previous g m f i := by
    obtain ⟨a, h⟩ := i
    have hw := (mem_filter.mp h).2.2
    cases a with
    | inl v =>
      change cost _ = if _ then cost _ else 0
      exact (ite_eq_left hw).symm
    | inr q => rfl
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i : ↥(G.receipts g m col w), G.previous g m f i :=
      sum_le_sum fun i _ => (hsizes i).trans_eq (he i)
    _ ≤ ∑ i, G.previous g m f i := by
      rw [sum_coe_sort]
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      rintro (v|j) _ _
      · exact hf _
      · exact le_rfl
    _ = ∑ i, f (G.units.place i) := by
      rw [Fintype.sum_sum_type]
      simp only [previous, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, sum_const_zero, add_zero]
    _ ≤ _ := by
      let e : G.diagram.V ↪ G.V × Cell h := ⟨_, one⟩
      have hh : push (fun t => g.route m col t.1 t.2) cost w = ∑ t, f t := by
        apply sum_congr rfl
        intro i _
        unfold f; congr
      rw [hh]
      change (∑ i, f (e i)) ≤ ∑ t, f t
      rw [← sum_map univ e]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hf i)

end OAI.LinearAlgebra.MatrixExponent.Packing.HostNet
end

/-! # Correctness of the packed local history -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Bundle
open Coloring Packing
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z : ℕ}
  {P : Gadget F} {G : HostNet F L h (P.b * z)}
  {Δ D k : ℕ} {B' : ℝ} {g : Grouping G.N G.C Δ D k B' G.load}
  {m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix} {i : g.Choice m P}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r G.diagram} {hz : 0 < z}
  {v : Site G.V h}
  {c e l s d : ℕ} (b : Bundle P G g m i p hz v c)
  (names : Kind S P c ↪ B l) (index : ∀ a : Kind S P c, (kind S P z hz a).Span ↪ B s)
  (seat : Visible g m P G.units i p v ↪ B e) (size : Hidden g m P i v → B d)
  (len : B d → ℕ) (w : B e → ℕ) (h₀ : len 0 = 0)
  (hi : ∀ q : Hidden g m P i v, len (size q) = segmentWidth g m P i z q.val)
  (ho : ∀ q : Visible g m P G.units i p v, w (seat q) = visibleWidth g m P i p z q.val)
  (p' : (g.contract m P G.units hz i).Port v ≃ Positions w)
  (hp : ∀ j : Visible g m P G.units i p v, ∀ t : Fin (visibleWidth g m P i p z j.val),
    p' (visibleBits g m P G.units hz i p v ⟨j, t⟩) = ⟨seat j, t.cast (ho j).symm⟩)

local notation "pack" => b.packed names index seat size
local notation "M" => menu (kind S P z hz) names index len
local notation "Q" => cluster g m P G.units hz i

local notation "N" => g.contract m P G.units hz i

private def inner : (pack).Inner M ≃ (Q).hidden v :=
  (Equiv.sigmaCongrRight (fun j => finCongr (hi j))).trans (hiddenBits g m P G.units hz i v)

include hp in
private theorem resolve (q : PortMap.Port g m P G.units i p v)
    (t : Fin (PortMap.width g m P G.units i p v q))
    (r : (B e ⊕ Hidden g m P i v) × B d) (he : r = (q.map seat id, 0))
    (a : Fin ((pack).cap M w r)) (ha : a.val = t.val) :
    Sum.map (fun u => named N v (p'.symm u))
      (fun j => (⟨v, b.inner names index seat size len hi j⟩ : Σ u, (Q).hidden u)) ((pack).resolve M w r a) =
        PortMap.bit g m P G.units i p v hz q t := by
  subst r
  cases q with
  | inl q =>
    have e : p' (visibleBits g m P G.units hz i p v ⟨q, t⟩) = ⟨seat q, a⟩ :=
      (hp q t).trans (congrArg (fun s : Fin (w (seat q)) => (⟨seat q, s⟩ : Positions w)) (Fin.ext ha.symm))
    change Sum.inl (named _ _ (p'.symm ⟨seat q, a⟩)) = _
    rw [← e, Equiv.symm_apply_apply, visible_pin]
    rfl
  | inr q =>
    have eq : (finCongr (hi q)) a = t := Fin.ext ha
    change Sum.inr (⟨v, hiddenBits g m P G.units hz i v ⟨q, (finCongr (hi q)) a⟩⟩ : Σ u, (Q).hidden u) = _
    rw [eq]
    rfl

variable (neutral : ∀ u, G.diagram.arity u = 0 → ∀ x, Transcript.sample (G.diagram.table u) x = 1)

include hp h₀ hi ho neutral in
theorem decode {t : ℕ} (atoms : Receipt P G g m i v ↪ B t) (hidden : Hidden g m P i v ↪ B e)
    (x : Positions w → Bool) :
    (M).decode w ((pack).encode atoms hidden) x =
      Transcript.sample ((g.contract m P G.units hz i).table v) (x ∘ p') := by
  have ht := b.fits names index seat size len w h₀ hi ho
  rw [Packed.decode _ _ _ _ _ h₀ ht]
  let _ : Fintype ((before g m P G.units hz i).Between (Sum.elim (g.assign m P G.units i) (g.locate m (g.layout m P i)))) := (N).fe
  refine Traces.correct (C := Q) (out := p') ?_ x
  refine ⟨includeAtom hz, b.inner names index seat size len hi, ?_, fun t ht w => idle_atoms neutral t ht w⟩
  intro j y
  let Y := (pack).history M w ht
  let e := b.inner names index seat size len hi
  let k := y ∘ embed Q Y v p' e ∘ Y.read j
  change (M).value (names (b.label j)) k = _
  refine (menu_read (kind S P z hz) names index len (b.label j) k).trans ?_
  refine Eq.trans ?_ ((b.arg j).value y)
  refine congrArg _ (funext fun u => funext fun t => ?_)
  let q := (b.arg j).slot u (Nat.zero_lt_of_lt t.isLt)
  let a := index (b.label j) u
  let r := (pack).ptr j a
  have hr : r = (q.map seat id, 0) := by
    change (b.ptr index seat j a, 0) = _
    rw [show a = index (b.label j) u from rfl, b.ptr_at index seat j u (Nat.zero_lt_of_lt t.isLt)]
  let t' : Fin ((M).width (names (b.label j)) a) :=
    t.cast (menu_width _ names index len _ u).symm
  let n : Fin ((pack).cap M w r) := ⟨_, ht j a t'⟩
  have hn : n.val = t.val := by change len 0 + t.val = _; rw [h₀, zero_add]
  exact congrArg y (b.resolve names index seat size len w hi ho p' hp q
    (t.cast ((b.arg j).size u _).symm) r hr n hn)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Subround.Bundle
end

/-!
# Compact local numbering for contraction histories

Rank each key within the finite set of keys actually present, using the
fixed order of their encodings. Only the resulting rank is stored. Neither
the enumeration of the objects nor the proof of the size bound affects it.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing HostNet History.Subround Finset
open scoped Classical

variable {A A' K : Type} [Fintype A] [Fintype A'] [Encodable K] {H : ℕ}

def index (s : Finset K) (x : K) : ℕ :=
  (s.filter fun y => Encodable.encode y < Encodable.encode x).card

private theorem index_lt (s : Finset K) (x : K) (hx : x ∈ s) : index s x < s.card := by
  apply card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _, fun he => by
    have := congrArg (x ∈ ·) he
    simp [hx] at this⟩

private theorem index_strict (s : Finset K) (x y : K) (hx : x ∈ s)
    (he : Encodable.encode x < Encodable.encode y) : index s x < index s y := by
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    obtain ⟨hi, h⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi, h.trans he⟩
  · intro h
    have hh := congrArg (x ∈ ·) h
    simp [hx, he] at hh

def compact (key : A ↪ K) (bound : Fintype.card A ≤ 2 ^ H) : A ↪ B H where
  toFun x := ⟨index (univ.map key) (key x),
    (index_lt _ _ (mem_map_of_mem key (mem_univ x))).trans_le (by simpa using bound)⟩
  inj' x y he := by
    have h := congrArg Fin.val he
    rcases lt_trichotomy (Encodable.encode (key x)) (Encodable.encode (key y)) with hr | hr | hr
    · exact ((index_strict _ _ _ (mem_map_of_mem key (mem_univ x)) hr).ne h).elim
    · exact key.injective (Encodable.encode_injective hr)
    · exact ((index_strict _ _ _ (mem_map_of_mem key (mem_univ y)) hr).ne h.symm).elim

theorem compact_eq {f : A ↪ K} {g : A' ↪ K}
    {hf : Fintype.card A ≤ 2 ^ H} {hg : Fintype.card A' ≤ 2 ^ H}
    (hs : univ.map f = univ.map g) {x : A} {y : A'} (he : f x = g y) :
    compact f hf x = compact g hg y := by
  apply Fin.ext
  exact congrArg₂ index hs he

theorem compact_relabel (e : A ≃ A') {f : A ↪ K} {g : A' ↪ K}
    {hf : Fintype.card A ≤ 2 ^ H} {hg : Fintype.card A' ≤ 2 ^ H}
    (he : ∀ x, f x = g (e x)) (x : A) :
    compact f hf x = compact g hg (e x) := by
  refine compact_eq ?_ (he x)
  ext q
  simp only [mem_map, mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨e i, (he i).symm.trans hi⟩,
    fun ⟨i, hi⟩ => ⟨e.symm i, by rw [he, e.apply_symm_apply, hi]⟩⟩

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h z d w : ℕ}

structure Budget (P : Gadget F) (G : HostNet F L h (P.b * z)) (Δ k : ℕ) (B' : ℝ) (H : ℕ) : Prop where
  pos : 0 < z
  nonneg : 0 ≤ B'
  core : 0 < Δ
  deg : ∀ v, (G.C v).card ≤ Δ
  bound : (10 : ℝ) * (4 * Δ) ^ 300 * 2 ^ k * B' ≤ 2 ^ H * z

variable {P : Gadget F} {G : HostNet F L h (P.b * z)} {Δ D k : ℕ} {B' : ℝ}

omit [Fintype T] in
private theorem Budget.fit (b : Budget P G Δ k B' H) (v : Site G.V h) (n : ℕ) {c : ℝ}
    (hc : c ≤ 10) (hn : n * (z : ℝ) ≤ c * (near G.C Δ v).card * ((2 : ℝ) ^ k * B')) : n ≤ 2 ^ H := by
  have ha : ((near G.C Δ v).card : ℝ) ≤ (4 * Δ) ^ 300 := by
    exact_mod_cast near_card G.C Δ b.core b.deg v
  have hs : n * (z : ℝ) ≤ 2 ^ H * z := calc
    _ ≤ _ := hn
    _ ≤ 10 * (4 * Δ) ^ 300 * ((2 : ℝ) ^ k * B') := mul_le_mul_of_nonneg_right
      (mul_le_mul hc ha (Nat.cast_nonneg _) (by norm_num)) (mul_nonneg (by positivity) b.nonneg)
    _ ≤ _ := by simpa only [mul_assoc] using b.bound
  exact_mod_cast le_of_mul_le_mul_right hs (Nat.cast_pos.mpr b.pos)

variable (q : Navigation G d w) (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (i : g.Choice m P)

def atoms (b : Budget P G Δ k B' H) (contacts : ∀ t, P.b * z ≤ G.tetherLoad (G.far t))
    (v : Site G.V h) : ↥(G.receipts g m (g.layout m P i) v) ↪ B H :=
  compact (q.atomNames g m (g.layout m P i) v) (by
    rw [Fintype.card_coe]
    refine b.fit v _ (by norm_num : (8 : ℝ) ≤ 10) (le_trans ?_
      (G.receipts_bound g m contacts q.one b.nonneg (g.layout m P i) v))
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.le_mul_of_pos_left _ P.pos))
      (Nat.cast_nonneg _))

def hidden (b : Budget P G Δ k B' H) (v : Site G.V h) : Hidden g m P i v ↪ B H :=
  compact (q.hiddenNames g m P i v) (b.fit v _ le_rfl (hidden_bound P G g m i v b.nonneg))

variable {S : Scheme F} {r : S.format.obj}

def visible (q : Navigation G d S.e) (p : S.Presentation r G.diagram)
    (b : Budget P G Δ k B' H) (floor : ∀ t, z ≤ p.borderWidth t)
    (v : Site G.V h) : Visible g m P G.units i p v ↪ B H :=
  compact (visibleNames P G g m i p v q)
    (b.fit v _ (by norm_num : (9 : ℝ) ≤ 10) (visible_bound P G g m i p v b.pos b.nonneg floor))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
end

/-! # Span links at a live station of the previous presentation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
open Coloring Packing History History.Subround
open scoped Classical

variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T}
  {h z : ℕ} {P : Gadget F} {S : Scheme F} {r : S.format.obj}
  {G : HostNet F L h (P.b * z)} (p : S.Posting r G)
  (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)
  (m : Matching (g.ends (G.regroup a ha).src (G.regroup a ha).ix)
    (g.ends (G.regroup a ha).dst (G.regroup a ha).ix) (G.regroup a ha).ix)
  (i : g.Choice m P) (v : Site (G.V × Cell a) (h - a)) (w : G.diagram.V)
  (hw : g.assign m P (G.regroup a ha).units i w = v)

local notation "H" => G.regroup a ha
local notation "V" => PortMap.Port g m P (HostNet.units H) i p.toPresentation v
local notation "W" => PortMap.width g m P (HostNet.units H) i p.toPresentation v

omit [Fintype T] in
private theorem span_end (j : S.Span) (hj : 0 < S.width r j) (hp : S.peer r j ≠ none) :
    ∃ e t, p.span e t = j := by
  obtain ⟨q, hq⟩ := p.toSeating.ends.surjective ⟨j, ⟨0, hj⟩⟩
  have he : (p.toSeating.ends q).1 = j := congrArg Sigma.fst hq
  rcases q with (t|e)|(t|e)
  · exact (hp (he ▸ p.input t)).elim
  · obtain ⟨⟨e, n⟩, rfl⟩ := G.units.bits.symm.surjective e
    exact ⟨e, false, (p.ordered e false n).1.symm.trans he⟩
  · exact (hp (he ▸ p.output t)).elim
  · obtain ⟨⟨e, n⟩, rfl⟩ := G.units.bits.symm.surjective e
    exact ⟨e, true, (p.ordered e true n).1.symm.trans he⟩

omit [Fintype T] in
theorem station_place {j : B S.e} {e : G.E} {t : Bool} (he : p.span e t = (p.vertex w, j)) :
    (H).units.place w = (side H e t, (H).ix e) := by
  rw [p.vertex_eq] at he
  have h₁ := p.host.injective (congrArg (fun i : S.Span => i.1.1) he)
  have h₂ := p.block.injective (congrArg (fun i : S.Span => i.1.2.1) he)
  have h : G.units.place w = (side G e t, G.ix e) := Prod.ext h₁.symm h₂.symm
  change splitAddr G.V a ha (G.units.place w) = _
  rw [h]
  cases t <;> rfl

include hw in
private theorem station_location {j : B S.e} {e : G.E} {t : Bool} (he : p.span e t = (p.vertex w, j)) :
    g.route m (g.layout m P i) (side H e t) ((H).ix e) = v := by
  unfold Grouping.assign at hw
  rw [p.station_place a ha w he] at hw
  exact hw

variable (j : B S.e) (hj : 0 < S.width r (p.vertex w, j))

inductive Origin : V → Prop
  | outside (q : p.toPresentation.BorderSpan) (hq : q.val = (w, j)) (he) :
    Origin (PortMap.exterior g m P (H).units i p.toPresentation v q he)
  | inside (e : G.E) (t : Bool) (he : p.span e t = (p.vertex w, j)) (hs) :
    Origin (PortMap.demand g m P (H).units i p.toPresentation v e t hs)

include hw hj in
private theorem exists_origin : ∃ q, p.Origin a ha g m i v w j q := by
  by_cases h : S.peer r (p.vertex w, j) = none
  · exact ⟨_, .outside ⟨(w, j), hj, h⟩ rfl hw⟩
  · obtain ⟨e, t, he⟩ := p.span_end _ hj h
    exact ⟨_, .inside e t he (p.station_location a ha g m i v w hw he)⟩

def stationPort : V := (p.exists_origin a ha g m i v w hw j hj).choose

theorem station_origin : p.Origin a ha g m i v w j (p.stationPort a ha g m i v w hw j hj) :=
  (p.exists_origin a ha g m i v w hw j hj).choose_spec

theorem origin_width {s : V} (hs : p.Origin a ha g m i v w j s) :
    W s = S.width r (p.vertex w, j) := by
  cases hs with
  | outside q hq he =>
    erw [PortMap.width_exterior g m P (H).units i p.toPresentation v q he, Presentation.borderWidth, hq]
    rfl
  | inside e t he hs =>
    erw [PortMap.width_demand g m P (H).units i p.toPresentation v e t hs, ← he]
    exact (p.length e t).symm

variable (hz : 0 < z)

theorem origin_address {s : V} (hs : p.Origin a ha g m i v w j s)
    (b : Fin (S.width r (p.vertex w, j))) :
    address (cluster g m P (H).units hz i) (old g m P (H).units hz i
      (p.toSeating.ends.symm ⟨(p.vertex w, j), b⟩)) =
      PortMap.bit g m P (H).units i p.toPresentation v hz s
        (b.cast (p.origin_width a ha g m i v w j hs).symm) := by
  cases hs with
  | outside q hq he =>
    rcases q with ⟨⟨u, l⟩, h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
    let q : p.toPresentation.BorderSpan := ⟨(u, l), h⟩
    have eq := p.toPresentation.border_pin (⟨q, b⟩ : p.toPresentation.BorderBit)
    have hh : p.toSeating.ends.symm ⟨(p.vertex u, l), b⟩ =
        boundaryEnd _ (p.toPresentation.exteriorBits ⟨q, b⟩) := p.toSeating.ends.symm_apply_eq.mpr eq.symm
    rw [hh]
    exact PortMap.address_exterior g m P (H).units i p.toPresentation v hz q he b
  | inside e t he hm =>
    let c := b.cast ((congrArg (S.width r) he.symm).trans (p.length e t))
    have hh : p.toSeating.ends (endBit G e t c) = ⟨(p.vertex w, j), b⟩ := by
      have he' := (p.ordered e t c).1.trans he
      exact Sigma.ext he' ((Fin.heq_ext_iff (congrArg (S.width r) he')).mpr (p.ordered e t c).2)
    rw [p.toSeating.ends.symm_apply_eq.mpr hh.symm]
    exact PortMap.address_demand_old g m P (H).units i p.toPresentation v hz e t hm c

abbrev oldLabel := ((r (p.vertex w).1).2 (p.vertex w).2.1, (p.vertex w).2.2)

def oldMap : AtomMap g m P (H).units hz i p.toPresentation v (History.original S (p.oldLabel w)) (.inl w) where
  slot j h := p.stationPort a ha g m i v w hw j h
  size j h := p.origin_width a ha g m i v w j (p.station_origin a ha g m i v w hw j h)
  value b := by
    erw [old_factor g m P (H).units hz i b w]
    change S.table r (p.vertex w) (fun u => b (PortMap.bit g m P (H).units i p.toPresentation v hz
      (p.stationPort a ha g m i v w hw u.1 u.2.pos) (u.2.cast
        (p.origin_width a ha g m i v w u.1 (p.station_origin a ha g m i v w hw u.1 u.2.pos)).symm))) = _
    rw [p.sample]
    apply congrArg
    funext k
    let u := p.pin w k
    have ht := p.origin_address a ha g m i v w u.1 hz (p.station_origin a ha g m i v w hw u.1 u.2.pos) u.2
    have he : p.toSeating.ends.symm ⟨(p.vertex w, u.1), u.2⟩ = named G.diagram w k :=
      p.toSeating.ends.symm_apply_eq.mpr (p.toSeating.ends_at w k).symm
    rw [he] at ht
    exact congrArg b ht.symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Posting
end

/-! # A two-hop bound on the sources of all receipts at a site -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
open Coloring Packing Finset
open scoped Classical

variable {T F : Type} {x y : Wire} {L : Fringe x y T} {h u d w : ℕ}
  {G : HostNet F L h u} (p : Navigation G d w)

def neighborhood (root : G.V) :=
  univ.image fun i : Option (B d) × Option (B d) => p.recover (p.recover root i.1) i.2

theorem neighborhood_card (v : G.V) : (p.neighborhood v).card ≤ (2 ^ d + 1) ^ 2 := by
  unfold neighborhood
  exact card_image_le.trans_eq (by simp [pow_two])

variable [Fintype T] {Δ D k : ℕ} {B' : ℝ} (g : Grouping G.N G.C Δ D k B' G.load)
  (m : Matching (g.ends G.src G.ix) (g.ends G.dst G.ix) G.ix) (col : Bool)

private theorem reachable (v : G.V) (b : Cell h) (j : Option (B d)) :
    p.recover v j ∈ p.neighborhood (g.route m col v b).1 := by
  let z := (g.route m col v b).1
  refine mem_image.mpr ⟨(p.reverse z v, j), mem_univ _, ?_⟩
  exact congrArg (fun u => p.recover u j) (p.recover_reverse g m col v b)

theorem window_move (v : G.V) (b : Cell h) :
    v ∈ p.neighborhood (g.route m col v b).1 :=
  p.reachable g m col v b none

theorem window_end (i : G.E) (b : Bool) :
    G.src i ∈ p.neighborhood (g.route m col (Scheme.side G i b) (G.ix i)).1 := by
  cases b
  · exact p.window_move g m col _ _
  · rw [← p.back i]
    exact p.reachable g m col (G.dst i) (G.ix i) (some _)

theorem window_party (i : m.items) (j : Fin 6) :
    G.src i.val ∈ p.neighborhood (g.party m col i j).1 := by
  let e := G.via g m col j i
  let b := (HostNet.roleCode col j).2
  have hs : G.src e = G.src i.val := by
    have he : G.src (m.mate i) = G.src i.val := congrArg Sigma.fst (m.spec i).2.1
    unfold e HostNet.via Matching.pairEdge
    change G.src (if (HostNet.roleCode col j).1 = 0 then m.mate i else i.val) = _
    split_ifs <;> first | exact he | rfl
  have he : g.rep m col i j = (Scheme.side G e b, G.ix e) := by
    rw [G.role]
    dsimp only [b, e]
    cases (HostNet.roleCode col j).2 <;> rfl
  rw [Grouping.party, he, ←hs]
  exact p.window_end g m col e b

variable [Field F] (P : Gadget F) (i : g.Choice m P)

def issuer : g.Supply m P i → G.V
  | .inl e => G.src e.1.val
  | .inr e => G.src e.1.val

theorem window_supply (e : g.Supply m P i) (b : Bool) :
    issuer g m P i e ∈ p.neighborhood
      (cond b (g.contact m col e).2 (g.contact m col e).1).1 := by
  rcases e with ⟨e, j, t⟩|⟨e, t⟩
  · cases b <;> exact p.window_party g m col e _
  · cases b
    · exact p.window_end g m col e.val false
    · exact p.window_end g m col e.val true

end OAI.LinearAlgebra.MatrixExponent.Assembly.Navigation
end
