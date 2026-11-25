import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Spans
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.ChildPaths

/-! # Grouping a board using only the transmitted loads -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
open Coloring Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
  {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} (p : D.Presents r P)
  {g H T a : ℕ} {L θ : ℝ} (ha : a < D.scheme.h)

local notation "n" => D.scheme.h - a
local notation "cost" => ((H : ℝ) * T / 2)

theorem group_load (v : P.V) (i : Cell a) (j : Cell n) :
    D.load (D.counter r (p.host v) (D.position a ha.le (cellIndex a i) (cellIndex n j))) =
      P.groupLoad a ha.le (v, i) j := by
  let q := (splitCell a ha.le).symm (i, j)
  have he : splitAddr P.V a ha.le (v, q) = ((v, i), j) := by simp [splitAddr, q]
  rw [show D.position a ha.le _ _ = cellIndex _ q by simp [position, q], p.load]
  unfold Rounds.Board.groupLoad push
  simp only [Function.comp_apply, ← he, (splitAddr P.V a ha.le).injective.eq_iff]
  congr! 3

structure Plan (g H T : ℕ) where
  group : P.Plan a ha.le g H T
  tag : ∀ v i, D.intervals a ha.le 1 ((H : ℝ) * T / 2) g g r (Group.embed p.host a v) (cellIndex n i) =
    intervalCode n (group.here v i).2

theorem plan (hg : 0 < g) (hH : 0 < H) (hT : 0 < T) (ok : P.Ready g H T L θ) :
    Nonempty (p.Plan ha g H T) := by
  have h : Group.Presents (D.groups a ha.le r) p.host P.adj P.adj
      (Packing.relative 1 cost (P.groupLoad a ha.le)) (D.relative 1 cost) :=
    ⟨p.live, p.closed, p.edge, p.core, fun v i j =>
      congrArg (· / ((2 : ℝ) ^ 1 * cost)) (p.group_load ha v i j)⟩
  obtain ⟨G, hG⟩ := h.grouping hg hg le_rfl (by omega) (by positivity)
    P.sym P.sym (fun _ => Finset.Subset.rfl) ok.1 ok.1 (P.groupBound ha.le ok)
  exact ⟨⟨G, hG⟩⟩

namespace Plan
variable {p ha} (G : p.Plan ha g H T)

def occurrence (i : P.diagram.V) := splitAddr P.V a ha.le (P.place i)
def col (i : P.diagram.V) := G.group.loc (occurrence (ha := ha) i).1 (occurrence (ha := ha) i).2
def row (i : P.diagram.V) := cellIndex n (occurrence (ha := ha) i).2

local notation "suffixOf" => (row (P := P) (ha := ha))

theorem one : Function.Injective (fun i => (G.col i, suffixOf i)) := by
  intro i j he
  apply P.one
  apply (splitAddr P.V a ha.le).injective
  exact Prod.ext (congrArg (fun x => x.1.1) he) ((cellIndex n).injective (congrArg Prod.snd he))

variable (hg : 0 < g) (hH : 0 < H) (hT : 0 < T) (ok : P.Ready g H T L θ)
  (hs : (P.seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ (D.scheme.h - a))

abbrev cells := P.withCells hg hH hT ha ok hs G.group
abbrev bin := (G.cells hg hH hT ok hs).bin suffixOf hH

variable {R : ℕ} (hd : (4 * g) ^ 300 < H) (hR : 0 < R) (hRT : R * H ^ 2 ≤ T)
  (hx : ((wd x + wd y : ℕ) : ℝ) * H ≤ L)

abbrev input := (G.cells hg hH hT ok hs).input hd hR hRT
  ((Finset.sum_nonneg fun v _ => P.charge_nonneg v).trans ok.2.1) hx (G.bin hg hH hT ok hs)
  ((G.cells hg hH hT ok hs).bin_sq suffixOf hH G.one ok.2.1 ok.2.2.1)

end Plan
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
end

/-! # Suffix rows as read from the grouping controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
open Coloring Packing Rounds Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
  {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
  {g H T a : ℕ} {L θ : ℝ} {ha : a < D.scheme.h} (G : p.Plan ha g H T)

local notation "n" => D.scheme.h - a
local notation "suffixOf" => (row (P := P) (ha := ha))
local notation "Col" => G.group.Colony

abbrev weight (c : Col) (j : B n) := push (fun v => (G.col v, suffixOf v)) P.charge (c, j)

theorem weight_at (v : P.diagram.V) : G.weight (G.col v) (suffixOf v) = P.charge v := by
  simp only [weight, push, G.one.eq_iff, sum_ite_eq', mem_univ, ite_true]

theorem weight_pos {c : Col} {j : B n} (h : 0 < G.weight c j) :
    ∃ i : P.diagram.V, G.col i = c ∧ suffixOf i = j ∧ 0 < P.charge i := by
  by_contra! hn
  refine h.not_ge (sum_nonpos fun i _ => ?_)
  split_ifs with hi
  · exact hn i (Prod.mk.inj hi).1 (Prod.mk.inj hi).2
  · rfl

theorem weight_eq (c : Col) (j : Cell n) :
    G.weight c (cellIndex n j) = if G.group.loc c.1 j = c then P.groupLoad a ha.le c.1 j else 0 := by
  have test (i : P.diagram.V) : (G.col i, suffixOf i) = (c, cellIndex n j) ↔
      G.group.loc c.1 j = c ∧ occurrence (ha := ha) i = (c.1, j) := by
    constructor
    · intro h
      have he := Prod.mk.inj h
      have eq : occurrence (ha := ha) i = (c.1, j) :=
        Prod.ext (congrArg Sigma.fst he.1) ((cellIndex n).injective he.2)
      exact ⟨by simpa only [col, eq] using he.1, eq⟩
    · rintro ⟨h, he⟩
      simp only [col, row, he, h]
  unfold weight push
  simp only [test, ite_and, sum_ite_irrel, sum_const_zero]
  split_ifs
  · apply sum_congr rfl
    intro i _
    unfold occurrence
    by_cases h : splitAddr P.V a ha.le (P.place i) = (c.1, j)
    · exact (ite_eq_left h).trans (ite_eq_left h).symm
    · exact (ite_eq_right h).trans (ite_eq_right h).symm
  · rfl

def interval (c : Col) := intervalCode n (G.group.site c).2
def labels (v : B D.scheme.m) (i : B a) :=
  D.intervals a ha.le 1 ((H : ℝ) * T / 2) g g r ((Match.rowIndex _ _).symm (v, i))

def profile (v : B D.scheme.m) (i : B a) (k : B (n + 1)) (j : B n) :=
  if labels (D := D) (r := r) (ha := ha) (H := H) (T := T) (g := g) v i j = k
  then D.load (D.counter r v (D.position a ha.le i j)) else 0

theorem profile_eq (c : Col) :
    profile (D := D) (r := r) (ha := ha) (H := H) (T := T) (g := g)
      (p.host c.1.1) (cellIndex _ c.1.2) (G.interval c) = G.weight c := by
  funext j
  obtain ⟨j, rfl⟩ := (cellIndex n).surjective j
  rw [weight_eq, profile, p.group_load ha]
  have ht := G.tag c.1 j
  change labels (D := D) (r := r) (ha := ha) (H := H) (T := T) (g := g)
    (p.host c.1.1) (cellIndex _ c.1.2) (cellIndex n j) = _ at ht
  rw [ht]
  have eq : intervalCode n (G.group.here c.1 j).2 = G.interval c ↔ G.group.loc c.1 j = c :=
    ⟨fun h => G.group.site_injective (Prod.ext rfl ((intervalCode n).injective h)),
      fun h => congrArg G.interval h⟩
  simp only [eq]

def active {q : ℕ} (f : B q → ℝ) := univ.filter (fun j => 0 < f j)

theorem active_card (hg : 0 < g) (hH : 0 < H) (hT : 0 < T) (ok : P.Ready g H T L θ)
    (hs : (P.seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ n) (hθ : 0 < θ) (c : Col) :
    (active (G.weight c)).card ≤ ⌈(H : ℝ) / θ⌉₊ := by
  let s := active (G.weight c)
  have low j (hj : j ∈ s) : θ * T ≤ G.weight c j := by
    obtain ⟨v, rfl, rfl, hv⟩ := G.weight_pos (mem_filter.mp hj).2
    rw [G.weight_at]
    exact (ok.2.2.2 v).2.resolve_left hv.ne'
  have h : (s.card : ℝ) * θ * T ≤ (H : ℝ) * T := calc
    _ = ∑ _ ∈ s, θ * T := by simp [mul_assoc]
    _ ≤ ∑ j ∈ s, G.weight c j := sum_le_sum low
    _ ≤ ∑ j, G.weight c j := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ =>
      push_nonneg _ _ P.charge_nonneg _
    _ ≤ _ := by
      unfold weight
      rw [← push_fst, push_comp]
      exact (G.cells hg hH hT ok hs).mass c
  exact Nat.cast_le.mp (((le_div_iff₀ hθ).mpr
    (le_of_mul_le_mul_right h (Nat.cast_pos.mpr hT))).trans (Nat.le_ceil _))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
end

/-! # Merging on a loopless board preserves the full kernel -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
open Coloring Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
  {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
  {g H T a R : ℕ} {L θ : ℝ} {ha : a < D.scheme.h} (G : p.Plan ha g H T)
  (hg : 0 < g) (hH : 0 < H) (hT : 0 < T) (ok : P.Ready g H T L θ)
  (hs : (P.seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ (D.scheme.h - a))
  (hn : ∀ i, P.diagram.source i ≠ P.diagram.target i)

local notation "C" => G.cells hg hH hT ok hs
local notation "f" => G.bin hg hH hT ok hs
local notation "A" => Cells.before P

include hn in
theorem separated : (A).Separated ((C).seat f) := by
  rintro (i|j|k) e
  · have hc : G.col (P.diagram.source i) = G.col (P.diagram.target i) := congrArg Prod.fst e
    have hr : row (ha := ha) (P.diagram.source i) = row (ha := ha) (P.diagram.target i) :=
      congrArg (fun t => cellIndex _ (suffix a t)) (P.edge i).1.symm
    exact hn i (G.one (Prod.ext hc hr))
  · exact Option.some_ne_none _ (congrArg Prod.snd e)
  · exact Option.some_ne_none _ (congrArg Prod.snd e.symm)

variable (hd : (4 * g) ^ 300 < H) (hR : 0 < R) (hRT : R * H ^ 2 ≤ T) (hx : ((wd x + wd y : ℕ) : ℝ) * H ≤ L)

include hn in
theorem input_eval (neutral : ∀ v, P.diagram.arity v = 0 → ∀ t, Transcript.sample (P.diagram.table v) t = 1) :
    (G.input hg hH hT ok hs hd hR hRT hx).diagram.eval = P.diagram.eval := by
  have ne (v : (A).V) (h : (A).arity v = 0) (t : Transcript.Ports ((A).table v) → Bool) :
      Transcript.sample ((A).table v) t = 1 := by
    rcases v with i|j
    · exact neutral i h t
    · exact ((by decide : 2 ≠ 0) h).elim
  exact (Diagram.eval_pad ((C).stations f) R).trans
    (((G.separated hg hH hT ok hs hn).prune_eval ne).trans (eval_ident P.diagram))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
end

/-!
# Tracking an exterior bit through its equality station

Each old bit keeps its original station. For a boundary bit there
are two more ends, on opposite sides of the attached identity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel
open Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} (G : Diagram F x y)
local notation "E" => (Border.attach (ident F x y) G)

def axis : (E).End → Option Bool × G.End
  | .inl (.inl i) => (some false, .inl (.inl i))
  | .inl (.inr (.inl e)) => (none, .inl (.inr e))
  | .inl (.inr (.inr (.inl i))) => (none, .inl (.inl i))
  | .inl (.inr (.inr (.inr j))) => (some true, .inr (.inl j))
  | .inr (.inl j) => (some false, .inr (.inl j))
  | .inr (.inr (.inl e)) => (none, .inr (.inr e))
  | .inr (.inr (.inr (.inl i))) => (some true, .inl (.inl i))
  | .inr (.inr (.inr (.inr j))) => (none, .inr (.inl j))

def real : G.End → (E).End
  | .inl (.inl i) => .inl (.inr (.inr (.inl i)))
  | .inl (.inr e) => .inl (.inr (.inl e))
  | .inr (.inl i) => .inr (.inr (.inr (.inr i)))
  | .inr (.inr e) => .inr (.inr (.inl e))

def copy : Bool → slots x ⊕ slots y → (E).End
  | false, i => boundaryEnd E i
  | true, .inl i => .inr (.inr (.inr (.inl i)))
  | true, .inr j => .inl (.inr (.inr (.inr j)))

theorem axis_real (q : G.End) : axis G (real G q) = (none, q) := by rcases q with (_|_)|(_|_) <;> rfl
theorem axis_copy (b : Bool) (i : slots x ⊕ slots y) :
    axis G (copy G b i) = (some b, boundaryEnd G i) := by cases b <;> cases i <;> rfl

theorem covered (t : (E).End) : (∃ q, t = real G q) ∨ (∃ b i, t = copy G b i) := by
  rcases t with (i|e|i|j)|(j|e|i|j)
  · exact .inr ⟨false, .inl i, rfl⟩
  · exact .inl ⟨.inl (.inr e), rfl⟩
  · exact .inl ⟨.inl (.inl i), rfl⟩
  · exact .inr ⟨true, .inr j, rfl⟩
  · exact .inr ⟨false, .inr j, rfl⟩
  · exact .inl ⟨.inr (.inr e), rfl⟩
  · exact .inr ⟨true, .inl i, rfl⟩
  · exact .inl ⟨.inr (.inl j), rfl⟩

theorem axis_inj : Function.Injective (axis G) := by
  intro i j h
  rcases covered G i with ⟨_, rfl⟩|⟨_, _, rfl⟩ <;> rcases covered G j with ⟨_, rfl⟩|⟨_, _, rfl⟩ <;>
    simp only [axis_real, axis_copy, Prod.mk.injEq, reduceCtorEq, Option.some.injEq,
      (boundaryEnd G).injective.eq_iff, true_and, false_and] at h
  · rw [h]
  · rw [h.1, h.2]

theorem station_real (q : G.End) : (E).station (real G q) = Sum.inl (G.station q) := by
  rcases q with (_|_)|(_|_) <;> rfl

theorem station_copy (b : Bool) (i : slots x ⊕ slots y) : (E).station (copy G b i) = Sum.inr i := by
  cases b <;> cases i <;> rfl

theorem factor_real (v : G.V) (w : (E).End → Bool) :
    (E).weight (.inl v) (w ∘ .inl) (w ∘ .inr) =
      G.weight v (w ∘ real G ∘ .inl) (w ∘ real G ∘ .inr) := by
  unfold Diagram.weight
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg <;> funext i
  · change w (.inl (Border.merge _ _ _ _ (.inl (G.src ⟨v, i⟩)))) = w (real G (.inl (G.src ⟨v, i⟩)))
    cases G.src ⟨v, i⟩ <;> rfl
  · change w (.inr (((Equiv.refl _).sumCongr ((Equiv.refl _).sumCongr (Equiv.sumComm _ _)))
      (Border.merge _ _ _ _ (.inl (G.dst ⟨v, i⟩))))) = w (real G (.inr (G.dst ⟨v, i⟩)))
    cases G.dst ⟨v, i⟩ <;> rfl

theorem factor_copy (i : slots x ⊕ slots y) (w : (E).End → Bool) :
    (E).weight (.inr i) (w ∘ .inl) (w ∘ .inr) =
      if w (copy G false i) = w (copy G true i) then 1 else 0 := by
  cases i
  · rfl
  · simp only [eq_comm (a := w (copy G false _))]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel
end

/-! # Local labels and peer addresses of active rows -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel
open Rounds Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g H T : ℕ} {L : ℝ}
  {P : Rounds.Board F x y h} (C : Cells P a g H T L)
  {S : Scheme F} {r : S.format.obj} (p : S.Presentation r P.diagram)
  {m d k u : ℕ} (bin : P.diagram.V → Fin H) (w : (Frame S m d a k u).obj)

local notation "N" => scheme S m d a k u
local notation "out" => encode S w

abbrev rowAt (w : (Frame S m d a k u).obj) (t : B m × B a) := (w t.1).2 t.2

/-- Agreement of the transmitted rows with the original incidence
data, expressed entirely in short addresses. -/
structure Manifest where
  cell : C.A ↪ B m × B a
  number : Option (Fin H) ↪ B k
  zero : number none = 0
  rank : P.diagram.V → B u
  one : ∀ i j, 0 < P.diagram.arity i → 0 < P.diagram.arity j → C.cell i = C.cell j → rank i = rank j → i = j
  first : ∀ i, (p.vertex i).2.2 = 0
  slot_eq : ∀ i, 0 < P.diagram.arity i → slot S (rowAt w (cell (C.cell i))) (rank i) = number (some (bin i))
  pattern_eq : ∀ i, 0 < P.diagram.arity i →
    label S (rowAt w (cell (C.cell i))) (rank i) = S.pattern r (p.vertex i)
  appears : ∀ t j, slot S (rowAt w t) j ≠ 0 → ∃ i, 0 < P.diagram.arity i ∧ cell (C.cell i) = t ∧ rank i = j
  index : B m → B m → B d
  stay : ∀ v, index v v = 0
  self : ∀ v, (w v).1 0 = v
  peer : ∀ i s j t, 0 < S.width r (p.vertex i, s) → S.peer r (p.vertex i, s) = some (p.vertex j, t) →
    let v := cell (C.cell i)
    let v' := cell (C.cell j)
    ((rowAt w v (rank i)).2.2 s = (index v.1 v'.1, number (some (bin j)), rank j)) ∧
      (w v.1).1 (index v.1 v'.1) = v'.1 ∧ v.2 = v'.2

namespace Manifest
variable {C p bin w} (A : Manifest C p bin w)

abbrev address (v : P.diagram.V) := A.cell (C.cell v)
abbrev row (v : P.diagram.V) := rowAt w (A.address v)
abbrev mobile (v : P.diagram.V) := A.number (some (bin v))

theorem mobile_ne (v : P.diagram.V) : A.mobile v ≠ 0 :=
  fun h => Option.some_ne_none _ (A.number.injective (h.trans A.zero.symm))

def seat : C.Slot ↪ (N).Vtx :=
  (A.cell.prodMap A.number).trans (Equiv.prodAssoc _ _ _).toEmbedding

abbrev vertex : (C.stations bin).V ↪ (N).Vtx := (Function.Embedding.subtype _).trans A.seat
abbrev idSlot (f : Option Bool) (v : P.diagram.V) := f.elim (A.mobile v) (fun _ => 0)
def place (f : Option Bool) (v : P.diagram.V) : (N).Vtx := ((A.address v).1, (A.address v).2, A.idSlot f v)
def span (f : Option Bool) (v : P.diagram.V) (s : B S.e) : (N).Span :=
  (A.place f v, Parcel.index _ _ (f.getD false, A.rank v, s))

theorem positive {v : P.diagram.V} {s : B S.e} (hw : 0 < S.width r (p.vertex v, s)) :
    0 < P.diagram.arity v := by
  have ht : Nonempty (P.diagram.Port v) := ⟨(p.pin v).symm ⟨s, ⟨0, hw⟩⟩⟩
  simpa [Diagram.Port, Diagram.arity] using Fintype.card_pos_iff.mpr ht

theorem raw_length {v : P.diagram.V} (hv : 0 < P.diagram.arity v) (s : B S.e) :
    (label S (A.row v) (A.rank v)).width 0 s = S.width r (p.vertex v, s) := by
  rw [A.pattern_eq v hv, Scheme.width, A.first]

theorem raw_external {v : P.diagram.V} (hv : 0 < P.diagram.arity v) (s : B S.e) :
    external S (A.row v) (A.rank v) s ↔ S.peer r (p.vertex v, s) = none := by
  unfold external Scheme.peer
  rw [A.pattern_eq v hv, A.first]
  exact Option.map_eq_none_iff.symm

theorem accept {v : P.diagram.V} (hv : 0 < P.diagram.arity v) (s : B S.e) (f : Option Bool)
    (hf : f ≠ none → S.peer r (p.vertex v, s) = none) :
    accepts S (A.row v) (A.idSlot f v) (f.getD false) (A.rank v) s := by
  unfold accepts
  rw [A.slot_eq v hv]
  refine ⟨A.mobile_ne v, ?_⟩
  cases f with
  | none => exact .inr ⟨rfl, rfl⟩
  | some b => exact .inl ⟨rfl, (A.raw_external hv s).mpr (hf (Option.some_ne_none _))⟩

theorem length_eq {v : P.diagram.V} (hv : 0 < P.diagram.arity v) (s : B S.e) (f : Option Bool)
    (hf : f ≠ none → S.peer r (p.vertex v, s) = none) :
    length S (A.row v) (A.idSlot f v) (f.getD false, A.rank v, s) = S.width r (p.vertex v, s) := by
  rw [length, ite_eq_left (A.accept hv s f hf), A.raw_length hv s]

theorem width_eq {v : P.diagram.V} (hv : 0 < P.diagram.arity v) (s : B S.e) (f : Option Bool)
    (hf : f ≠ none → S.peer r (p.vertex v, s) = none) :
    (N).width out (A.span f v s) = S.width r (p.vertex v, s) := by
  rw [Scheme.width, pattern_encode]
  simpa only [span, place, pattern, size, Equiv.symm_apply_apply] using A.length_eq hv s f hf

theorem dir_eq {v : P.diagram.V} (hv : 0 < P.diagram.arity v) (s : B S.e) (f : Option Bool) :
    (N).direction out (A.span f v s) =
      cond (f.getD false) (!(S.direction r (p.vertex v, s))) (S.direction r (p.vertex v, s)) := by
  rw [Scheme.direction, pattern_encode]
  simp only [span, place, pattern, Equiv.symm_apply_apply, side]
  rw [Scheme.direction, A.first]
  exact congrArg (fun l : Pattern F _ _ _ => cond (f.getD false) (!(l.direction 0 s)) (l.direction 0 s))
    (A.pattern_eq v hv)

theorem span_inj {v v' : P.diagram.V} {s s' : B S.e} {f f' : Option Bool}
    (hv : 0 < P.diagram.arity v) (hv' : 0 < P.diagram.arity v')
    (he : A.span f v s = A.span f' v' s') : f = f' ∧ v = v' ∧ s = s' := by
  have hl : A.address v = A.address v' := congrArg (fun t : (N).Span => (t.1.1, t.1.2.1)) he
  have ht : A.idSlot f v = A.idSlot f' v' := congrArg (fun t : (N).Span => t.1.2.2) he
  obtain ⟨hb, hr⟩ := Prod.mk.inj ((Parcel.index u S.e).injective (congrArg Prod.snd he))
  have hvv := A.one _ _ hv hv' (A.cell.injective hl) (Prod.mk.inj hr).1
  refine ⟨?_, hvv, (Prod.mk.inj hr).2⟩
  cases f <;> cases f'
  · rfl
  · exact ((A.mobile_ne v) ht).elim
  · exact ((A.mobile_ne v') ht.symm).elim
  · exact congrArg some hb

private theorem split_span (i : B m) (l : B a) (j : B k) (b : Bool) (x : B u) (s : B S.e)
    (ht : 0 < (N).width out ((i, l, j), Parcel.index _ _ (b, x, s))) :
    accepts S (rowAt w (i, l)) j b x s ∧ 0 < (label S (rowAt w (i, l)) x).width 0 s := by
  have e : (N).width out ((i, l, j), Parcel.index _ _ (b, x, s)) = length S (rowAt w (i, l)) j (b, x, s) := by
    rw [Scheme.width, pattern_encode]
    simp only [pattern, size, Equiv.symm_apply_apply, rowAt]
  have h := ht.trans_eq e
  unfold length at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact (lt_irrefl _ h).elim

theorem used (t : (N).Span) (ht : 0 < (N).width out t) :
    ∃ f v s, A.span f v s = t ∧ 0 < S.width r (p.vertex v, s) ∧
      (f ≠ none → S.peer r (p.vertex v, s) = none) := by
  obtain ⟨⟨i, l, j⟩, q⟩ := t
  obtain ⟨⟨b, x, s⟩, rfl⟩ := (Parcel.index u S.e).surjective q
  obtain ⟨ha, ht'⟩ := split_span i l j b x s ht
  clear ht
  obtain ⟨v, hv, he, hr⟩ := A.appears (i, l) x ha.1
  have hw : 0 < S.width r (p.vertex v, s) := by
    rw [← A.raw_length hv, hr]
    unfold row address
    rw [he]; exact ht'
  have e : A.row v = rowAt w (i, l) := congrArg (rowAt w) he
  obtain ⟨rfl, hp⟩|⟨hj, rfl⟩ := ha.2
  · refine ⟨some b, v, s, ?_, hw, fun _ => (A.raw_external hv s).mp ?_⟩
    · simp only [span, place, address, he, hr]; rfl
    · rw [e, hr]; exact hp
  · have hm : A.mobile v = j := by
      rw [show A.mobile v = slot S (A.row v) (A.rank v) from (A.slot_eq v hv).symm, e, hr]
      exact hj.symm
    refine ⟨none, v, s, ?_, hw, by simp⟩
    simp only [span, place, address, he, hr, idSlot, Option.elim_none, hm]; rfl

end Manifest
end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel
end

/-! # The address of each physical wire end after merging -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
open Rounds Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g H T : ℕ} {L : ℝ}
  {P : Rounds.Board F x y h} {C : Cells P a g H T L}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r P.diagram}
  {m d k u : ℕ} {bin : P.diagram.V → Fin H} {w : (Frame S m d a k u).obj} (A : Manifest C p bin w)

local notation "G" => P.diagram
local notation "E" => Cells.before P
local notation "N" => scheme S m d a k u
local notation "out" => encode S w

abbrev stub (p : S.Presentation r P.diagram) (q : (G).End) := (p.toSeating.ends q).1.2

theorem old (p : S.Presentation r P.diagram) (q : (G).End) :
    (p.toSeating.ends q).1 = (p.vertex ((G).station q), stub p q) := Prod.ext (p.end_station q) rfl

theorem live (p : S.Presentation r P.diagram) (q : (G).End) : 0 < (G).arity ((G).station q) :=
  positive ((old p q) ▸ (p.toSeating.ends q).2.pos)

def destination (t : (E).End) : (N).Span :=
  let z := axis G t
  A.span z.1 ((G).station z.2) (stub p z.2)

theorem is_exposed (p : S.Presentation r P.diagram) (t : (E).End) :
    (axis G t).1 ≠ none → S.peer r (p.toSeating.ends (axis G t).2).1 = none := by
  rcases covered G t with ⟨q, rfl⟩|⟨b, i, rfl⟩
  · simp only [axis_real]; exact fun he => (he rfl).elim
  · rw [axis_copy]; exact fun _ => (p.no_peer _).mpr ⟨i, rfl⟩

theorem destination_size (t : (E).End) :
    (N).width out (A.destination t) = S.width r (p.toSeating.ends (axis G t).2).1 := by
  have h := is_exposed p t
  rw [old p] at h ⊢
  exact A.width_eq (live p _) _ _ h

def route (t : (E).End) : (N).Pin out :=
  ⟨A.destination t, (p.toSeating.ends (axis G t).2).2.cast (A.destination_size t).symm⟩

theorem route_inj : Function.Injective A.route := by
  intro i j h
  have he : A.destination i = A.destination j := congrArg Sigma.fst h
  have hi := live p (axis G i).2
  have hj := live p (axis G j).2
  obtain ⟨hd, hv, hs⟩ := A.span_inj hi hj he
  apply axis_inj G
  refine Prod.ext hd (p.toSeating.ends.injective ?_)
  have ht : (p.toSeating.ends (axis G i).2).1 = (p.toSeating.ends (axis G j).2).1 :=
    by rw [old p (axis G i).2, old p (axis G j).2, hv, hs]
  exact Sigma.ext ht ((Fin.heq_ext_iff (congrArg (S.width r) ht)).mpr
    (congrArg (fun t : (N).Pin out => t.2.val) h))

theorem route_surj : Function.Surjective A.route := by
  rintro ⟨s, j⟩
  obtain ⟨f, v, b, rfl, hw, hb⟩ := A.used s j.pos
  let q : S.Pin r := ⟨(p.vertex v, b), j.cast (A.width_eq (positive hw) b f hb)⟩
  let i := p.toSeating.ends.symm q
  have hi : p.toSeating.ends i = q := p.toSeating.ends.apply_symm_apply q
  have hv : (G).station i = v :=
    p.vertex.injective ((p.end_station i).symm.trans (congrArg (fun z : S.Pin r => z.1.1) hi))
  have hq : ∃ t, axis G t = (f, i) := by
    cases f with
    | none => exact ⟨real G i, axis_real G _⟩
    | some c =>
      obtain ⟨l, hl⟩ := (p.no_peer i).mp (by rw [hi]; exact hb (Option.some_ne_none _))
      exact ⟨copy G c l, (axis_copy G _ _).trans (Prod.ext rfl hl)⟩
  obtain ⟨t, ht⟩ := hq
  have hd : A.destination t = A.span f v b := by
    unfold destination
    rw [ht]
    dsimp only
    rw [hv, show stub p i = b from congrArg (fun z : S.Pin r => z.1.2) hi]
  refine ⟨t, Sigma.ext hd ((Fin.heq_ext_iff (congrArg ((N).width out) hd)).mpr ?_)⟩
  change (p.toSeating.ends (axis G t).2).2.val = j.val
  rw [ht, hi]; rfl

theorem location (t : (E).End) : (A.route t).1.1 = A.seat (C.seat bin ((E).station t)) := by
  change A.place _ _ = _
  rcases covered G t with ⟨i, rfl⟩|⟨b, j, rfl⟩
  · rw [axis_real, station_real]
    rfl
  · rw [axis_copy, station_copy, station_boundary]
    exact congrArg (fun k => ((A.address (portEnd G j)).1, (A.address (portEnd G j)).2, k)) A.zero.symm

theorem direction (hd : p.Directed) (t : (E).End) : (N).direction out (A.route t).1 = t.isRight := by
  rw [show (A.route t).1 = A.destination t from rfl, destination, A.dir_eq (live p _), ← old, hd]
  rcases t with (_|_|_|_)|(_|_|_|_) <;> rfl

variable (sep : (Cells.before P).Separated (C.seat bin))

def ends : (C.stations bin).End ≃ (N).Pin out :=
  sep.ends.symm.trans (Equiv.ofBijective A.route ⟨A.route_inj, A.route_surj⟩)

theorem ends_at (t : (E).End) : A.ends sep (sep.ends t) = A.route t :=
  congrArg A.route (sep.ends.symm_apply_apply t)

theorem station (t : (C.stations bin).End) :
    (A.ends sep t).1.1 = A.vertex ((C.stations bin).station t) := by
  obtain ⟨q, rfl⟩ := sep.ends.surjective t
  rw [ends_at, location, ← sep.station]
  rcases q with (_|_)|(_|_) <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
end

/-! # Linking spans at a merged station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
open Rounds Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g H T : ℕ} {L : ℝ}
  {P : Rounds.Board F x y h} {C : Cells P a g H T L}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r P.diagram}
  {m d k u : ℕ} {bin : P.diagram.V → Fin H} {w : (Frame S m d a k u).obj} (A : Manifest C p bin w)

local notation "G" => P.diagram
local notation "E" => Cells.before P
local notation "N" => scheme S m d a k u
local notation "out" => encode S w

def Leads (q t : (N).Span) : Prop :=
  (N).peer out q = some t ∧ (N).arc out q = some (A.index q.1.1 t.1.1, t.1.2.2)

abbrev localLink (q : (N).Span) := ((N).pattern out q.1).peer q.1.2.2 q.2

private theorem leads_of {q t : (N).Span}
    (h : localLink (w := w) q = some (A.index q.1.1 t.1.1, t.1.2.2, t.2))
    (hn : (w q.1.1).1 (A.index q.1.1 t.1.1) = t.1.1) (hb : q.1.2.1 = t.1.2.1) :
    A.Leads q t := by
  unfold localLink at h
  unfold Leads Scheme.peer Scheme.arc Pattern.target
  rw [h]
  simp only [Option.map_some, Parcel.encode, hn, hb, and_self]

theorem local_link (f : Option Bool) (v : (G).V) (s : B S.e) :
    localLink (w := w) (A.span f v s) =
      Parcel.link S (A.row v) (A.idSlot f v) (f.getD false, A.rank v, s) := by
  unfold localLink
  rw [pattern_encode]
  simp only [span, place, pattern, Equiv.symm_apply_apply, row, rowAt]

variable {i j : P.diagram.V} {s t : B S.e}

theorem joined (hw : 0 < S.width r (p.vertex i, s)) (he : S.peer r (p.vertex i, s) = some (p.vertex j, t)) :
    A.Leads (A.span none i s) (A.span none j t) := by
  obtain ⟨hp, hn, hb⟩ := A.peer i s j t hw he
  apply A.leads_of _ hn hb
  have hi := positive hw
  have ht : ∃ d k, (label S (A.row i) (A.rank i)).peer 0 s = some (d, k, t) := by
    rw [A.pattern_eq _ hi, ← A.first i]
    obtain ⟨⟨d, k, e⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp he
    have : e = t := congrArg Prod.snd h₂
    subst e
    exact ⟨_, _, h₁⟩
  obtain ⟨l, k, hk⟩ := ht
  rw [A.local_link, Parcel.link, A.length_eq hi s none (by simp), ite_eq_left hw]
  change (if A.mobile i = 0 then _ else _) = _
  rw [ite_eq_right (A.mobile_ne i), hk]
  dsimp only
  rw [show (A.row i (A.rank i)).2.2 s = _ from hp]
  rfl

theorem exposed (hw : 0 < S.width r (p.vertex i, s)) (he : S.peer r (p.vertex i, s) = none) :
    (N).peer out (A.span (some false) i s) = none ∧
      A.Leads (A.span none i s) (A.span (some true) i s) ∧
      A.Leads (A.span (some true) i s) (A.span none i s) := by
  have hi := positive hw
  have hg := (A.raw_external hi s).mpr he
  have hn : (w (A.address i).1).1 (A.index (A.address i).1 (A.address i).1) = (A.address i).1 := by
    rw [A.stay, A.self]
  have hl (b : Option Bool) := A.length_eq hi s b (fun _ => he)
  constructor
  · change (localLink (w := w) _).map _ = _
    rw [A.local_link, Parcel.link, hl, ite_eq_left hw]
    simp [idSlot]
  constructor
  · refine A.leads_of ?_ hn rfl
    rw [A.local_link, Parcel.link, hl, ite_eq_left hw]
    change (if A.mobile i = 0 then _ else _) = _
    rw [ite_eq_right (A.mobile_ne i), hg]
    simp only [span, place, A.stay]
    rfl
  · refine A.leads_of ?_ hn rfl
    rw [A.local_link, Parcel.link, hl, ite_eq_left hw]
    simp only [idSlot, Option.elim_some, ite_true, Option.getD_some, span, place, A.stay]
    rw [show slot S (A.row i) (A.rank i) = A.mobile i from A.slot_eq i hi]
    rfl

theorem unused {q : (N).Span} (h : ¬0 < (N).width out q) : (N).peer out q = none := by
  rw [Scheme.width, pattern_encode] at h
  simp only [pattern, size] at h
  rw [Scheme.peer, pattern_encode]
  change (Parcel.link _ _ _ _).map _ = none
  unfold Parcel.link
  rw [ite_eq_right h]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
end

/-! # Peer alignment in the merged network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
open Rounds Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h a g H T : ℕ} {L : ℝ}
  {P : Rounds.Board F x y h} {C : Cells P a g H T L}
  {S : Scheme F} {r : S.format.obj} {p : S.Presentation r P.diagram}
  {m d k u : ℕ} {bin : P.diagram.V → Fin H} {w : (Frame S m d a k u).obj} (A : Manifest C p bin w)

local notation "G" => P.diagram
local notation "E" => Cells.before P
local notation "N" => scheme S m d a k u
local notation "out" => encode S w

def Bond (i j : (E).End) : Prop :=
  A.Leads (A.route i).1 (A.route j).1 ∧ A.Leads (A.route j).1 (A.route i).1 ∧
    (N).width out (A.route i).1 = (N).width out (A.route j).1 ∧
    (A.route i).2.val = (A.route j).2.val

theorem Bond.swap {i j : (E).End} (e : A.Bond i j) : A.Bond j i :=
  ⟨e.2.1, e.1, e.2.2.1.symm, e.2.2.2.symm⟩

theorem real_span (i : (G).End) :
    (A.route (real G i)).1 = A.span none ((G).station i) (stub p i) := by
  simp only [route, destination, axis_real]

theorem copy_span (b : Bool) (i : slots x ⊕ slots y) :
    (A.route (copy G b i)).1 = A.span (some b) (portEnd G i) (stub p (boundaryEnd G i)) := by
  simp only [route, destination, axis_copy, station_boundary]

theorem routed_width (i : (E).End) :
    (N).width out (A.route i).1 = S.width r (p.toSeating.ends (axis G i).2).1 :=
  A.destination_size i

theorem offset (i : (E).End) : (A.route i).2.val = (p.toSeating.ends (axis G i).2).2.val := rfl

private theorem bond_old (z : (G).E) :
    A.Bond (real G (.inl (.inr z))) (real G (.inr (.inr z))) := by
  have h := p.internal z
  have b := p.proper _ _ h.1
  have go {i j : (G).End} (he : S.peer r (p.toSeating.ends i).1 = some (p.toSeating.ends j).1) :
      A.Leads (A.route (real G i)).1 (A.route (real G j)).1 := by
    rw [old p i, old p j] at he
    rw [real_span, real_span]
    exact A.joined ((old p i) ▸ (p.toSeating.ends i).2.pos) he
  refine ⟨go h.1, go b.1, ?_, ?_⟩
  · rw [routed_width, routed_width, axis_real, axis_real]; exact b.2.1
  · rw [offset, offset, axis_real, axis_real]; exact h.2

private theorem bond_copy (i : slots x ⊕ slots y) :
    (N).peer out (A.route (copy G false i)).1 = none ∧
      A.Bond (real G (boundaryEnd G i)) (copy G true i) := by
  let q := boundaryEnd G i
  have he := (p.no_peer q).mpr ⟨i, rfl⟩
  have hw := (p.toSeating.ends q).2.pos
  rw [old p q] at he hw
  obtain ⟨h₁, h₂, h₃⟩ := A.exposed hw he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [copy_span, ← station_boundary]; exact h₁
  · rw [real_span, copy_span, ← station_boundary]; exact h₂
  · rw [real_span, copy_span, ← station_boundary]; exact h₃
  · rw [routed_width, routed_width, axis_real, axis_copy]
  · rw [offset, offset, axis_real, axis_copy]

theorem internal (i : (E).E) : A.Bond (.inl (.inr i)) (.inr (.inr i)) := by
  rcases i with z|i|j
  · exact A.bond_old z
  · exact (A.bond_copy (.inl i)).2
  · exact ((A.bond_copy (.inr j)).2.swap A)

theorem outside (i : slots x ⊕ slots y) :
    (N).peer out (A.route (boundaryEnd E i)).1 = none := (A.bond_copy i).1

private theorem reciprocal {q t : (N).Span} (he : (N).peer out q = some t) :
    ∃ i j : (E).End, (A.route i).1 = q ∧ (A.route j).1 = t ∧ A.Bond i j ∧ i.isRight ≠ j.isRight := by
  have hq : 0 < (N).width out q := by
    by_contra hn
    rw [unused hn] at he
    contradiction
  obtain ⟨i, hi⟩ := A.route_surj ⟨q, ⟨0, hq⟩⟩
  have hw : (A.route i).1 = q := congrArg Sigma.fst hi
  rw [← hw] at he
  rcases i with (i|i)|(i|i)
  · exact (Option.some_ne_none t (he.symm.trans (A.outside (.inl i)))).elim
  · have e := A.internal i
    exact ⟨_, _, hw, Option.some.inj (e.1.1.symm.trans he), e, Bool.false_ne_true⟩
  · exact (Option.some_ne_none t (he.symm.trans (A.outside (.inr i)))).elim
  · have e := (A.internal i).swap A
    exact ⟨_, _, hw, Option.some.inj (e.1.1.symm.trans he), e, Ne.symm Bool.false_ne_true⟩

include A in
theorem proper (hd : p.Directed) : (N).Proper out := by
  intro i j he
  obtain ⟨s, t, rfl, rfl, b, hn⟩ := A.reciprocal he
  exact ⟨b.2.1.1, b.2.2.1, by rwa [A.direction hd, A.direction hd]⟩

theorem arc_eq (i : (N).Span) :
    (N).arc out i = ((N).peer out i).map (fun q => (A.index i.1.1 q.1.1, q.1.2.2)) := by
  cases h : (N).peer out i with
  | none =>
    have he := Scheme.destination (r := out) i
    rw [h, Option.map_none] at he
    exact Option.map_eq_none_iff.mp he.symm
  | some t =>
    obtain ⟨s, u, rfl, rfl, b, _⟩ := A.reciprocal h
    exact b.1.2

include A in
theorem resolved : (N).Resolved out := by
  intro v i j _ _ h
  rw [A.arc_eq, A.arc_eq]
  simpa only [Option.map_map, Function.comp_def] using
    congrArg (Option.map (fun y : (N).Vtx => (A.index v.1 y.1, y.2.2))) h

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
end

/-!
# Enumerating active rows in one colony

The temporary sheet contains the label, counter and elected interval
of every suffix. The record sent to the next stage keeps only active
rows and replaces remote host names by indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing Rounds
open scoped Classical

variable {F : Type} (D : Template F) (n : ℕ)

abbrev Sheet := Format.vec n (.pair (.addr D.scheme.ℓ) (.pair (.addr D.count) (.addr (n + 1))))

theorem sheet_width : (D.Sheet n).width = 2 ^ n * (D.scheme.ℓ + (D.count + (n + 1))) := by
  simp only [Sheet, Format.width_vec, Format.width_pair, Format.width_addr]
  exact congrArg (fun x => 2 ^ n * (D.scheme.ℓ + (D.count + x))) (Format.width_addr (n + 1))

namespace Sheet

variable {n} (c : (D.Sheet n).obj)

def weights (j : B n) (i : B n) := if (c i).2.2 = (c j).2.2 then D.load (c i).2.1 else 0

def list (u : ℕ) (l : B n → ℝ) (i : B n) : B u :=
  let s := Presents.Plan.active l
  if h : i ∈ s ∧ s.card ≤ 2 ^ u then Fin.castLE h.2 (s.equivFin ⟨i, h.1⟩) else 0

theorem list_inj (u : ℕ) (l : B n → ℝ) (hl : (Presents.Plan.active l).card ≤ 2 ^ u) :
    Set.InjOn (list u l) (Presents.Plan.active l) := by
  intro i hi j hj h
  let s := Presents.Plan.active l
  have he (x : B n) (hx : x ∈ s) : list u l x = Fin.castLE hl (s.equivFin ⟨x, hx⟩) :=
    dite_eq_left (show x ∈ s ∧ s.card ≤ 2 ^ u from ⟨hx, hl⟩)
  rw [he i hi, he j hj] at h
  exact congrArg Subtype.val (s.equivFin.injective ((Fin.castLE_injective hl) h))

abbrev rank (u : ℕ) (j : B n) := list u (weights D c j) j
abbrev bins (H T : ℕ) (hH : 0 < H) (j : B n) := Cells.chooseBin H T hH (weights D c j) j
abbrev slots (H : ℕ) := Nat.clog 2 (H + 1)

def number (H : ℕ) : Option (Fin H) ↪ B (slots H) :=
  ((finSuccEquiv H).symm.toEmbedding).trans (Fin.castLEEmb (Nat.le_pow_clog (by decide) _))

theorem number_none (H : ℕ) : number H none = 0 := by apply Fin.ext; rfl

def live (j : B n) := Nonempty ((D.scheme.decode (c j).1).Pin 0)

def eligible (u : ℕ) (z : B (n + 1)) (b : B u) (j : B n) : Prop :=
  live D c j ∧ (c j).2.2 = z ∧ rank D c u j = b

def find (u : ℕ) (z : B (n + 1)) (b : B u) : Option (B n) :=
  if h : ∃ j, eligible D c u z b j then some h.choose else none

theorem find_spec (u : ℕ) (z : B (n + 1)) (b : B u) (j : B n) (he : find D c u z b = some j) :
    eligible D c u z b j := by
  unfold find at he
  split at he
  · rename_i h
    rw [← Option.some.inj he]
    exact h.choose_spec
  · contradiction

variable (H T : ℕ) (hH : 0 < H) (u d : ℕ)
  (neigh : B D.scheme.d → (D.Sheet n).obj)
  (nav : B (n + 1) → B D.scheme.d → B (n + 1) → B d)

def target (j : B n) (s : B D.scheme.e) : (Parcel.destination d (slots H) u).obj :=
  match (D.scheme.decode (c j).1).peer 0 s with
  | none => (0, 0, 0)
  | some t =>
    let w := neigh t.1
    (nav (c j).2.2 t.1 (w j).2.2, number H (some (bins D w H T hH j)), rank D w u j)

def record (z : B (n + 1)) : (Parcel.record D.scheme d (slots H) u).obj := fun i =>
  match find D c u z i with
  | none => (0, 0, fun _ => (0, 0, 0))
  | some j => (number H (some (bins D c H T hH j)), (c j).1, target D c H T hH u d neigh nav j)

end Sheet

variable [Field F] (a : ℕ) (ha : a < D.scheme.h) (g H T : ℕ) (r : D.format.obj)
local notation "q" => D.scheme.h - a

def sheet (v : B D.scheme.m) (x : B a) : (D.Sheet q).obj := fun j =>
  let i := D.position a ha.le x j
  ((r.1 v).2 i, D.counter r v i, Presents.Plan.labels (D := D) (r := r) (ha := ha)
    (g := g) (H := H) (T := T) v x j)

abbrev childInput := Child.fromGroup (D.groups a ha.le r) false
abbrev binNav := Child.neighbors q g (D.childInput a ha r)
abbrev childM := D.scheme.m + ((D.scheme.h - a) + 1)
abbrev childD := Child.nextWidth (D.scheme.h - a) g D.scheme.d

def childFrame (hH : 0 < H) (u : ℕ) : (Parcel.Frame D.scheme (D.childM a) (D.childD a g) a (Sheet.slots H) u).obj :=
  let Z := D.binNav a ha g r
  let y := Match.rowIndex D.scheme.m (q + 1)
  let f := D.sheet a ha g H T r
  fun i => (Z i, fun j => Sheet.record D (f (y i).1 j) H T hH u _
    (fun s => f (D.nav r (y i).1 s) j)
    (fun l s l' => Child.index Z (y.symm ((y i).1, l)) (y.symm (D.nav r (y i).1 s, l')))
    (y i).2)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end
