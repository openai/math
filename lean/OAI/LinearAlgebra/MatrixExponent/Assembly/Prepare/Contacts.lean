import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Sheet
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel

/-! # Recovering occupied rows and their ranks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
open Coloring Packing Rounds Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
  {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
  {g H T a u : ℕ} {L θ : ℝ} {ha : a < D.scheme.h} (G : p.Plan ha g H T)

local notation "n" => D.scheme.h - a
local notation "old" => P.diagram
local notation "suffixOf" => (row (P := P) (ha := ha))
local notation "colony" => G.group.Colony
local notation "page" => D.sheet a ha g H T r

abbrev parent (i : (old).V) := p.host (P.place i).1
abbrev prefixOf (i : (old).V) := cellIndex _ (ancestor ha.le (P.place i).2)
abbrev sheetAt (i : (old).V) := page (parent (p := p) i) (prefixOf (ha := ha) i)
abbrev rank (u : ℕ) (i : (old).V) := Sheet.list u (G.weight (G.col i)) (suffixOf i)

def cellAddr : colony ↪ B (D.childM a) × B a :=
  ((⟨G.group.site, G.group.site_injective⟩ : colony ↪ _).trans splitSite.toEmbedding).trans
    ((Child.host p.host n).prodMap (cellIndex _).toEmbedding)

local notation "base" => (parent (p := p))
local notation "top" => (prefixOf (P := P) (ha := ha))
local notation "atSheet" => (sheetAt (p := p) (ha := ha) (g := g) (H := H) (T := T))

theorem cell_parts (i : (old).V) :
    G.cellAddr (G.col i) = ((Match.rowIndex D.scheme.m (n + 1)).symm (base i, G.interval (G.col i)), top i) := rfl

omit [Field F] in
private theorem position_inj : Function.Injective
    (fun t : B a × B n => D.position a ha.le t.1 t.2) :=
  ((cellIndex _).injective.comp (splitCell a ha.le).symm.injective).comp
    (((cellIndex a).symm.prodCongr (cellIndex n).symm).injective)

theorem given (i : (old).V) : p.pres.vertex i = (base i, D.position a ha.le (top i) (suffixOf i), 0) := by
  rw [p.vertex]
  have ht : D.position a ha.le (top i) (suffixOf i) = cellIndex _ (P.place i).2 := by
    unfold position prefixOf row
    simp only [Equiv.symm_apply_apply]
    exact congrArg (cellIndex _) ((splitCell a ha.le).symm_apply_apply (P.place i).2)
  rw [ht]

theorem row_label (i : (old).V) : D.scheme.decode (atSheet i (suffixOf i)).1 =
    D.scheme.pattern r.1 (p.pres.vertex i) := by rw [given (ha := ha)]; rfl

theorem row_interval (i : (old).V) :
    (atSheet i (suffixOf i)).2.2 = G.interval (G.col i) :=
  G.tag (occurrence (ha := ha) i).1 (occurrence (ha := ha) i).2

theorem row_weights (i : (old).V) :
    Sheet.weights D (atSheet i) (suffixOf i) = G.weight (G.col i) := by
  rw [← G.profile_eq]
  funext j
  unfold Sheet.weights
  rw [G.row_interval]
  rfl

theorem row_rank (i : (old).V) :
    Sheet.rank D (atSheet i) u (suffixOf i) = G.rank u i := congrArg (fun l => Sheet.list _ l _) (G.row_weights i)

theorem row_live (i : (old).V) (hi : 0 < (old).arity i) : Sheet.live D (atSheet i) (suffixOf i) := by
  have h : Nonempty ((old).Port i) := Fintype.card_pos_iff.mp (by simpa [Diagram.Port, Diagram.arity] using hi)
  have h' : Nonempty (D.scheme.LocalPin r.1 (p.pres.vertex i)) := h.map (p.pres.pin i)
  rw [given (ha := ha)] at h'
  exact h'

theorem live_row (v : B D.scheme.m) (l : B a) (j : B n) (hw : Sheet.live D (page v l) j) :
    ∃ i, 0 < (old).arity i ∧ base i = v ∧ top i = l ∧ suffixOf i = j := by
  let v' : D.scheme.Vtx := (v, D.position a ha.le l j, 0)
  have hv : Nonempty (D.scheme.LocalPin r.1 v') := hw
  obtain ⟨z⟩ := hv
  obtain ⟨i, hi⟩ := p.pres.cover (D.scheme.port r.1 v' z)
  change p.pres.vertex i = v' at hi
  have h₁ : 0 < (old).arity i := Parcel.Manifest.positive (s := z.1) (by rw [hi]; exact z.2.pos)
  rw [given (ha := ha)] at hi
  have he := Prod.mk.inj hi
  have h₂ : (top i, suffixOf i) = (l, j) := position_inj (ha := ha) (Prod.mk.inj he.2).1
  exact ⟨i, h₁, he.1, Prod.mk.inj h₂⟩

variable (hg : 0 < g) (hH : 0 < H) (hT : 0 < T) (ok : P.Ready g H T L θ)
  (hs : (P.seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ (D.scheme.h - a))

theorem row_bin (i : (old).V) :
    Sheet.bins D (atSheet i) H T hH (suffixOf i) = G.bin hg hH hT ok hs i :=
  congrArg (fun l => Cells.chooseBin H T hH l (suffixOf i)) (G.row_weights i)

abbrev depth (H : ℕ) (θ : ℝ) := Nat.clog 2 ⌈(H : ℝ) / θ⌉₊

def Room (u : ℕ) : Prop := ∀ c, (active (G.weight c)).card ≤ 2 ^ u

include hg hH hT ok hs in
theorem room (hθ : 0 < θ) : G.Room (depth H θ) := fun c =>
  (G.active_card hg hH hT ok hs hθ c).trans (Nat.le_pow_clog (by decide) _)

theorem unique_rank (hw : G.Room u) (i j : (old).V) (hi : 0 < (old).arity i) (hj : 0 < (old).arity j)
    (he : G.col i = G.col j) (hr : G.rank u i = G.rank u j) : i = j := by
  have mem i (h : 0 < (old).arity i) : suffixOf i ∈ active (G.weight (G.col i)) :=
    mem_filter.mpr ⟨mem_univ _, (G.weight_at i).symm ▸ (Nat.cast_pos.mpr h).trans_le (P.cover i)⟩
  unfold rank at hr
  rw [he] at hr
  exact G.one (Prod.ext he (Sheet.list_inj u _ (hw _) (he ▸ mem i hi) (mem j hj) hr))

theorem eligible (v : B D.scheme.m) (l : B a) (z : B (n + 1)) (b : B u) (j : B n) :
    Sheet.eligible D (page v l) u z b j ↔
      ∃ i, 0 < (old).arity i ∧ G.cellAddr (G.col i) = ((Match.rowIndex _ _).symm (v, z), l) ∧
        G.rank u i = b ∧ suffixOf i = j := by
  constructor
  · rintro ⟨hl, hz, hr⟩
    obtain ⟨i, hi, rfl, rfl, rfl⟩ := live_row (p := p) _ _ _ hl
    refine ⟨i, hi, ?_, (G.row_rank i).symm.trans hr, rfl⟩
    rw [G.cell_parts, ← G.row_interval]
    exact congrArg (fun z => ((Match.rowIndex _ _).symm (base i, z), top i)) hz
  · rintro ⟨i, hi, he, rfl, rfl⟩
    rw [G.cell_parts] at he
    obtain ⟨hp, rfl⟩ := Prod.mk.inj he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ((Match.rowIndex _ _).symm.injective hp)
    exact ⟨row_live i hi, G.row_interval i, G.row_rank i⟩

theorem found (hw : G.Room u) (i : (old).V) (hi : 0 < (old).arity i) :
    Sheet.find D (atSheet i) u (G.interval (G.col i)) (G.rank u i) = some (suffixOf i) := by
  have ht := G.eligible (base i) (top i) (G.interval (G.col i)) (G.rank u i)
  have ex : ∃ j, Sheet.eligible D (atSheet i) u (G.interval (G.col i)) (G.rank u i) j :=
    ⟨suffixOf i, (ht _).mpr ⟨i, hi, rfl, rfl, rfl⟩⟩
  rw [Sheet.find, dite_eq_left ex]
  obtain ⟨v, hv, he, hr, hl⟩ := (ht _).mp ex.choose_spec
  have hh := G.unique_rank hw v i hv hi (G.cellAddr.injective he) hr
  subst v
  exact congrArg some hl.symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
end

/-! # Reading old and copied bits from the merged tables -/

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

def bit {F : Type} (S : Scheme F) (s : S.format.obj) (t : S.Pin s → Bool) (p : S.Span) (i : ℕ) :=
  if h : i < S.width s p then t ⟨p, ⟨i, h⟩⟩ else false

theorem bit_at {F : Type} (S : Scheme F) (s : S.format.obj) (t : S.Pin s → Bool) (p : S.Pin s) :
    bit S s t p.1 p.2.val = t p := by rw [bit, dite_eq_left p.2.isLt]

private def value {d k e : ℕ} (A : Pattern F d k e) (j : B k) (w : B e → ℕ → Bool) :=
  A.value j (fun s l => w s l.val)

omit [Field F] in
private theorem table_bit {S : Scheme F} (r : S.format.obj) (t : S.Pin r → Bool) (v : S.Vtx) :
    S.table r v (t ∘ S.port r v) = value (S.pattern r v) v.2.2 (fun s => bit S r t (v, s)) := by
  apply congrArg ((S.pattern r v).value v.2.2)
  funext j i
  exact (bit_at S r t ⟨(v, j), i⟩).symm

abbrev atRow (v : (N).Vtx) := rowAt w (v.1, v.2.1)
def bitsAt (v : (N).Vtx) (t : (N).Pin out → Bool) (b : Bool) (i : B u) (s : B S.e) :=
  bit (N) out t (v, Parcel.index _ _ (b, i, s))

theorem table_factor (v : (N).Vtx) (t : (N).Pin out → Bool) :
    (N).table out v (t ∘ (N).port out v) =
      ∏ i, factor S (atRow (w := w) v) v.2.2 (bitsAt v t) i := by
  rw [table_bit, pattern_encode]
  let R := atRow (w := w) v
  let f := fun s (i : Fin (size S R v.2.2 s)) => bit (N) out t (v, s) i.val
  change (∏ i, factor S R v.2.2 (read S R v.2.2 f) i) = _
  have h : read S R v.2.2 f = bitsAt v t := by
    funext b i s j
    let q := Parcel.index _ _ (b, i, s)
    have he : (N).width out (v, q) = size S R v.2.2 q := by rw [Scheme.width, pattern_encode]; rfl
    change (if h : j < size S R v.2.2 q then f q ⟨j, h⟩ else false) = bit (N) out t (v, q) j
    split
    · rfl
    · rename_i hh
      unfold bit
      rw [dite_eq_right (fun hj => hh (hj.trans_eq he))]
  rw [h]

variable (t : (scheme S m d a k u).Pin (encode S w) → Bool)

theorem real_at (q : (G).End) :
    bitsAt (A.place none ((G).station q)) t false (A.rank ((G).station q)) (stub p q) (p.toSeating.ends q).2.val =
      t (A.route (real G q)) := by
  have h := bit_at (N) out t (A.route (real G q))
  rw [offset, axis_real, real_span] at h
  exact h

theorem copy_at (q : slots x ⊕ slots y) (b : Bool) :
    bitsAt (A.place (some false) (portEnd G q)) t b (A.rank (portEnd G q))
       (stub p (boundaryEnd G q)) (p.toSeating.ends (boundaryEnd G q)).2.val =
      t (A.route (copy G b q)) := by
  have h := bit_at (N) out t (A.route (copy G b q))
  rw [offset, axis_copy, copy_span] at h
  exact h

def contribution (i : (E).V) := (E).weight i (t ∘ A.route ∘ .inl) (t ∘ A.route ∘ .inr)

theorem row_value (i : (G).V) (hi : 0 < (G).arity i) :
    factor S (A.row i) (A.mobile i) (bitsAt (A.place none i) t) (A.rank i) =
      A.contribution t (.inl i) := by
  have hn : slot S (A.row i) (A.rank i) = A.mobile i := A.slot_eq i hi
  rw [factor, hn, ite_eq_right (A.mobile_ne i), ite_eq_right (A.mobile_ne i), ite_eq_left rfl]
  change value (label S (A.row i) (A.rank i)) 0 (bitsAt (A.place none i) t false (A.rank i)) =
    (E).weight (.inl i) ((t ∘ A.route) ∘ .inl) ((t ∘ A.route) ∘ .inr)
  rw [A.pattern_eq _ hi, ← A.first i, factor_real]
  let w' := t ∘ A.route ∘ real G ∘ p.toSeating.ends.symm
  have eq : w' ∘ p.toSeating.ends = t ∘ A.route ∘ real G :=
    funext fun j => congrArg (t ∘ A.route ∘ real G) (p.toSeating.ends.symm_apply_apply j)
  have he := p.weight_at w' i
  rw [← Function.comp_assoc w', ← Function.comp_assoc w', eq] at he
  refine Eq.trans ?_ he
  apply congrArg ((S.pattern r (p.vertex i)).value (p.vertex i).2.2)
  funext s l
  let q := p.toSeating.ends.symm ⟨(p.vertex i, s), l⟩
  have hp : p.toSeating.ends q = ⟨(p.vertex i, s), l⟩ := p.toSeating.ends.apply_symm_apply _
  have hs : (G).station q = i := p.vertex.injective ((p.end_station q).symm.trans
    (congrArg (fun z : S.Pin r => z.1.1) hp))
  have h := A.real_at t q
  rw [hs, stub, hp] at h
  exact h

def equal (i : slots x ⊕ slots y) : Prop := t (A.route (copy G false i)) = t (A.route (copy G true i))

theorem copy_value (q : slots x ⊕ slots y) :
    A.contribution t (.inr q) = if A.equal t q then 1 else 0 := by
  have he := factor_copy G q (t ∘ A.route)
  change A.contribution t (.inr q) = _ at he
  rw [he]
  by_cases h : A.equal t q
  · exact (ite_eq_left h).trans (ite_eq_left h).symm
  · exact (ite_eq_right h).trans (ite_eq_right h).symm

theorem check_value (i : (G).V) (hi : 0 < (G).arity i) :
    factor S (A.row i) 0 (bitsAt (A.place (some false) i) t) (A.rank i) =
      if ∀ q, portEnd G q = i → A.equal t q then 1 else 0 := by
  let w' := bitsAt (A.place (some false) i) t
  have h : (∀ s, external S (A.row i) (A.rank i) s →
      ∀ l : Fin ((label S (A.row i) (A.rank i)).width 0 s), w' false (A.rank i) s l = w' true (A.rank i) s l) ↔
      ∀ q, portEnd G q = i → A.equal t q := by
    have read' (q : slots x ⊕ slots y) (hq : portEnd G q = i) (b : Bool) :
        w' b (A.rank i) (stub p (boundaryEnd G q)) (p.toSeating.ends (boundaryEnd G q)).2.val =
          t (A.route (copy G b q)) := by
      unfold w'
      rw [← hq]
      exact A.copy_at t q b
    constructor
    · intro hc q hq
      let s := stub p (boundaryEnd G q)
      have hs : (p.toSeating.ends (boundaryEnd G q)).1 = (p.vertex i, s) := by
        rw [old, station_boundary, hq]
      have hn : external S (A.row i) (A.rank i) s := (A.raw_external hi s).mpr (by
        rw [← hs]; exact (p.no_peer _).mpr ⟨q, rfl⟩)
      let j := (p.toSeating.ends (boundaryEnd G q)).2.cast
        ((congrArg (S.width r) hs).trans (A.raw_length hi s).symm)
      exact (read' q hq false).symm.trans ((hc s hn j).trans (read' q hq true))
    · intro hc s hs j
      let z : S.Pin r := ⟨(p.vertex i, s), j.cast (A.raw_length hi s)⟩
      obtain ⟨q, hq⟩ := (p.no_peer (p.toSeating.ends.symm z)).mp (by
        rw [Equiv.apply_symm_apply]; exact (A.raw_external hi s).mp hs)
      have he := p.toSeating.ends.eq_symm_apply.mp hq
      have hiq : portEnd G q = i := by
        apply p.vertex.injective
        rw [← station_boundary, ← p.end_station, he]
      have eq := (read' q hiq false).trans ((hc q hiq).trans (read' q hiq true).symm)
      rw [stub, he] at eq
      exact eq
  have hn : slot S (A.row i) (A.rank i) ≠ 0 := (A.slot_eq i hi).trans_ne (A.mobile_ne i)
  unfold factor
  simp only [ite_eq_right hn, ite_true]
  exact if_congr h rfl rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
end

/-! # Evaluating all the rows of a group -/

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
open Finset

variable (t : (scheme S m d a k u).Pin (encode S w) → Bool)
  (hn : ∀ v, P.diagram.arity v = 0 → ∀ z, Transcript.sample (P.diagram.table v) z = 1)

private theorem copy_prod (i : (G).V) :
    (∏ q : {q // portEnd G q = i}, A.contribution t (.inr q.val)) =
      if ∀ q, portEnd G q = i → A.equal t q then 1 else 0 := by
  split
  · rename_i h
    exact prod_eq_one fun q _ => (A.copy_value t _).trans (ite_eq_left (h _ q.2))
  · rename_i h
    push Not at h
    obtain ⟨q, hq, he⟩ := h
    refine prod_eq_zero (mem_univ (⟨q, hq⟩ : {q // portEnd G q = i})) ?_
    exact (A.copy_value t q).trans (ite_eq_right he)

abbrev position (q : (E).V) := A.seat (C.seat bin q)

theorem pos_real (i : (G).V) : A.position (.inl i) = A.place none i := rfl
theorem pos_copy (q : slots x ⊕ slots y) : A.position (.inr q) = A.place (some false) (portEnd G q) :=
  congrArg (fun k => ((A.address (portEnd G q)).1, (A.address (portEnd G q)).2, k)) A.zero

def piece (v : (N).Vtx) (q : (E).V) : F := if A.position q = v then A.contribution t q else 1
def block (v : (N).Vtx) (i : (G).V) : F :=
  A.piece t v (.inl i) * ∏ q : {q // portEnd G q = i}, A.piece t v (.inr q.val)

private theorem pieces (v : (N).Vtx) :
    (∏ i, A.block t v i) = ∏ q, A.piece t v q := by
  unfold block
  rw [prod_mul_distrib, Fintype.prod_fiberwise (portEnd G) (fun q => A.piece t v (.inr q))]
  exact (Fintype.prod_sum_type (A.piece t v)).symm

private theorem block_eq (v : (N).Vtx) (i : (G).V) : A.block t v i =
    (if A.place none i = v then A.contribution t (.inl i) else 1) *
    (if A.place (some false) i = v then if ∀ q, portEnd G q = i → A.equal t q then 1 else 0 else 1) := by
  unfold block piece
  rw [pos_real]
  congr 1
  have he (q : {q // portEnd G q = i}) : A.position (.inr q.val) = A.place (some false) i := by
    rw [pos_copy, q.property]
  simp only [he, prod_ite_irrel, prod_const_one, A.copy_prod]

include hn in
theorem neutral {q : (E).V} (h : (E).arity q = 0) : A.contribution t q = 1 := by
  rcases q with i|q
  · unfold contribution
    rw [← Function.comp_assoc t, ← Function.comp_assoc t, factor_real]
    exact hn i h (fun u => t (A.route (real G ((G).portEquiv ⟨i, u⟩))))
  · exact ((by decide : 2 ≠ 0) h).elim

private theorem eq_place {v : (N).Vtx} {i : (G).V} {b : Option Bool}
    (ha : A.address i = (v.1, v.2.1)) : A.place b i = v ↔ A.idSlot b i = v.2.2 :=
  ⟨fun h => congrArg (fun q : (N).Vtx => q.2.2) h, fun h =>
    Prod.ext (Prod.mk.inj ha).1 (Prod.ext (Prod.mk.inj ha).2 h)⟩

include hn in
private theorem active {v : (N).Vtx} {i : (G).V} (hi : A.block t v i ≠ 1) :
    0 < (G).arity i ∧ A.address i = (v.1, v.2.1) := by
  constructor
  · by_contra! h
    have hz : (G).arity i = 0 := Nat.eq_zero_of_le_zero h
    have he : ∀ q, portEnd G q = i → A.equal t q := by
      intro q hq
      have hpos := live p (boundaryEnd G q)
      rw [station_boundary, hq, hz] at hpos
      exact (lt_irrefl _ hpos).elim
    rw [A.block_eq, A.neutral t hn (q := .inl i) hz, ite_eq_left he, ite_self, ite_self, one_mul] at hi
    exact hi rfl
  · by_contra h
    have hv b : A.place b i ≠ v := fun e => h (congrArg (fun q : (N).Vtx => (q.1, q.2.1)) e)
    exact hi (by rw [A.block_eq, ite_eq_right (hv _), ite_eq_right (hv _), one_mul])

private theorem block_factor {v : (N).Vtx} {i : (G).V} (hi : 0 < (G).arity i)
    (ha : A.address i = (v.1, v.2.1)) :
    A.block t v i = factor S (atRow (w := w) v) v.2.2 (bitsAt v t) (A.rank i) := by
  rw [block_eq]
  have h : A.place none i ≠ A.place (some false) i := fun h =>
    A.mobile_ne i (congrArg (fun v : (N).Vtx => v.2.2) h)
  by_cases hf : A.place (some false) i = v
  · subst v
    rw [ite_eq_right h, ite_eq_left rfl, one_mul]
    exact (A.check_value t i hi).symm
  rw [ite_eq_right hf, mul_one]
  by_cases he : A.place none i = v
  · subst v
    rw [ite_eq_left rfl]
    exact (A.row_value t i hi).symm
  rw [ite_eq_right he]
  have h₁ : v.2.2 ≠ 0 := fun e => hf ((A.eq_place ha).mpr e.symm)
  have h₂ : v.2.2 ≠ A.mobile i := fun e => he ((A.eq_place ha).mpr e.symm)
  have h₃ : slot S (atRow (w := w) v) (A.rank i) = A.mobile i := by
    unfold atRow
    rw [← ha]
    exact A.slot_eq i hi
  simp only [factor, h₃, ite_eq_right (A.mobile_ne i), ite_eq_right h₁, ite_eq_right h₂]

include hn in
theorem product (v : (N).Vtx) : (N).table out v (t ∘ (N).port out v) = ∏ q, A.piece t v q := by
  rw [table_factor, ← pieces]
  symm
  refine prod_bij_ne_one (fun i _ _ => A.rank i) (fun _ _ _ => mem_univ _) ?_ ?_ ?_
  · intro i _ hi j _ hj he
    obtain ⟨h₁, h₂⟩ := A.active t hn hi
    obtain ⟨k₁, k₂⟩ := A.active t hn hj
    exact A.one i j h₁ k₁ (A.cell.injective (h₂.trans k₂.symm)) he
  · intro j _ hj
    have h : slot S (atRow (w := w) v) j ≠ 0 := fun h => hj (ite_eq_left h)
    obtain ⟨i, hi, hv, rfl⟩ := A.appears _ _ h
    exact ⟨i, mem_univ _, (A.block_factor t hi hv).trans_ne hj, rfl⟩
  · intro i _ hi
    obtain ⟨h₁, h₂⟩ := A.active t hn hi
    exact A.block_factor t h₁ h₂

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
end

/-! # Presenting the merged diagram -/

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

open Finset

variable (sep : (Cells.before P).Separated (C.seat bin))
  (hn : ∀ v, P.diagram.arity v = 0 → ∀ z, Transcript.sample (P.diagram.table v) z = 1)

include hn in
private theorem occupied (v : (C.stations bin).V) (t : (N).Pin out → Bool) :
    (N).table out (A.vertex v) (t ∘ (N).port out (A.vertex v)) =
      (C.stations bin).weight v (t ∘ A.ends sep ∘ .inl) (t ∘ A.ends sep ∘ .inr) := by
  rw [A.product t hn]
  let l : (C.grouped bin).End → Bool := t ∘ A.ends sep
  have he : l ∘ sep.ends = t ∘ A.route := funext fun q => congrArg t (A.ends_at sep q)
  have h := sep.weight v.val l
  simp only [← Function.comp_assoc l, he] at h
  refine Eq.trans ?_ h.symm
  unfold piece
  rw [← prod_filter]
  refine prod_subtype _ (fun q => ?_) (A.contribution t)
  simp only [mem_filter, mem_univ, true_and]
  exact A.seat.injective.eq_iff

include hn sep in
private theorem vacant (v : (N).Vtx) (hv : v ∉ Set.range A.vertex) (t : (N).LocalPin out v → Bool) :
    (N).table out v t = 1 := by
  let z : (N).Pin out → Bool := fun _ => false
  have ht : t = z ∘ (N).port out v := by
    funext i
    obtain ⟨j, hj⟩ := (A.ends sep).surjective ((N).port out v i)
    exact (hv ⟨_, (A.station sep j).symm.trans (congrArg (fun q : (N).Pin out => q.1.1) hj)⟩).elim
  rw [ht, A.product z hn]
  refine prod_eq_one fun q _ => ?_
  unfold piece
  split
  · rename_i he
    apply A.neutral z hn
    apply sep.zero
    by_contra! hc
    exact hv ⟨⟨_, Nat.pos_of_ne_zero hc⟩, he⟩
  · rfl

def seating : Sphere.Print.Seating (N) out (C.stations bin) where
  vertex := A.vertex
  ends := A.ends sep
  station := A.station sep
  value t v := A.occupied sep hn v t
  empty v hv t := A.vacant sep hn v hv t

variable (hd : p.Directed)

private theorem at_ends (q : (E).End) :
    (A.seating sep hn).seat.ends (sep.ends q) = A.route q := by
  rw [Sphere.Print.Seating.ends_eq]
  exact A.ends_at sep q

def present : (N).Presentation out (C.stations bin) where
  toSeating := (A.seating sep hn).seat
  proper := A.proper hd
  input i := by
    change (N).peer out ((A.seating sep hn).seat.ends (sep.ends (boundaryEnd E (.inl i)))).1 = none
    rw [at_ends]
    exact A.outside (.inl i)
  output i := by
    change (N).peer out ((A.seating sep hn).seat.ends (sep.ends (boundaryEnd E (.inr i)))).1 = none
    rw [at_ends]
    exact A.outside (.inr i)
  internal i := by
    obtain ⟨e, rfl⟩ := sep.edges.surjective i
    change (N).Joins out ((A.seating sep hn).seat.ends (sep.ends (.inl (.inr e))))
      ((A.seating sep hn).seat.ends (sep.ends (.inr (.inr e))))
    rw [at_ends, at_ends]
    exact ⟨(A.internal e).1.1, (A.internal e).2.2.2⟩

theorem directed : (A.present sep hn hd).Directed := by
  intro i
  obtain ⟨q, rfl⟩ := sep.ends.surjective i
  rw [show (A.present sep hn hd).toSeating.ends (sep.ends q) = A.route q from A.at_ends sep hn q, A.direction hd]
  cases q <;> rfl

variable (R : ℕ)
def padded := (A.present sep hn hd).pad (A.directed sep hn hd) A.resolved R (C.loopless bin)

theorem padded_directed : (A.padded sep hn hd R).Directed :=
  (A.present sep hn hd).pad_directed (A.directed sep hn hd) A.resolved R (C.loopless bin)

theorem padded_end (i : slots x ⊕ slots y) :
    (A.padded sep hn hd R).toSeating.ends (boundaryEnd _ i) = (N).liftPad out R false (A.route (copy G false i)) := by
  have he : boundaryEnd ((C.stations bin).pad R) i = (C.stations bin).insertEnds R (sep.ends (copy G false i)) := by
    cases i <;> rfl
  rw [he, padded, Scheme.Presentation.pad_ends, Scheme.Presentation.pad_old]
  exact congrArg _ (A.at_ends sep hn (copy G false i))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel.Manifest
end

/-! # Resolving original contacts on the child host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
open Coloring Packing Rounds Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
  {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
  {g H T a u : ℕ} {L θ : ℝ} {ha : a < D.scheme.h} (G : p.Plan ha g H T)

local notation "n" => D.scheme.h - a
local notation "old" => P.diagram
local notation "suffixOf" => (row (P := P) (ha := ha))
local notation "colony" => G.group.Colony
local notation "page" => D.sheet a ha g H T r
local notation "base" => (parent (p := p))
local notation "top" => (prefixOf (P := P) (ha := ha))
local notation "atSheet" => (sheetAt (p := p) (ha := ha) (g := g) (H := H) (T := T))

theorem childPresent (p : D.Presents r P) (ha : a < D.scheme.h) :
    Child.Presents P.adj p.host (D.childInput a ha r) := by
  have h : Group.Presents (D.groups a ha.le r) p.host P.adj P.adj (P.groupLoad a ha.le) D.load :=
    ⟨p.live, p.closed, p.edge, p.core, p.group_load ha⟩
  exact Child.presents h false

local notation "nav" => D.binNav a ha g r
local notation "host" => Child.host p.host n

theorem reach (hg : 0 < g) {v w : Site P.V n} (hw : w ∈ near P.adj g v) :
    nav (host v) (Child.index nav (host v) (host w)) = host w :=
  (childPresent p ha).nav hg v w ((mem_cube ..).mpr ⟨v, near_self .., v, near_self .., hw⟩)

variable (hH : 0 < H)
local notation "frame" => D.childFrame a ha g H T r hH u
local notation "back" => Equiv.symm (Match.rowIndex D.scheme.m (n + 1))

abbrev addr (v : (old).V) := G.cellAddr (G.col v)

abbrev rewriteTarget (v : (old).V) : B D.scheme.e → (Parcel.destination (D.childD a g) (Sheet.slots H) u).obj :=
  Sheet.target D (atSheet v) H T hH u _ (fun s => page (D.nav r (base v) s) (top v))
    (fun l s l' => Child.index nav (back (base v, l)) (back (D.nav r (base v) s, l'))) (suffixOf v)

theorem entry (hroom : G.Room u) (i : (old).V) (hi : 0 < (old).arity i) :
    Parcel.rowAt frame (G.addr i) (G.rank u i) =
      (Sheet.number H (some (Sheet.bins D (atSheet i) H T hH (suffixOf i))),
        (atSheet i (suffixOf i)).1, rewriteTarget (p := p) (ha := ha) (g := g) (T := T) hH i) := by
  simp only [addr, cell_parts, Parcel.rowAt, childFrame, Equiv.apply_symm_apply, Sheet.record]
  rw [G.found hroom i hi]

theorem appears (v : B (D.childM a) × B a) (b : B u)
    (hb : Parcel.slot D.scheme (Parcel.rowAt frame v) b ≠ 0) :
    ∃ i, 0 < (old).arity i ∧ G.addr i = v ∧ G.rank u i = b := by
  obtain ⟨v, l⟩ := v
  obtain ⟨⟨v, z⟩, rfl⟩ := (back).surjective v
  simp only [Parcel.slot, Parcel.rowAt, childFrame, Equiv.apply_symm_apply, Sheet.record] at hb
  cases h : Sheet.find D (page v l) u z b with
  | none => rw [h] at hb; exact (hb rfl).elim
  | some j =>
    obtain ⟨i, hi, he, hr, _⟩ := (G.eligible v l z b j).mp (Sheet.find_spec _ _ _ _ _ _ h)
    exact ⟨i, hi, he, hr⟩

variable {i j : P.diagram.V} {s t : B D.scheme.e}

theorem adjacency (hp : 0 < D.scheme.width r.1 (p.pres.vertex i, s))
    (he : D.scheme.peer r.1 (p.pres.vertex i, s) = some (p.pres.vertex j, t)) :
    (∃ e, (old).source e = i ∧ (old).target e = j) ∨ (∃ e, (old).source e = j ∧ (old).target e = i) := by
  obtain ⟨e, b, hb⟩ := p.pres.linked (q := ⟨(p.pres.vertex i, s), ⟨0, hp⟩⟩) (by simp [he])
  have h : (p.pres.tip e b).1 = (p.pres.vertex i, s) := congrArg Sigma.fst hb
  have h' : (p.pres.tip e (!b)).1 = (p.pres.vertex j, t) :=
    Option.some.inj ((p.pres.link_tip e b).1.symm.trans (h ▸ he))
  have h₁ := p.pres.vertex.injective ((p.pres.at_tip e b).symm.trans (congrArg Prod.fst h))
  have h₂ := p.pres.vertex.injective ((p.pres.at_tip e (!b)).symm.trans (congrArg Prod.fst h'))
  cases b
  · exact .inl ⟨e, h₁, h₂⟩
  · exact .inr ⟨e, h₂, h₁⟩

private theorem old_target (he : D.scheme.peer r.1 (p.pres.vertex i, s) = some (p.pres.vertex j, t)) :
    ∃ b, (D.scheme.decode (atSheet i (suffixOf i)).1).peer 0 s = some (b, 0, t) ∧
      D.nav r (base i) b = base j ∧ top i = top j ∧ suffixOf i = suffixOf j := by
  rw [p.vertex i, p.vertex j] at he
  obtain ⟨⟨b, c, l⟩, h₁, h₂⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨hv, hl⟩ := Prod.mk.inj h₂
  have hc := (Prod.mk.inj (Prod.mk.inj hv).2).2
  have hp := (cellIndex D.scheme.h).injective ((Prod.mk.inj (Prod.mk.inj hv).2).1)
  change c = 0 at hc
  change l = t at hl
  subst c; subst l
  refine ⟨b, ?_, (Prod.mk.inj hv).1, congrArg (fun j => cellIndex _ (ancestor ha.le j)) hp,
    congrArg (fun j => cellIndex _ (suffix a j)) hp⟩
  rw [row_label, p.vertex i]
  exact h₁

variable (hg : 0 < g) (hT : 0 < T) (ok : P.Ready g H T L θ)
  (hs : (P.seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ (D.scheme.h - a))
local notation "C" => G.cells hg hH hT ok hs
local notation "bin" => G.bin hg hH hT ok hs

theorem target_eq (he : D.scheme.peer r.1 (p.pres.vertex i, s) = some (p.pres.vertex j, t)) :
    rewriteTarget (p := p) (ha := ha) (g := g) (T := T) hH i s =
      (Child.index nav (G.addr i).1 (G.addr j).1, Sheet.number H (some (bin j)), G.rank u j) := by
  obtain ⟨b, h₁, h₂, h₃, h₄⟩ := old_target (ha := ha) (g := g) (H := H) (T := T) he
  unfold rewriteTarget Sheet.target
  rw [h₁]
  dsimp only
  rw [G.row_interval i, h₂, h₃, h₄]
  change (Child.index nav (G.addr i).1 (back (base j, (atSheet j (suffixOf j)).2.2)),
    Sheet.number H (some (Sheet.bins D (atSheet j) H T hH (suffixOf j))), Sheet.rank D (atSheet j) u (suffixOf j)) = _
  rw [G.row_interval j, G.row_rank j, G.row_bin hg hH hT ok hs j]
  rfl

def manifest (hroom : G.Room u) : Parcel.Manifest (C) p.pres bin frame where
  cell := G.cellAddr
  number := Sheet.number H
  zero := Sheet.number_none H
  rank := G.rank u
  one := G.unique_rank hroom
  first i := by rw [p.vertex]
  slot_eq i hi := by
    change (Parcel.rowAt frame (G.addr i) (G.rank u i)).1 = _
    rw [G.entry hH hroom i hi, G.row_bin hg hH hT ok hs]
  pattern_eq i hi := by
    change D.scheme.decode (Parcel.rowAt frame (G.addr i) (G.rank u i)).2.1 = _
    rw [G.entry hH hroom i hi]
    exact row_label (g := g) (H := H) (T := T) i
  appears := G.appears hH
  index := Child.index nav
  stay i := by
    have h : nav i 0 = i := Neighborhood.origin
    simp only [Child.index, Child.select, h, decide_true, ite_true]
  self _ := Neighborhood.origin
  peer i s j t hp he := by
    change (Parcel.rowAt frame (G.addr i) (G.rank u i)).2.2 s = _ ∧ _
    rw [G.entry hH hroom i (Parcel.Manifest.positive hp)]
    refine ⟨G.target_eq hH hg hT ok hs he, ?_⟩
    have hloc : ((C).site ((C).cell j)).1 ∈ near P.adj g ((C).site ((C).cell i)).1 ∧
        ((C).site ((C).cell i)).2 = ((C).site ((C).cell j)).2 := by
      rcases adjacency hp he with ⟨e, rfl, rfl⟩|⟨e, rfl, rfl⟩
      · exact ⟨((C).edge e).2, ((C).edge e).1.symm⟩
      · exact ⟨(C).sym _ _ ((C).edge e).2, ((C).edge e).1⟩
    exact ⟨reach (p := p) (ha := ha) hg hloc.1, congrArg (cellIndex a) hloc.2⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents.Plan
end
