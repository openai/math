import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Origin
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.Ledger.Quota

/-!
# Reading the geometry from a finite tag and length words

Each output width digit uses the tag and just one digit of each length.
Thus the cost is linear in the length of a word for fixed tag, station and
span alphabets. The digit convention is arbitrary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Blueprint
open Coloring
open scoped Classical

variable {T X Y : Type} {w d e k : ℕ}

/-- The distinguished word holds the common internal width. -/
abbrev LengthKey (k : ℕ) := Option (B k × Bool)
abbrev ReadIn (X : Type) (k b : ℕ) := X ⊕ (LengthKey k × Fin b)
abbrev ReadOut (Y : Type) (w e b : ℕ) := Y ⊕ (B w × B e × Fin b)

def lengths (u : ℕ) (size : Option (B k) → Bool → ℕ) : LengthKey k → ℕ
  | none => u
  | some (v, s) => size (some v) s

variable (emb : T ↪ (X → Bool)) (blue : T → Blueprint w d e k)
  (info : T → Y → Bool) (outer : Bool ↪ B e) (b : ℕ) (bit : ℕ → Fin b → Bool)

def readIn (t : T) (u : ℕ) (size : Option (B k) → Bool → ℕ) : ReadIn X k b → Bool :=
  Sum.elim (emb t) (fun h => bit (lengths u size h.1) h.2)

def readOut (t : T) (u : ℕ) (size : Option (B k) → Bool → ℕ) : ReadOut Y w e b → Bool :=
  Sum.elim (info t) (fun h => bit ((blue t h.1).width u outer size h.2.1) h.2.2)

private def sliceCode : T × (LengthKey k → Bool) ↪ (X ⊕ LengthKey k → Bool) where
  toFun p := Sum.elim (emb p.1) p.2
  inj' _ _ h := Prod.ext (emb.injective (funext fun i => congrFun h (.inl i)))
    (funext fun i => congrFun h (.inr i))

private def digit (v : B w) (s : B e) (j : Fin b) (t : T × (LengthKey k → Bool)) :=
  let o := blue t.1 v
  let side h := o.name.elim (bit 0 j) fun i => t.2 (some (i, h))
  if (o.peer s).isSome then t.2 none else
    if s = outer false then side false else if s = outer true then side true else bit 0 j

private theorem digit_eq (v : B w) (s : B e) (j : Fin b)
    (t : T) (u : ℕ) (size : Option (B k) → Bool → ℕ) (hzero : ∀ h, size none h = 0) :
    digit blue outer b bit v s j (t, fun l => bit (lengths u size l) j) =
      bit ((blue t v).width u outer size s) j := by
  unfold digit Outline.width
  dsimp only
  split_ifs <;> cases hn : (blue t v).name <;> simp [lengths, hzero]

variable [Fintype T] [Fintype X]

/-- Uniform work bound for one metadata bit or width digit. -/
def readCost (T X : Type) [Fintype T] [Fintype X] (k : ℕ) :=
  (3 * Fintype.card X + 2) * Fintype.card T + 1 +
  ((3 * Fintype.card (X ⊕ LengthKey k) + 2) * Fintype.card (T × (LengthKey k → Bool)) + 1)

theorem read_bit (i : ReadOut Y w e b) :
    ∃ g : BitFormula (ReadIn X k b), g.cost ≤ readCost T X k ∧
      ∀ t u (size : Option (B k) → Bool → ℕ), (∀ h, size none h = 0) →
        g.eval (readIn emb b bit t u size) = readOut blue info outer b bit t u size i := by
  rcases i with i|⟨v, s, j⟩
  · obtain ⟨g, hg, hc⟩ := finite_formula emb (fun t => info t i)
    refine ⟨g.rename Sum.inl, ?_, ?_⟩
    · rw [BitFormula.cost_rename]
      exact hc.trans (Nat.le_add_right _ _)
    · intro t u size _
      rw [BitFormula.eval_rename]
      exact hg t
  · obtain ⟨g, hg, hc⟩ := finite_formula (sliceCode emb) (digit blue outer b bit v s j)
    let f : X ⊕ LengthKey k → ReadIn X k b := Sum.map id (fun l => (l, j))
    refine ⟨g.rename f, ?_, ?_⟩
    · rw [BitFormula.cost_rename]
      exact hc.trans (Nat.le_add_left _ _)
    · intro t u size hz
      have hf : readIn emb b bit t u size ∘ f =
          sliceCode emb (t, fun l => bit (lengths u size l) j) := by
        funext x
        cases x <;> rfl
      rw [BitFormula.eval_rename, hf, hg]
      exact digit_eq blue outer b bit v s j t u size hz

/-- The same family of formulas works for all tags and all length words. -/
theorem read_net [Fintype Y] :
    ∃ g : ReadOut Y w e b → BitFormula (ReadIn X k b),
      (∀ t u size, (∀ h, size none h = 0) → ∀ i,
        (g i).eval (readIn emb b bit t u size) = readOut blue info outer b bit t u size i) ∧
      (∀ i, (g i).cost ≤ readCost T X k) ∧
      (∑ i, (g i).cost) ≤ readCost T X k * (Fintype.card Y + 2 ^ w * 2 ^ e) * (b + 1) := by
  choose g hg he using read_bit emb blue info outer b bit
  refine ⟨g, fun t u size h i => he i t u size h, hg, ?_⟩
  calc
    _ ≤ ∑ _ : ReadOut Y w e b, readCost T X k := Finset.sum_le_sum fun i _ => hg i
    _ = readCost T X k * (Fintype.card Y + 2 ^ w * 2 ^ e * b) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, ReadOut,
        Fintype.card_sum, Fintype.card_prod, B, Fintype.card_fin]
      ring
    _ ≤ _ := by
      rw [mul_assoc (readCost T X k)]
      gcongr
      rw [add_mul]
      exact add_le_add (Nat.le_mul_of_pos_right _ (by omega)) (Nat.mul_le_mul_left _ (by omega))

/-- One-hot peer indices and holder locations accompany the role and direction bits. -/
abbrev Flags (w d e k : ℕ) :=
  B w ⊕ (B w × Option (B k)) ⊕ (B w × B e) ⊕
    (B w × B e × Option (B d × B 0 × B e)) ⊕ (B k × B w)

def flags (a : Blueprint w d e k) : Flags w d e k → Bool
  | .inl i => (a i).live
  | .inr (.inl (i, h)) => decide ((a i).name = h)
  | .inr (.inr (.inl (i, j))) => (a i).direction j
  | .inr (.inr (.inr (.inl (i, j, h)))) => decide ((a i).peer j = h)
  | .inr (.inr (.inr (.inr (h, i)))) => decide (a.find h = i)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Blueprint
end

/-! # Genuine prints register each old exterior holder -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K X Z J I : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ r₀ t₀ : ℕ} {W : ℝ} {P : Input F x y S.h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam S.m d S.h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I (B S.k) P.Occupied P.grid.Seam Z X}
  {G : Record F (M * r) (M * t) P.Occupied P.grid.Seam K (B S.k)}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option (B S.k) → Bool → ℕ} {old : P.V ↪ B S.m}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

variable {tape : S.format.obj} {pres : S.Presentation tape P.diagram}

variable {G₀ : (Key.share s Q).Geo P k} (B : U.Physical G₀ π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)
  (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)
  (keeps : NamedKeeps Q left right hm pres a.coord)
  (hl : B.rules.left = left) (hr : B.rules.right = right)

include H keeps hl hr in
theorem origin (dir : pres.Directed) :
    U.Origin S tape data status (B.select.write p) pres (B.shows p hw) := by
  have ke : Keeps Q B.rules.left B.rules.right pres a.coord := by rw [hl, hr]; exact keeps.keeps
  refine ⟨rfl, dir, B.retains p (B.frame p hw) rfl pres ke, ?_, H.injection keeps dir G₀.count, B.presentAt p⟩
  intro e v
  obtain ⟨i, hpos, hleft, hright, hn, hi⟩ := keeps e
  have he : Sum.elim Q.left Q.right e = i := by
    cases e with
    | inl e => exact (left.mem i e).mp (by rw [hleft]; exact (P.diagram.mem_extLeft _ _).mpr rfl)
    | inr e => exact (right.mem i e).mp (by rw [hright]; exact (P.diagram.mem_extRight _ _).mpr rfl)
  have hv : v = pres.vertex (Packing.portEnd P.diagram e) := Payload.owner pres e
  rw [← hv] at hpos hn
  have heq := eq_of_heq (H.read (a.coord i.1))
  rw [Atlas.fill_at, hpos] at heq
  have hx : namedIndex (U.namesAt ((data v.1).2 v.2.1)) v.2.2 = i.2.val := by
    rw [namesAt, heq, Option.elim_some]
    exact named_index hm i _ hn hi
  refine (B.boundary_child p hw e i he).trans ?_
  unfold childFor
  have hi' := i.2.isLt.trans_le (G₀.count i.1)
  exact congrArg (fun j => U.slot (.inl (.inl (true, j))))
    (Fin.ext (by simp only [Fin.val_castLE, hx, Nat.mod_eq_of_lt hi']))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end

/-! # Recovering the span widths of a genuine print from its blueprint -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Packing Rounds
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (data : U.rows.obj) (status : (Children.Header S.m d).obj)
    (choice : U.selectors.obj)

variable {Y : U.template.format.obj}
local notation "A" => U.canonical S x Y

private theorem paired_width (v : B U.labelBits) (s : B U.spanBits)
    (hs : (U.engine.decode v).peer 0 s ≠ none) : (U.engine.decode v).width 0 s = u := by
  cases h : U.read v with
  | none => simp [engine, h, Star.vacant] at hs
  | some a =>
    simp only [engine, h, Option.map_some, Option.getD_some, Star.pattern] at hs ⊢
    rcases a.active U.ix u (Or.inr hs) with ⟨b, rfl⟩|⟨b, l, i, t, m, rfl, hi, hj⟩
    · rw [Star.desc_ext] at hs
      exact (hs rfl).elim
    · rw [a.desc_link U.ix u hi i hj]

variable {a b : Wire} {G : Diagram F a b} {Q : LocalTerm F a b U.template.scheme.h u}
    (p : S.Presentation x G) (P : U.template.Shows Y Q)

namespace Origin
variable {S U x data status choice p P} (f : U.Origin S x data status choice p P)
include f

private theorem exterior : Geometry.Widths G U.template.scheme (Y).1 (U.holder S x A p) U.outer := by
  apply Geometry.widths_of_retains f.retains
  intro i
  rw [f.address, Payload.owner]

theorem matching (v : U.Actors S) :
    (U.localAt S A v).Matches u U.outer (S.extWidth (U.originalAt S x v))
      (U.engine.decode (U.printedAt S Y v)) := by
  let o := U.localAt S A v
  let k₀ := U.printedAt S Y v
  have eq : o = U.original S (U.originalAt S x v) k₀ := U.local_canonical S x Y v
  have hp : o.peer = (U.engine.decode k₀).peer 0 := congrArg Geometry.Outline.peer eq
  refine ⟨hp, congrArg Geometry.Outline.direction eq, ?_⟩
  funext s
  change o.width u U.outer _ s = (U.engine.decode k₀).width 0 s
  unfold Geometry.Outline.width
  by_cases free : o.peer s = none
  swap
  · rw [ite_eq_left (Option.isSome_iff_ne_none.mpr free)]
    exact (U.paired_width S k₀ s (hp ▸ free)).symm
  rw [free, ite_eq_right (by simp)]
  have hv : v.2.2 = 0 := Fin.eq_zero _
  have hw : U.template.scheme.borderLen (Y).1 (v, s) = (U.engine.decode k₀).width 0 s := by
    have no : U.template.scheme.peer (Y).1 (v, s) = none := by
      unfold Scheme.peer
      apply Option.map_eq_none_iff.mpr
      change (U.engine.decode k₀).peer v.2.2 s = none
      rw [hv, ← hp]
      exact free
    rw [Scheme.borderLen, ite_eq_left no]
    change (U.engine.decode k₀).width v.2.2 s = _
    rw [hv]
  refine Eq.trans ?_ ((f.exterior v s).symm.trans hw)
  let out : Bool ↪ B U.spanBits := U.outer
  let u₀ : B S.ℓ := U.originalAt S x v
  change (if s = out false then S.extWidth u₀ o.name false else
    if s = out true then S.extWidth u₀ o.name true else 0) =
      ∑ i : G.V, if U.holder S x A p i = v then
        if s = out false then (G.extLeft i).length else if s = out true then (G.extRight i).length else 0 else 0
  by_cases hl : s = out false
  · simp only [hl, ite_true]
    exact U.holder_width S x Y A f.registered p f.directed v false
  simp only [hl, ite_false]
  by_cases hr : s = out true
  · simp only [hr, ite_true]
    exact U.holder_width S x Y A f.registered p f.directed v true
  simp only [hr, ite_false, ite_self, Finset.sum_const_zero]

end Origin
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
# Concentration for every accepted geometric proposal

The bounds apply even if a proposal fails the coefficient check.
Only the short quotas and the unchanged exterior wires enter.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Rounds
open scoped Classical
variable {F K : Type} [Field F] [Finite K] {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g σ ν : ℕ} {x y : Wire} {W : ℝ} {P : Input F x y S.h D T R g W}
  (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  {old : P.V ↪ B S.m} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {nav : B S.m → B d → B S.m} (A : Children.Shows P.adj old (nav, status))
  (hdata : ∀ i, (data i).1 = nav i) (hg : g ≤ D ^ k) (c : U.selectors.obj)
  {x₀ : S.format.obj} (p : S.Presentation x₀ P.diagram) (hd : p.Directed)
  {loc : P.Occupied ↪ B S.m × B S.h} {part : Fin ν → P.Occupied → P.Occupied}
  {E H : P.Occupied → ℕ} (a : P.Occupied → U.Tag S g σ ν)

local notation "Y" => U.advance data status c
local notation "C" => Input.terminalExponent g σ
local notation "plan" => U.complete S loc (fun i => Prod.fst (a i))
local notation "net" => U.graph A hdata hg c


private def coverage {I V : Type} [Fintype V]
    (rows : U.template.format.obj) (G : U.Graph S rows V)
    (b : U.Matrix S) (hv : U.Valid S x₀ rows b) (loc : I ↪ B S.m × B S.h)
    (hc : ∀ v : U.Actors S, (U.localAt S b v).live = true → ((U.split v.1).1, v.2.1) ∈ Set.range loc)
    (hf : ∀ v, U.template.frozen rows v = U.fixedChild (U.split v).2) :
    Geometry.Support I (fun i => b (loc i).1 (loc i).2) (fun _ => U.fixedChild)
      (U.admitted S x₀ rows b hv G p hd).term := by
  have eq : U.board S x₀ rows b hv G (U.materialize S x₀ rows b hv p hd) (fun _ => Iff.rfl) =
      U.admitted S x₀ rows b hv G p hd := rfl
  let sup := U.board_support S x₀ rows b hv G (U.materialize S x₀ rows b hv p hd) (fun _ => Iff.rfl)
    loc hc U.fixedChild (fun v _ => hf v.1)
  exact Eq.mp (congrArg (fun E : Geometry.Board (U.revised S) (U.overlay S x₀ rows b) x y u =>
    Geometry.Support I (fun i => b (loc i).1 (loc i).2) (fun _ => U.fixedChild) E.term) eq) sup

private theorem admitted_concentrated {V : Type} [Fintype V]
    (rows : U.template.format.obj) (G : U.Graph S rows V)
    (pass : U.passes S loc part E H (T / u) x₀ rows a)
    (fixed : ∀ v, U.template.frozen rows v = U.fixedChild (U.split v).2)
    (cells : Fintype.card V ≤ D ^ C * Fintype.card P.V)
    (full : ∀ v, (G.adj v).card ≤ D ^ C)
    (core : ∀ v, ((G.adj v).filter (fun w => ¬G.frozen v ∧ ¬G.frozen w)).card ≤ 3)
    (he : (∑ v, (E v : ℝ)) * T ≤ 2 * SphereScale.budget g * ((ν : ℝ) + 1) * W)
    (hh : (∑ v, (H v : ℝ)) * D * T ≤ 3 * (D : ℝ) ^ 5 * W) :
    Concentrated P (U.admitted S x₀ rows plan pass.1 G p hd).term (Geometry.overhead g C) n σ := by
  have support := coverage U p hd rows G plan pass.1 loc (U.complete_support S loc _) fixed
  rw [funext (U.complete_here S loc (fun i => (a i).1))] at support
  have hD : 0 < D := lt_of_lt_of_le (by decide) U.large
  have hv : (Fintype.card P.Occupied : ℝ) * D * T ≤ W := by
    simpa only [Input.Occupied, Fintype.card_coe] using P.occupied
  have totals := Geometry.totals (fun v => (a v).1) (fun _ => U.fixedChild) hD hv he hh pass.2.1 pass.2.2
  exact support.concentrated (P := P) («C» := Input.terminalExponent g σ) (U.admitted_fibers S x₀ rows plan pass.1 G p hd) hD cells core full totals pass.2.2

theorem approved_term (ok : U.passes S loc part E H (T / u) x₀ (U.advance data status c) a)
    (hk : k = Layout.Sharing.allocation g σ)
    (he : (∑ v, (E v : ℝ)) * T ≤ 2 * SphereScale.budget g * ((ν : ℝ) + 1) * W)
    (hh : (∑ v, (H v : ℝ)) * D * T ≤ 3 * (D : ℝ) ^ 5 * W) :
    Concentrated P (U.admitted S x₀ Y plan ok.1 net p hd).term (Geometry.overhead g C) n σ := by
  exact admitted_concentrated U p hd a Y net ok (fun _ => rfl)
    (U.graph_cells A hg hk) (U.graph_fullDegree A hdata hg c hk) (U.graph_coreDegree A hdata hg c) he hh

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Uniform bounds for all profiles of one physical state -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K N X Z J I : Type} [Field F] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ : ℕ} {W : ℝ} {P : Input F x y h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K N m d h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam m d h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I N P.Occupied P.grid.Seam Z X}
  {G : Record F (M * r) (M * t) P.Occupied P.grid.Seam K N}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option N → Bool → ℕ} {old : P.V ↪ B m}
  {data : U.rows.obj} {status : (Children.Header m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

include H in
theorem capacity (bound : P.FinalBounds Q σ j) (sc : Scales g σ D T j b c)
    (ha : M * r = c * b) (hb : M * t = c) (hM : M = SphereScale.chunks σ D) (hk : k = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T)
    (hc : Input.terminalExponent g σ * D * T ≤ u * U.cap) (hz : depth σ D g j (c * b) < 2 ^ z) :
    ∃ (G₀ : (Key.share s Q).Geo P k) (B : U.Physical G₀ π old data status),
      B.rules.left = left ∧ B.rules.right = right ∧
      ∀ p : Layout.Profile s.scene.cell s.scene.level,
        Concentrated P (B.term p) (Input.terminalExponent g σ) n σ ∧
          ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap := by
  subst M k
  let steer := H.parents.steer U.degree
  let G₀ := {bound.geometry sc with steer := steer}
  have hr := (bound.raw sc hb).with_steer steer
  have hs := hr.budgets sc ha hb rfl le_rfl n
  obtain ⟨B, hl, hr⟩ := H.physical G₀ (fun _ => rfl) rfl rfl (fun i => (bound.shape_bound sc i).trans_lt hz)
  refine ⟨G₀, B, hl, hr, fun p => ?_⟩
  have hC : 1 ≤ Input.terminalExponent g σ := by
    have := (Layout.Fanout.exponent_bounds (c := Sharing.radius (Sharing.allocation g σ)) (ℓ := σ) le_rfl).1
    exact le_trans (by omega) this
  have he := G₀.concentrated U.dyadic U.large hs p j U.pos le_rfl hu
  exact ⟨B.concentrated p he, Sharing.Geo.capacity U.dyadic U.large U.pos p he hC hc⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end

/-! # Controlled emission of diagrams with several exterior stations per cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K X Z J I : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ r₀ t₀ : ℕ} {W : ℝ} {P : Input F x y S.h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F r₀ t₀ Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam S.m d S.h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I (B S.k) P.Occupied P.grid.Seam Z X}
  {G : Record F r₀ t₀ P.Occupied P.grid.Seam K (B S.k)}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option (B S.k) → Bool → ℕ} {old : P.V ↪ B S.m}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

variable {tape : S.format.obj} {pres : S.Presentation tape P.diagram}

/-- All profiles share the same decoder. Their scalar, term and exact
physical presentation are drawn from a single terminal tape. -/
def namedRelease (keeps : NamedKeeps Q left right hm pres a.coord) (hn : Nonempty P.V)
    (bound : P.FinalBounds Q σ j) (sc : Scales g σ D T j b c)
    (hr : r₀ = M * r) (ht : t₀ = M * t) (ha : r₀ = c * b) (hb : t₀ = c)
    (hM : M = SphereScale.chunks σ D) (hk : k = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T)
    (hc : Input.terminalExponent g σ * D * T ≤ u * U.cap) (hz : depth σ D g j (c * b) < 2 ^ z) :
    U.NamedRelease pres data status (fun x y => ∑ i, s.value j (Q.init x y i)) σ := by
  apply Classical.choice
  subst r₀ t₀
  obtain ⟨G₀, B, hl, hr, cap⟩ := H.capacity bound sc ha hb hM hk hu hc hz
  have ke : Keeps Q B.rules.left B.rules.right pres a.coord := by rw [hl, hr]; exact keeps.keeps
  exact ⟨{
    I := Layout.Profile s.scene.cell s.scene.level
    finite := Input.FinalBounds.profileType _ _
    select := B.select
    coeff := Layout.Profile.sign
    term := B.term
    value := B.value
    bound := fun i => (cap i).1
    populated := fun i => B.populated i hn
    valid := B.score
    shows := fun i => B.shows i (cap i).2
    retains := fun i => B.retains i (B.frame i (cap i).2) rfl pres ke
    reciprocal := by
      intro v i hi
      simp only [H.graph] at hi ⊢
      exact H.parents.reciprocal v i hi
    nonzero := by
      intro i
      rw [← sign_stamp]
      apply Finset.prod_ne_zero_iff.mpr
      intro v _
      simp [Shapes.sign]
    named := by
      intro p e v
      obtain ⟨i, hpos, hleft, hright, hn, hi⟩ := keeps e
      have he : Sum.elim Q.left Q.right e = i := by
        cases e with
        | inl e => exact (left.mem i e).mp (by rw [hleft]; exact (P.diagram.mem_extLeft _ _).mpr rfl)
        | inr e => exact (right.mem i e).mp (by rw [hright]; exact (P.diagram.mem_extRight _ _).mpr rfl)
      have hv : v = pres.vertex (Packing.portEnd P.diagram e) := Payload.owner pres e
      rw [← hv] at hpos hn
      have heq := eq_of_heq (H.read (a.coord i.1))
      rw [Atlas.fill_at, hpos] at heq
      have hx : namedIndex (U.namesAt ((data v.1).2 v.2.1)) v.2.2 = i.2.val := by
        rw [namesAt, heq, Option.elim_some]
        exact named_index hm i _ hn hi
      refine (B.boundary_child p (cap p).2 e i he).trans ?_
      unfold childFor
      have hi' := i.2.isLt.trans_le (G₀.count i.1)
      exact congrArg (fun j => U.slot (.inl (.inl (true, j))))
        (Fin.ext (by simp only [Fin.val_castLE, hx, Nat.mod_eq_of_lt hi']))
  }⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end

/-! # Measured output plans for terminal sphere configurations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K X Z J I : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ r₀ t₀ ν : ℕ} {W : ℝ} {P : Input F x y S.h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F r₀ t₀ Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam S.m d S.h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I (B S.k) P.Occupied P.grid.Seam Z X}
  {G : Record F r₀ t₀ P.Occupied P.grid.Seam K (B S.k)}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option (B S.k) → Bool → ℕ} {old : P.V ↪ B S.m}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  (H : U.Signal Q left right a π β R₀ G hm index size ext old data status)

open SphereScale (Scales depth)

variable {tape : S.format.obj} {pres : S.Presentation tape P.diagram}

/-- All profiles share the same decoder. Their scalar, term and exact
physical presentation are drawn from a single terminal tape. -/
def measuredRelease (keeps : NamedKeeps Q left right hm pres a.coord) (hn : Nonempty P.V)
    (bound : P.FinalBounds Q σ j) (sc : Scales g σ D T j b c)
    (hr : r₀ = M * r) (ht : t₀ = M * t) (ha : r₀ = c * b) (hb : t₀ = c)
    (hM : M = SphereScale.chunks σ D) (hk : k = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T)
    (hc : Input.terminalExponent g σ * D * T ≤ u * U.cap) (hz : depth σ D g j (c * b) < 2 ^ z)
    (dir : pres.Directed) (credit : P.Occupied → Geometry.Credits g σ D ν)
    (hcount : ∀ v, D ^ 5 * Fintype.card {i : Fin (s.scene.cell v).stations.length //
        (item s.scene.cell ⟨v, i⟩).label.role = .collector} ≤ (credit v).time (Fin.last ν))
    (henergy : ∀ v, Geometry.clip ν (j * SphereScale.energy σ D (c * b)) (s.tally j Role.collected v) ≤
        (credit v).power (Fin.last ν)) :
    U.MeasuredRelease pres data status (fun x y => ∑ i, s.value j (Q.init x y i)) σ a.coord credit := by
  apply Classical.choice
  subst r₀ t₀ M k
  let steer := H.parents.steer U.degree
  let geo := {bound.geometry sc with steer := steer}
  have raw := (bound.raw sc hb).with_steer steer
  have budgets := raw.budgets sc ha hb rfl le_rfl n
  obtain ⟨B, hl, hr⟩ := H.physical geo (fun _ => rfl) rfl rfl (fun i => (bound.shape_bound sc i).trans_lt hz)
  have hC : 1 ≤ Input.terminalExponent g σ := by
    have := (Layout.Fanout.exponent_bounds (c := Sharing.radius (Sharing.allocation g σ)) (ℓ := σ) le_rfl).1
    exact le_trans (by omega) this
  have conc (p : Layout.Profile s.scene.cell s.scene.level) :=
    geo.concentrated U.dyadic U.large budgets p j U.pos le_rfl hu
  have hw (p : Layout.Profile s.scene.cell s.scene.level) :=
    Sharing.Geo.capacity U.dyadic U.large U.pos p (conc p) hC hc
  have auth (p : Layout.Profile s.scene.cell s.scene.level) := H.origin B p (hw p) keeps hl hr dir
  have hf (i : Place s.scene.cell) (hi : geo.frozen i) :
      (item s.scene.cell i).label.role = .collector ∧ ¬thinStation (item s.scene.cell i) := by
    change (item s.scene.cell i).label.role = .collector at hi
    exact ⟨hi, by simp [thinStation, hi]⟩
  exact ⟨{
    I := Layout.Profile s.scene.cell s.scene.level
    finite := Input.FinalBounds.profileType _ _
    select := B.select
    coeff := Layout.Profile.sign
    term := B.term
    value := B.value
    bound := fun i => B.concentrated i (conc i)
    populated := fun i => B.populated i hn
    valid := B.score
    shows := fun i => B.shows i (hw i)
    retains := fun i => (auth i).retains
    reciprocal := by
      intro v i hi
      simp only [H.graph] at hi ⊢
      exact H.parents.reciprocal v i hi
    nonzero := by
      intro i
      rw [← sign_stamp]
      apply Finset.prod_ne_zero_iff.mpr
      intro v _
      simp [Shapes.sign]
    named := fun i => (auth i).named
    checked := by
      intro p
      refine ⟨⟨(auth p).registered, B.linked p (hw p)⟩, ?_, (auth p).address,
        B.away p (auth p).registered, ?_⟩
      · intro v
        exact U.pattern_canonical S _ _ v ((auth p).matching v)
      · intro v
        apply (B.displayed p (tape := tape)).quota (hw p) raw sc ha hb rfl rfl hu hf v (credit v)
        · convert hcount v using 1
          unfold Sharing.Geo.collectorCount
          congr!
        · exact henergy v
  }⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Signal
end
