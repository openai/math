import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Origin
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Ballot
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Encode
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Initial

/-! # Passing from checked integer quotas to physical diagram bounds -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Rounds Packing Coloring Finset
open scoped Classical
variable {F V : Type} [Fintype V] {x y : Wire} {w d e k h T D u g R C ℓ n f : ℕ} {W : ℝ}
  {P : Input F x y h D T R g W} {Q : LocalTerm F x y h u}
  {a : V → Blueprint w d e k} {fixed : V → B w → Bool} (H : Support V a fixed Q)
  (he : ∀ i j, portEnd Q.diagram i = portEnd Q.diagram j ↔ portEnd P.diagram i = portEnd P.diagram j)

omit [Fintype V] in
theorem Support.amount (v : Q.diagram.V) :
    Q.charge v = (H.cellTag v).toll * u + (extLoad Q.diagram v : ℝ) := H.charge v

omit [Fintype V] in
theorem Support.core (v : Q.freeze.Core) : Q.charge v.val = ((H.cellTag v.val).toll : ℝ) * u := by
  have h : extLoad Q.diagram v.val = 0 := by
    unfold extLoad
    let : IsEmpty {i // portEnd Q.diagram i = v.val} :=
      ⟨fun i => v.property (i.property ▸ Q.freeze.exterior i.val)⟩
    exact Fintype.card_eq_zero
  rw [H.amount, h, Nat.cast_zero, add_zero]

def overhead (g C : ℕ) := 103 + 8 * C + 2 * squareConstant g

include H he in
theorem Support.concentrated (hD : 0 < D)
    (hc : Fintype.card Q.V ≤ D ^ C * Fintype.card P.V)
    (hd : ∀ i, (Q.frame.C i).card ≤ 3) (hf : ∀ i, (Q.frame.N i).card ≤ D ^ C)
    (hl : Totals a fixed D T u C n g W) {credits : V → Credits g ℓ D f}
    (hq : ∀ v, Quota C n (T / u) (fixed v) (a v) (credits v)) :
    Concentrated P Q (overhead g C) n ℓ := by
  let E := overhead g C
  have hW : 0 ≤ W := le_trans (by positivity) P.occupied
  have hpow : D ^ C ≤ D ^ E := Nat.pow_le_pow_right hD (by unfold E overhead; omega)
  have hc₀ : (3 : ℝ) ≤ E := by exact_mod_cast (show 3 ≤ E by unfold E overhead; omega)
  have hc₁ : (100 : ℝ) + 2 * C ≤ E := by exact_mod_cast (show 100 + 2 * C ≤ E by unfold E overhead; omega)
  have hc₂ : (2 : ℝ) * (squareConstant g + 1) ≤ E := by
    exact_mod_cast (show 2 * (squareConstant g + 1) ≤ E by unfold E overhead; omega)
  have hc₃ : (8 : ℝ) * C ≤ E := by exact_mod_cast (show 8 * C ≤ E by unfold E overhead; omega)
  refine ⟨hc.trans (Nat.mul_le_mul_right _ hpow), fun i => (hd i).trans (by exact_mod_cast hc₀),
    fun i => (hf i).trans hpow, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ (hl.count.trans (mul_le_mul_of_nonneg_right hc₀ hW))
    gcongr
    exact H.count
  · intro v
    have hv := (hq (H.addr v.val).1).large _ ((H.frozen _).mp v.property)
    have aux (k : ℕ) : k * (T / u) * u ≤ k * T := by rw [mul_assoc]; gcongr; exact Nat.div_mul_le_self ..
    have ha : ((H.cellTag v.val).toll : ℝ) * u ≤ 2 * C * D * T := by
      exact_mod_cast (Nat.mul_le_mul_right u hv).trans (aux _)
    rw [H.amount]
    calc
      _ ≤ (2 : ℝ) * C * D * T + (100 : ℝ) * D * T := add_le_add ha (extLoad_max P Q.diagram he v.val)
      _ = (100 + 2 * (C : ℝ)) * D * T := by ring
      _ ≤ _ := by gcongr
  · have s : (∑ i : Q.freeze.Fixed, ((H.cellTag i.val).toll : ℝ) ^ 2) * (u : ℝ) ^ 2 ≤ squareConstant g * W * T :=
      (mul_le_mul_of_nonneg_right H.square (sq_nonneg _)).trans hl.square
    have r := (Support.partial_square (Q := Q) (fun i => (extLoad Q.diagram i : ℝ))).trans
      (extLoad_squares P Q.diagram he)
    have aux (x y : ℝ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith only [sq_nonneg (x - y)]
    calc
      _ ≤ ∑ i : Q.freeze.Fixed, 2 * ((((H.cellTag i.val).toll : ℝ) * u) ^ 2 + (extLoad Q.diagram i.val : ℝ) ^ 2) := by
        apply sum_le_sum
        intro i _
        rw [H.amount]
        exact aux ..
      _ ≤ 2 * ((squareConstant g : ℝ) * W * T + W * T) := by
        simp only [←mul_sum, sum_add_distrib, mul_pow, ←sum_mul]
        exact mul_le_mul_of_nonneg_left (add_le_add s r) (by norm_num)
      _ = 2 * ((squareConstant g : ℝ) + 1) * W * T := by ring
      _ ≤ _ := by gcongr
  · intro v
    have hm := (hq (H.addr v.val).1).small _ (Bool.eq_false_iff.mpr (mt (H.frozen _).mpr v.property))
    have ht := (Nat.mul_le_mul_right u hm).trans (Nat.div_mul_le_self T u)
    rw [H.core v, mul_right_comm]
    exact_mod_cast ht
  · simp only [H.core, ←sum_mul]
    exact ((mul_le_mul_of_nonneg_right H.mobile (Nat.cast_nonneg _)).trans hl.mobile).trans (by gcongr)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# Proposed geometry on the occupied cells

The proposal contains no field coordinates, bit addresses or table
entries. Missing occurrences have an empty array of child slots.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Geometry Rounds
open scoped Classical
variable {F Z V : Type} [Field F] [Finite Z] (S : Scheme F)
    {d e M r t q D k n u j z : ℕ} (U : Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)
    (loc : V ↪ B S.m × B S.h)

def complete (a : V → U.Blueprint S) : U.Matrix S :=
  fun i b => Function.extend loc a (fun _ _ => Geometry.Outline.empty) (i, b)

omit [Field F] [Finite Z] in
theorem complete_here (a : V → U.Blueprint S) (i : V) :
    U.complete S loc a (loc i).1 (loc i).2 = a i := loc.injective.extend_apply _ _ _

omit [Field F] [Finite Z] in
theorem complete_vacant (a : V → U.Blueprint S) {i b} (h : (i, b) ∉ Set.range loc) :
    U.complete S loc a i b = fun _ => Geometry.Outline.empty := Function.extend_apply' _ _ _ h

omit [Field F] [Finite Z] in
theorem complete_of_vacant (a : U.Matrix S)
    (h : ∀ i b, (i, b) ∉ Set.range loc → a i b = fun _ => Geometry.Outline.empty) :
    U.complete S loc (fun i => a (loc i).1 (loc i).2) = a := by
  let r := fun i => a (loc i).1 (loc i).2
  have he (v : B S.m × B S.h) : U.complete S loc r v.1 v.2 = a v.1 v.2 := by
    by_cases hv : v ∈ Set.range loc
    · obtain ⟨w, rfl⟩ := hv
      exact U.complete_here S loc r w
    · rw [U.complete_vacant S loc _ hv, h _ _ hv]
  exact funext fun i => funext fun t => he (i, t)

theorem complete_support (a : V → U.Blueprint S) (v : U.Actors S)
    (h : (U.localAt S (U.complete S loc a) v).live = true) :
    ((U.split v.1).1, v.2.1) ∈ Set.range loc := by
  by_contra he
  unfold localAt at h
  rw [U.complete_vacant S loc _ he] at h
  cases h

abbrev Tag (g σ p : ℕ) := U.Blueprint S × Credits g σ D p

variable {g σ p : ℕ} [Fintype V]

/-- All tests are on the short geometry fields. -/
def passes (part : Fin p → V → V) (E H : V → ℕ) (K : ℕ)
    (x : S.format.obj) (y : U.template.format.obj) (a : V → U.Tag S g σ p) : Prop :=
  U.Valid S x y (U.complete S loc (fun i => (a i).1)) ∧
    Credits.Check part (fun i => (a i).2) E H ∧
    ∀ i, Quota (Input.terminalExponent g σ) n K U.fixedChild (a i).1 (a i).2

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! Recover the entire credit history from the final local address.
Each updated address encodes its predecessor at the center of the view. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Design
open Assembly Coloring
variable (a : Design) {F N A : Type} {e k : ℕ}

def previous (x : B (a.nextWidth e k)) : B e :=
  ((number (a.observed e k)).symm x 0 0).1

theorem previous_update (p : (a.port e).obj) (c : (a.selectors k).obj) (v : B a.m × B a.h) :
    a.previous (((a.update p c) v.1).2 v.2) = (p v.1).2 v.2 := by
  simp only [previous, update, Fmt.update, Equiv.symm_apply_apply, around, Fmt.around, Fmt.expand,
    Fmt.zip, Neighborhood.origin]

variable [Field F] [Fintype F] [ExpChar F a.p] (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (menu : a.Menu F N A e) (k : ℕ)

def historyRow : (i : ℕ) → i ≤ a.waves → B (a.widthAt e k i) → Fin (i + 1) → a.row F N
  | 0, _, x => fun _ => (menu x).2
  | i + 1, hi, x => Fin.snoc (historyRow i (Nat.le_of_succ_le hi) (a.previous x))
      (a.menuAt hF menu k (i + 1) hi x).2

theorem historyRow_last {i : ℕ} (hi : i ≤ a.waves) (x : B (a.widthAt e k i)) :
    a.historyRow hF menu k i hi x (Fin.last i) = (a.menuAt hF menu k i hi x).2 := by
  cases i with
  | zero => rfl
  | succ i => exact Fin.snoc_last ..

theorem historyRow_path (p : (a.port e).obj) {i : ℕ} (hi : i ≤ a.waves)
    (c : Fin i → (a.selectors k).obj) (v : B a.m × B a.h) (j : Fin (i + 1)) :
    a.historyRow hF menu k i hi ((a.path p i c v.1).2 v.2) j =
      (a.menuAt hF menu k j.val ((Nat.le_of_lt_succ j.isLt).trans hi)
        ((a.path p j.val (c ∘ Fin.castLE (Nat.le_of_lt_succ j.isLt)) v.1).2 v.2)).2 := by
  induction i with
  | zero => rw [Fin.eq_zero j]; rfl
  | succ i ih =>
    induction j using Fin.lastCases with
    | last => exact a.historyRow_last hF menu k hi _
    | cast j =>
      simp only [historyRow, Fin.snoc_castSucc, path, previous_update]
      exact ih (Nat.le_of_succ_le hi) (Fin.init c) j

/-- Defined on every possible label, independently of branch membership. -/
def credits (g ℓ D : ℕ) (raw : B (a.widthAt e k a.waves)) : Geometry.Credits g ℓ D a.waves :=
  let row := a.historyRow hF menu k a.waves le_rfl raw
  Geometry.Credits.issue g ℓ D a.waves (a.chart * a.H)
    (fun i => Metadata.energyCre (row i) a.chart a.H a.g)
    (fun i => Metadata.timeCre (row i) a.chart a.H a.U)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Design
end

/-! # Binary inputs for a local verifier -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Coloring

abbrev indexWidth (X : Type) := Nat.clog 2 (Nat.card X)

def labelCode (X : Type) [Fintype X] : X ↪ (Fin (indexWidth X) → Bool) :=
  Layout.binaryCode X _ (by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.le_pow_clog (by decide) _)

/-- Eligibility bits, a central record and one tag per sampled cell. -/
abbrev Pin (k : ℕ) (A I W : Type) := B k ⊕ Fin (indexWidth A) ⊕ (I × W)

variable {k : ℕ} {A I T W : Type} [Fintype A] (tcode : T ↪ (W → Bool))

def encode (e : B k → Bool) (a : A) (t : I → T) : Pin k A I W → Bool
  | .inl i => e i
  | .inr (.inl j) => labelCode A a j
  | .inr (.inr (i, j)) => tcode (t i) j

/-- A truth table on the encoded inputs has cost bounded in terms of the pin count alone. -/
theorem exists_formula [Fintype I] [Fintype W] (pred : (B k → Bool) → A → (I → T) → Prop)
    {n : ℕ} (hn : Fintype.card (Pin k A I W) ≤ n) :
    ∃ p : BitFormula (Pin k A I W), p.cost ≤ (3 * n + 2) * 2 ^ n + 1 ∧
      ∀ e a t, p.eval (encode tcode e a t) = true ↔ pred e a t := by
  classical
  obtain ⟨p, hp, hc⟩ := bool_formula fun x =>
    decide (∃ e a t, encode tcode e a t = x ∧ pred e a t)
  refine ⟨p, hc.trans (by gcongr), fun e a t => ?_⟩
  simp only [hp, decide_eq_true_eq]
  refine ⟨?_, fun h => ⟨e, a, t, rfl, h⟩⟩
  rintro ⟨e', a', t', h, h'⟩
  have he : e' = e := funext fun i => congrFun h (.inl i)
  have ha : a' = a := (labelCode A).injective (funext fun j => congrFun h (.inr (.inl j)))
  have ht : t' = t := funext fun i =>
    tcode.injective (funext fun j => congrFun h (.inr (.inr (i, j))))
  simpa only [he, ha, ht] using h'

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Geometry
variable {F Z : Type} (S : Scheme F)
  {d e M r t q D k n u j z : ℕ} (U : Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)

abbrev bluePins := B U.childBits × slots (word (U.planBits S))

/-- Store each child's outline verbatim as its own address bits. -/
def blueCode : U.Blueprint S ↪ (U.bluePins S → Bool) where
  toFun a i := (Format.addr (U.planBits S)).code (indexCode (U.Outline S) (a i.1)) i.2
  inj' _ _ h := funext fun c => (indexCode (U.Outline S)).injective
    ((Format.addr (U.planBits S)).code.injective (funext fun i => congrFun h (c, i)))

variable (g σ p : ℕ)

abbrev tagPins := U.bluePins S ⊕ Fin (indexWidth (Credits g σ D p))

def tagWidth := 2 ^ U.childBits * U.planBits S + indexWidth (Credits g σ D p)

theorem tagSize : Fintype.card (U.tagPins S g σ p) = U.tagWidth S g σ p := by
  simp only [tagPins, bluePins, tagWidth, B, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]

def tagCode : U.Tag S g σ p ↪ (U.tagPins S g σ p → Bool) where
  toFun a := Sum.elim (U.blueCode S a.1) (labelCode _ a.2)
  inj' _ _ h := Prod.ext
    ((U.blueCode S).injective (funext fun i => congrFun h (.inl i)))
    ((labelCode _).injective (funext fun i => congrFun h (.inr i)))

theorem tagCode_blue (a : U.Tag S g σ p) :
    U.tagCode S g σ p a ∘ Sum.inl = U.blueCode S a.1 := rfl

/-- Reject bit strings that are not the encoding of a tag. -/
theorem valid_formula :
    let b := U.tagWidth S g σ p
    ∃ f : BitFormula (U.tagPins S g σ p), f.cost ≤ (3 * b + 2) * 2 ^ b + 1 ∧
      ∀ t, f.eval t = true ↔ ∃ u, U.tagCode S g σ p u = t := by
  classical
  obtain ⟨f, hf, hc⟩ := bool_formula fun t => decide (∃ u, U.tagCode S g σ p u = t)
  rw [tagSize] at hc
  exact ⟨f, hc, fun t => by simp only [hf, decide_eq_true_eq]⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! Test a padded proposal using only the occupied cells. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Geometry
open scoped Classical
variable {F Z V : Type} [Field F] [Finite Z] (S : Scheme F)
  {d e M r t q D k n u j z : ℕ} (U : Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)
  (loc : V ↪ B S.m × B S.h) (y : U.template.format.obj)

abbrev Contacts := B U.childBits × B U.template.scheme.d

/-- The parent of the child reached by this navigation column. -/
def targetCell (v : V) (i : U.Contacts S) : B S.m × B S.h :=
  ((U.split (U.template.nav y (U.split.symm ((loc v).1, i.1)) i.2)).1, (loc v).2)

def linksAt (v : V) (a : U.Blueprint S) (next : U.Contacts S → U.Blueprint S) : Prop :=
  ∀ c j,
    let v' := U.split.symm ((loc v).1, c)
    let w := U.template.nav y v' j
    Geometry.Outline.Contact (a c) (next (c, j) (U.split w).2) j (U.template.flags y v' j).1
      (fun k => decide (U.template.nav y w k = v'))

/-- A local register and a reciprocal contact test. -/
def validAt (v : V) (eligible : B S.k → Bool) (a : U.Blueprint S)
    (next : U.Contacts S → U.Blueprint S) : Prop :=
  Geometry.Blueprint.Register a U.outer eligible (U.childLive S y (loc v).1) (U.childFixed S y (loc v).1) ∧
  U.linksAt S loc y v a next

def vacantHeld (x : S.format.obj) : Prop :=
  ∀ i b, (i, b) ∉ Set.range loc → ∀ l, held S ((x i).2 b) l = false

theorem valid_complete (x : S.format.obj) (hv : vacantHeld S loc x) (a : V → U.Blueprint S) :
    U.Valid S x y (U.complete S loc a) ↔ ∀ v,
      U.validAt S loc y v (held S ((x (loc v).1).2 (loc v).2)) (a v)
        (fun i => let w := U.targetCell S loc y v i; U.complete S loc a w.1 w.2) := by
  let A := U.complete S loc a
  have here (v : V) (c : B U.childBits) :
      U.localAt S A (U.split.symm ((loc v).1, c), (loc v).2, 0) = a v c := by
    rw [localAt, Equiv.apply_symm_apply]
    exact congrFun (U.complete_here S loc a v) c
  constructor
  · intro h v
    have hr := h.1 (loc v).1 (loc v).2
    rw [U.complete_here] at hr
    refine ⟨hr, fun c i => ?_⟩
    have hj := h.2 (U.split.symm ((loc v).1, c)) (loc v).2 i
    rw [← here v c]
    exact hj
  · intro h
    constructor
    · intro i b
      by_cases he : (i, b) ∈ Set.range loc
      · obtain ⟨v, he⟩ := he
        have hr := (h v).1
        rw [← U.complete_here S loc a v, he] at hr
        exact hr
      rw [U.complete_vacant S loc _ he]
      constructor <;> simp [Geometry.Outline.empty, hv i b he]
    · intro p b i
      by_cases he : ((U.split p).1, b) ∈ Set.range loc
      · obtain ⟨v, he⟩ := he
        let c := (U.split p).2
        have hj := (h v).2 c i
        rw [← here v c] at hj
        simp only [targetCell, he, c, Prod.mk.eta, Equiv.symm_apply_apply] at hj
        exact hj
      change Geometry.Outline.Contact (U.complete S loc a (U.split p).1 b (U.split p).2) _ _ _ _
      rw [U.complete_vacant S loc _ he]
      simp [Geometry.Outline.Contact, Geometry.Outline.empty]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! The checks at a cell use bounded initial caps, eligibility bits,
and tags read at a fixed set of addresses. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Credits
open Rounds.Input
variable {g σ D p : ℕ}

abbrev Caps (g σ D p : ℕ) := Fin (energyLimit g D p + 1) × Fin (timeLimit g σ D + 1)

def caps (g σ D p E H : ℕ) : Caps g σ D p :=
  (⟨min E _, Nat.lt_succ_of_le (min_le_right E _)⟩,
   ⟨min H _, Nat.lt_succ_of_le (min_le_right H _)⟩)

theorem le_caps (z : Credits g σ D p) (E H : ℕ) :
    (z.power 0 ≤ (caps g σ D p E H).1.val ∧ z.time 0 ≤ (caps g σ D p E H).2.val) ↔
      z.power 0 ≤ E ∧ z.time 0 ≤ H := by
  have he := Nat.le_of_lt_succ (z 0).1.isLt
  have ht := Nat.le_of_lt_succ (z 0).2.isLt
  simp only [caps, power, time, le_min_iff, he, ht, and_true]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Credits

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Geometry Surface.Local Rounds
open scoped Classical
variable {F Z N A : Type} [Field F] [Finite Z] (S : Scheme F)
    {d e M r t q D k n u j z g σ : ℕ} (U : Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)
    {cfg : Design} {x₀ y₀ : Wire} (w : Scenario F N A cfg x₀ y₀)
    (loc : w.V ↪ B S.m × B S.h) (y : U.template.format.obj)

abbrev Queries (v : w.V) := Unit ⊕ U.Contacts S ⊕ w.Ball v

/-- No tag is requested when the target cell is vacant. -/
def query (v : w.V) : U.Queries S w v → Option w.V
  | .inl _ => some v
  | .inr (.inl i) => Function.extend loc some (fun _ => none) (U.targetCell S loc y v i)
  | .inr (.inr i) => some i.val

abbrev blankTag (g σ p : ℕ) : U.Tag S g σ p := (fun _ => Outline.empty, fun _ => (0, 0))

def samples (a : w.V → U.Tag S g σ cfg.waves) (v : w.V) (i : U.Queries S w v) :=
  (U.query S w loc y v i).elim (U.blankTag S g σ cfg.waves) a

private theorem sample_next (a : w.V → U.Tag S g σ cfg.waves) (v : w.V) (i : U.Contacts S) :
    (U.samples S w loc y a v (.inr (.inl i))).1 =
      let x := U.targetCell S loc y v i
      U.complete S loc (fun j => (a j).1) x.1 x.2 := by
  simp only [samples, query]
  generalize U.targetCell S loc y v i = x
  by_cases hx : x ∈ Set.range loc
  · obtain ⟨j, rfl⟩ := hx
    rw [loc.injective.extend_apply, U.complete_here]
    rfl
  · rw [Function.extend_apply' _ _ _ hx, U.complete_vacant S loc _ hx]
    rfl

def examine (K : ℕ) (v : w.V) (eligible : B S.k → Bool) (c : Credits.Caps g σ D cfg.waves)
    (a : U.Queries S w v → U.Tag S g σ cfg.waves) : Prop :=
  U.validAt S loc y v eligible (a (.inl ())).1 (fun i => (a (.inr (.inl i))).1) ∧
  w.checkAt v (fun i => (a (.inr (.inr i))).2) c.1.val c.2.val ∧
  Quota (Input.terminalExponent g σ) n K U.fixedChild (a (.inl ())).1 (a (.inl ())).2

theorem passes_iff (K : ℕ) (E H : w.V → ℕ) (x : S.format.obj) (hv : vacantHeld S loc x)
    (a : w.V → U.Tag S g σ cfg.waves) :
    U.passes S loc w.loc E H K x y a ↔ ∀ v, U.examine S w loc y K v
      (held S ((x (loc v).1).2 (loc v).2)) (Credits.caps g σ D cfg.waves (E v) (H v))
      (U.samples S w loc y a v) := by
  unfold passes
  rw [U.valid_complete S loc y x hv, w.check_iff]
  simp only [examine, sample_next]
  simp only [samples, query, Option.elim_some, Scenario.checkAt, Credits.localCheck, Credits.le_caps,
    forall_and]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-!
# Computing the initial caps from bounded seat data

A seat provides its number of packets and one immobility bit.
Absent seats contribute neither packets nor collectors. The
arithmetic defining the caps is tabulated on this finite alphabet.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Geometry SphereScale Finset
open scoped Classical

abbrev CapSeat (ℓ D : ℕ) := Fin (probes ℓ D + 1) × Bool
abbrev CapData (ℓ D : ℕ) := Fin (100 * D) → CapSeat ℓ D
abbrev CapPins (ℓ D : ℕ) := Fin (100 * D) × Fin (indexWidth (CapSeat ℓ D))

def capCode {ℓ D : ℕ} : CapData ℓ D ↪ (CapPins ℓ D → Bool) where
  toFun s i := labelCode _ (s i.1) i.2
  inj' _ _ h := funext fun i => (labelCode _).injective (funext fun j => congrFun h (i, j))

private def pad {α : Type} {n k : ℕ} (z : α) (s : Fin n → α) (i : Fin k) :=
  if h : i.val < n then s ⟨i.val, h⟩ else z

private theorem sum_pad {α : Type} {n k : ℕ} (h : n ≤ k) (z : α) (s : Fin n → α)
    (f : α → ℕ) (hf : f z = 0) : ∑ i : Fin k, f (pad z s i) = ∑ i, f (s i) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.sum_univ_add]
  simp [pad, hf]

variable {F : Type} {x y : Wire} {h D T b d g ℓ m : ℕ} {W : ℝ}
    (P : Input F x y h D T (d * b) g W) (sc : Scales g ℓ D T m b d)

private def seatData (v : P.Occupied) (i : Fin (P.grid.stations v).card) : CapSeat ℓ D :=
  let u := P.grid.label v i
  (⟨(P.grid.uses u).card, Nat.lt_succ_of_le (P.maxPackets sc u)⟩, decide (¬ P.mobile u))

def capData (v : P.Occupied) : CapData ℓ D := pad (0, false) (P.seatData sc v)

def capEnergy (g m b d waves : ℕ) (z : CapData ℓ D) : ℕ :=
  let H := SphereScale.energy ℓ D (d * b)
  let packets := ∑ i, (d * b) * (8 * (z i).1.val ^ 2)
  clip waves (m * H) ((1 + 4 * g) * (reserve D b d (probes ℓ D) m H + m * packets))

def capTime (g : ℕ) (z : CapData ℓ D) : ℕ :=
  D ^ 5 * (1 + ∑ i, if (z i).2 then 1 else 0) + budget g * D ^ 2

theorem cap_energy (v : P.Occupied) (waves : ℕ) :
    capEnergy g m b d waves (P.capData sc v) = P.initialEnergyTokens ℓ m waves v := by
  let f (s : CapSeat ℓ D) := (d * b) * (8 * s.1.val ^ 2)
  have he : (∑ i, f (P.capData sc v i)) =
      ∑ i : Fin (P.grid.stations v).card, (d * b) * (8 * (P.grid.width v (Fin.castAdd _ i)) ^ 2) := by
    unfold capData
    rw [sum_pad (P.stations_bound v) _ _ _ (by simp [f])]
    simp only [f, seatData, Grid.width, Grid.mark_label]
  exact congrArg (fun e => clip waves (m * SphereScale.energy ℓ D (d * b))
    ((1 + 4 * g) * (reserve D b d (probes ℓ D) m (SphereScale.energy ℓ D (d * b)) + m * e))) he

theorem cap_time (v : P.Occupied) :
    capTime g (P.capData sc v) = P.initialTimeTokens v := by
  let f (s : CapSeat ℓ D) := if s.2 then 1 else 0
  have he : (∑ i, f (P.capData sc v i)) = ∑ u ∈ P.grid.stations v, if ¬ P.mobile u then 1 else 0 := by
    unfold capData
    rw [sum_pad (P.stations_bound v) _ _ _ (by simp [f]), ← sum_coe_sort (P.grid.stations v),
      ← (Grid.number P.grid.stationRank (P.grid.stations v)).sum_comp]
    apply sum_congr rfl
    intro i _
    change (if decide (¬P.mobile (P.grid.label v i)) then 1 else 0) =
      (if ¬P.mobile (P.grid.label v i) then 1 else 0)
    by_cases hi : P.mobile (P.grid.label v i) <;> simp [hi]
  exact congrArg (fun t => D ^ 5 * (1 + t) + budget g * D ^ 2) he

def capCost (g ℓ D waves : ℕ) : ℕ :=
  indexWidth (Credits.Caps g ℓ D waves) *
    ((3 * Fintype.card (CapPins ℓ D) + 2) * Fintype.card (CapData ℓ D) + 1)

/-- The same formulas work for all fields and cells. Only the
bounded seat and credit alphabets enter their total size. -/
theorem cap_formulas (g ℓ D m b d waves : ℕ) :
    ∃ f : Fin (indexWidth (Credits.Caps g ℓ D waves)) → BitFormula (CapPins ℓ D),
      (∑ i, (f i).cost) ≤ capCost g ℓ D waves ∧
      ∀ {F : Type} {x y : Wire} {h T : ℕ} {W : ℝ}
        (P : Input F x y h D T (d * b) g W) (sc : Scales g ℓ D T m b d) (v : P.Occupied) i,
        (f i).eval (capCode (P.capData sc v)) = labelCode _ (Credits.caps g ℓ D waves
          (P.initialEnergyTokens ℓ m waves v) (P.initialTimeTokens v)) i := by
  let out (z : CapData ℓ D) := labelCode _ (Credits.caps g ℓ D waves (capEnergy g m b d waves z) (capTime g z))
  choose f hf hc using fun i => finite_formula capCode (fun z => out z i)
  refine ⟨f, ?_, fun P sc v i => ?_⟩
  · simpa only [capCost, sum_const, card_fin, Nat.nsmul_eq_mul] using sum_le_sum (s := univ) (fun i _ => hc i)
  · rw [hf]
    unfold out
    rw [cap_energy, cap_time]

theorem local_caps (waves : ℕ) :
    ∃ f : Fin (indexWidth (Credits.Caps g ℓ D waves)) → BitFormula (CapPins ℓ D),
      (∑ i, (f i).cost) ≤ capCost g ℓ D waves ∧
      ∀ (v : P.Occupied) i, (f i).eval (capCode (P.capData sc v)) =
        labelCode _ (Credits.caps g ℓ D waves (P.initialEnergyTokens ℓ m waves v) (P.initialTimeTokens v)) i := by
  obtain ⟨f, hf, h⟩ := cap_formulas g ℓ D m b d waves
  exact ⟨f, hf, h P sc⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Boolean checks with one bounded formula per occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Geometry Surface.Local
open scoped Classical
variable {F Z N A : Type} [Field F] [Finite Z] (S : Scheme F)
  {d e M r t q D k n u j z : ℕ} (U : Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)

def checkWidth (g σ : ℕ) (cfg : Design) :=
  2 ^ S.k + indexWidth (Credits.Caps g σ D cfg.waves) +
    (1 + 2 ^ U.childBits * 2 ^ U.template.scheme.d + 2 ^ ((cfg.d + 1) * (cfg.U + 1))) * U.tagWidth S g σ cfg.waves

variable {cfg : Design} {x₀ y₀ : Wire} (w : Scenario F N A cfg x₀ y₀) (g σ : ℕ)

abbrev checkPins (v : w.V) :=
  Geometry.Pin S.k (Credits.Caps g σ D cfg.waves) (U.Queries S w v) (U.tagPins S g σ cfg.waves)

theorem check_size (v : w.V) : Fintype.card (U.checkPins S w g σ v) ≤ U.checkWidth S g σ cfg := by
  rw [checkWidth, ← U.tagSize]
  simp only [checkPins, Geometry.Pin, Queries, Contacts, B, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_unit, Fintype.card_fin, add_assoc]
  gcongr
  exact w.card_ball v

variable {g σ} (loc : w.V ↪ B S.m × B S.h) (y : U.template.format.obj)

def checkInputs (E H : w.V → ℕ) (x : S.format.obj) (a : w.V → U.Tag S g σ cfg.waves)
    (v : w.V) : U.checkPins S w g σ v → Bool :=
  Geometry.encode (U.tagCode S g σ cfg.waves) (held S ((x (loc v).1).2 (loc v).2)) (Credits.caps g σ D cfg.waves (E v) (H v))
    (U.samples S w loc y a v)

/-- The formulas are fixed before seeing the eligibility bits, the initial
caps, or the proposed blueprints and credits. -/
theorem passes_binary (K : ℕ) :
    let b := U.checkWidth S g σ cfg
    ∃ f : ∀ v, BitFormula (U.checkPins S w g σ v),
      (∀ v, (f v).cost ≤ (3 * b + 2) * 2 ^ b + 1) ∧
      ∀ (E H : w.V → ℕ) (x : S.format.obj), vacantHeld S loc x → ∀ a : w.V → U.Tag S g σ cfg.waves,
        U.passes S loc w.loc E H K x y a ↔ ∀ v, (f v).eval (U.checkInputs S w loc y E H x a v) = true := by
  choose f hf he using fun v => Geometry.exists_formula (U.tagCode S g σ cfg.waves)
    (U.examine S w loc y K v) (U.check_size S w g σ v)
  refine ⟨f, hf, fun E H x hv a => ?_⟩
  rw [U.passes_iff S w loc y K E H x hv]
  exact forall_congr' fun v => (he v _ _ _).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! The printer's geometry checks depend only on the common navigation and status. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring
variable {F Z V : Type} [Field F] [Finite Z] (S : Scheme F)
  {d e M r t q D k n u j z : ℕ} (U : Printer F Z (B S.k) S.m d S.h e M r t q D k n u j z)

/-- Changing block labels or printer selectors preserves the geometry checks. -/
theorem passes_advance [Fintype V] (loc : V ↪ B S.m × B S.h) {g σ p : ℕ}
    (part : Fin p → V → V) (E H : V → ℕ) (K : ℕ) (x : S.format.obj)
    (a : V → U.Tag S g σ p) {data data' : U.rows.obj}
    (status : (Children.Header S.m d).obj) (c c' : U.selectors.obj)
    (h : ∀ i, (data i).1 = (data' i).1) :
    U.passes S loc part E H K x (U.advance data status c) a ↔
      U.passes S loc part E H K x (U.advance data' status c') a := by
  have he : Children.tape (U.update data status c) = Children.tape (U.update data' status c') :=
    Prod.ext (funext h) rfl
  unfold advance Children.write
  erw [he]
  rfl

/-- Each printed neighbor lies over the same parent or one of its neighbors. -/
theorem nav_reach (data : U.rows.obj) (status : (Children.Header S.m d).obj)
    (c : U.selectors.obj) (v : B U.template.scheme.m) (i : B U.template.scheme.d) :
    Neighborhood.Reach (fun j => (data j).1) 1 (U.split v).1
      (U.split (U.template.nav (U.advance data status c) v i)).1 := by
  let r := Children.entries U.slot U.dyadic U.large U.chunks U.degree
    (Children.tape (U.update data status c))
  let p := ((r.2 v).2 i).2
  change Neighborhood.Reach _ 1 _ (U.split (U.split.symm
    (History.Reset.Child.follow r.1 (U.split v).1 p.1, p.2))).1
  rw [Equiv.apply_symm_apply]
  unfold History.Reset.Child.follow
  split
  · exact Neighborhood.mem.mp ⟨_, rfl⟩
  · exact Neighborhood.Reach.refl ..

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end
