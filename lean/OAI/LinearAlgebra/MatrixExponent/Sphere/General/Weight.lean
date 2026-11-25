import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Ballot
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Scales
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access

/-! # Occupied-cell indices for printed profiles -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local

private theorem retype_none {α β : Type} (h : α = β) :
    cast (congrArg Option h) (none : Option α) = none := by cases h; rfl

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {h g ℓ D T b d p l j : ℕ} {W : ℝ} {S : Scheme F}
    (P : Input F x y h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "world" => P.localWorld A sc hK s
local notation "Cfg" => design S g ℓ D b d p l

theorem printMenu_away {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j} (c : (world).Code (Cfg).waves menu)
    {M r t : ℕ} (ha : d * b = M * r) (hb : d = M * t) (v : B S.m × B S.h) (hv : v ∉ Set.range A.coord) :
    printMenu S menu ha hb ((c.tape v.1).2 v.2) = none := by
  unfold printMenu
  rw [P.panel_read A sc hK s c v, (world).atlas.fill_away _ hv]
  exact retype_none (congrArg₂ (fun x y => Print.Face F x y (Cfg).R (panelKeys Cfg) (B S.k)) ha hb)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.NamedRelease
open Coloring Assembly Rounds

variable {F K J : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g σ : ℕ} {W : ℝ} {P : Input F x y S.h D T R g W}
  {tape : S.format.obj} {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {pres : S.Presentation tape P.diagram} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {f : Val x → Val y → F} (o : U.NamedRelease pres data status f σ)
  (loc : J ↪ B S.m × B S.h)
  (vacant : ∀ v ∉ Set.range loc, U.menu ((data v.1).2 v.2) = none)

include vacant

/-- Even if the printed tensor vanishes, the explicit profile still
has a unit scalar and has only the padding ballot at vacant cells. -/
theorem supported (i : o.I) : Sparse.Supported loc U.pad (o.select.write i) := by
  apply U.supported data _ loc vacant
  rw [o.valid, (o.select.valid _ i).mpr rfl, Option.elim_some]
  exact o.nonzero i

def localIndex := Sparse.compress loc U.pad o.select (o.supported loc vacant)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.NamedRelease
end

/-! # Initial records with a mobility rule depending on the local label and seat -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere.Surface.Local SphereScale Transcript Finset
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {g ℓ D T b d p l : ℕ}

section
variable (S : Scheme F)

local notation "Cfg" => design S g ℓ D b d p l
local notation "Query" => panelQuery S g ℓ D b d p l

/-- Unused seats contribute no stations. A cell may have several fixed
stations when the mobility rule is false on several occupied seats. -/
def localMenu (hK : Ready K ℓ D g (p ^ l) b d) (mobility : B S.ℓ → B S.k → Bool) (k : ℕ) :
    (Cfg).Menu F (B S.k) (B S.ℓ) (Query k).width := fun j =>
  let v := (Design.number (Query k)).symm j
  if live S v.1.1 then
    if h : v.1.2.2.2.val < Fintype.card (Shape (probes ℓ D) b d) then
      viewStart S hK v.1.1 v.1.2.1 v.1.2.2.1 (fun i => (v.2 i).1) (fun i => (v.2 i).2.1)
        (mobility v.1.1) ((Fintype.equivFin _).symm ⟨_, h⟩)
    else (v.1.1, none)
  else (v.1.1, none)

end

variable {x y : Wire} {h k : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
  (s : P.Occupied → Shape (probes ℓ D) b d) {t : S.Presentation z P.diagram}
  {mobility : B S.ℓ → B S.k → Bool}
  (H : P.Placed t A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val) (fun v => mobility ((z v.1).2 v.2.1) v.2.2))

local notation "Sh" => Shape (probes ℓ D) b d

include H

theorem localWeight (hk : initialChoices ℓ D b d ≤ 2 ^ k) (c : (Boot.selectors S.m S.h k).obj) :
    Fmt.weight (panelGuard S sc k) (panelAround S sc z c) =
      ((P.panelSelector A hk).read c).elim 0 (fun _ => 1) := by
  let w (v : B S.m × B S.h) := panelGuard S sc k (((panelAround S sc z c) v.1).2 v.2)
  have fits : Fintype.card Sh ≤ 2 ^ k := by rw [card_shape]; exact hk
  have hw := Selector.scattered_weight A.coord (fun _ => Sh) (fun _ => fits)
    (Function.uncurry c) (fun _ _ => (1 : F)) w (by
      intro j
      have hj := (H.live_iff (A.coord j)).mpr ⟨j, rfl⟩
      simp only [w, panelGuard, panelAround, Boot.around, Boot.colored, hj, ite_true, Function.uncurry]
      split_ifs <;> rfl)
    (by
      intro v hv
      have hv' := mt (H.live_iff v).mp hv
      simp only [w, panelGuard, panelAround, Boot.around, Boot.colored, hv', ite_false, Function.uncurry]
      split_ifs <;> rfl)
  simp only [prod_const_one, Fintype.prod_prod_type] at hw
  exact hw

/-- The physical tape and the initial frame agree at every host, including vacant slots. -/
def localCode (hr : P.LocalRanks) (hk : initialChoices ℓ D b d ≤ 2 ^ k) :
    (P.localWorld A sc hK s).Code 0 (localMenu S hK mobility k) where
  frame := P.start A sc hK s
  tape := panelTape S sc z ((P.panelSelector A hk).write s)
  host _ := rfl
  read := by
    intro i
    simp only [panelTape, Fmt.update, localMenu, Equiv.symm_apply_apply, panelAround, Boot.around, Boot.colored]
    by_cases hi : i ∈ Set.range A.coord
    · obtain ⟨j, rfl⟩ := hi
      have hj := (H.live_iff (A.coord j)).mpr ⟨j, rfl⟩
      simp only [hj, ite_true, P.panelSelector_at, Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
      exact (P.start_at A sc hK s H hr j).symm
    · rw [ite_eq_right (mt (H.live_iff i).mp hi)]
      exact (P.start_away A sc hK s i hi).symm

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Occupied-cell selectors for initialization and motion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Transcript

variable {F : Type} {x y : Wire} {g ℓ D T b d p l h k : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (hk : initialChoices ℓ D b d ≤ 2 ^ k)

theorem panel_supported (i : P.Occupied → Shape (probes ℓ D) b d) :
    Sparse.Supported A.coord 0 ((P.panelSelector A hk).write i) :=
  fun v hv => Selector.scatter_away A.coord _ (fun _ => by rw [card_shape]; exact hk) i v hv

def localIndex := Sparse.compress A.coord 0 (P.panelSelector A hk) (P.panel_supported A hk)

variable [Field F] (sc : Scales g ℓ D T (p ^ l) b d)
  {t : S.Presentation z P.diagram} {mobility : B S.ℓ → B S.k → Bool}
  (H : P.Placed t A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val) (fun v => mobility ((z v.1).2 v.2.1) v.2.2))

include H hk in
theorem guard_supported (c : (Boot.selectors S.m S.h k).obj)
    (hc : Fmt.weight (panelGuard S sc k) (panelAround S sc z c) ≠ 0) :
    Sparse.Supported A.coord 0 c := by
  rw [P.localWeight A sc H hk] at hc
  exact Sparse.of_weight A.coord 0 _ (P.panel_supported A hk) hc

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring Assembly

variable {F A N : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p]
  {e k : ℕ} {x y : Wire} {menu : a.Menu F N A e}
  (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (j : Fin a.waves) (s : w.Code j.val menu)
  (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

def localIndex := Sparse.compress w.atlas.coord 0 (w.selector hF j s hk) (w.selector_away hF j s hk)

include hk in
theorem weight_supported (c : (a.selectors k).obj)
    (hc : Fmt.weight (a.tariff hF j menu k) (a.around s.tape c) ≠ 0) :
    Sparse.Supported w.atlas.coord 0 c := by
  rw [w.weighted hF j s hk] at hc
  exact Sparse.of_weight w.atlas.coord 0 _ (w.selector_away hF j s hk) hc

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-! # Computing the weight from the occupied occurrences alone -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Coloring Assembly Sphere
open scoped Classical

namespace Rounds.Input
open SphereScale
variable {F : Type} [Field F] {x y : Wire} {h k g ℓ D T b d p l : ℕ} {W : ℝ}
  (P : Input F x y h D T (d * b) g W) {S : Scheme F} {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d)
  {pres : S.Presentation z P.diagram} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}

theorem guard_occupied (H : P.Placed pres A.coord tone mobile) (c : P.Occupied → B k) :
    let t := panelAround S sc z (Sparse.pack A.coord 0 c)
    Fmt.weight (panelGuard S sc k) t =
      ∏ i, panelGuard S sc k ((t (A.coord i).1).2 (A.coord i).2) := by
  intro t
  refine Sparse.prod_occupied A.coord (fun v => panelGuard S sc k ((t v.1).2 v.2)) ?_
  intro v hv
  have empty := mt (H.live_iff v).mp hv
  have zero := Sparse.pack_supported A.coord 0 c v hv
  simp only [t, panelGuard, panelAround, Boot.around, Boot.colored, empty, ite_false, zero, ite_true]

end Rounds.Input

namespace Sphere.Surface.Local.Scenario
variable {F N A : Type} [Field F] [Fintype F] {a : Design} [ExpChar F a.p] {x y : Wire}
  (w : Scenario F N A a x y) {e k : ℕ} (hF : a.M * (2 * a.D + 1) < Fintype.card F)
  (menu : a.Menu F N A e) (start : w.Code 0 menu)

theorem charge_occupied (i : ℕ) (hi : i ≤ a.waves) (c : w.History k i) :
    a.totalCharge start.tape hF menu i hi (w.tapes c) =
      ∏ v, a.localCharge start.tape hF menu i hi (w.tapes c) (w.atlas.coord v) := by
  refine a.total_occupied start.tape hF menu w.atlas.coord ?_ i hi (w.tapes c)
    (fun j => Sparse.pack_supported _ _ (c j))
  intro v hv
  rw [start.read, stored, Palette.records_away _ _ _ _ _ hv]

end Sphere.Surface.Local.Scenario

namespace Sphere.Print.Printer
variable {F K N : Type} [Field F] {m d h e M r t q D k n u j z : ℕ}
  (U : Printer F K N m d h e M r t q D k n u j z) (data : U.rows.obj)

theorem score_occupied {J : Type} [Fintype J] (loc : J ↪ B m × B h)
    (vacant : ∀ v ∉ Set.range loc, U.menu ((data v.1).2 v.2) = none) (c : J → B U.digits) :
    U.score data (Sparse.pack loc U.pad c) =
      ∏ v, U.tariff (((U.around data (Sparse.pack loc U.pad c)) (loc v).1).2 (loc v).2) := by
  let tape := Sparse.pack loc U.pad c
  refine Sparse.prod_occupied loc (fun v => U.tariff (((U.around data tape) v.1).2 v.2)) ?_
  intro v hv
  let w := U.view (((U.around data tape) v.1).2 v.2)
  have he : w 0 0 = (none, fun _ _ => 0) := by
    have padAt : tape v.1 v.2 = U.pad := Sparse.pack_supported loc U.pad c v hv
    simp only [w, view, around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin, vacant v hv,
      padAt, pad, Equiv.symm_apply_apply]
  have ok : w.valid U.positive := by simp [Lens.valid, Lens.ask, he, quota, tally]
  change w.score U.positive = 1
  simp [Lens.score, ok, he]

end Sphere.Print.Printer
end OAI.LinearAlgebra.MatrixExponent
end

/-! # A finite expansion indexed by the occupied-cell history -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Assembly Coloring Transcript Finset
open scoped Classical

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
    (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
    {e : ℕ} (menu : a.Menu F N A e) (k : ℕ) (start : w.Code 0 menu)

abbrev Invariant := ∀ i, w.History k i → w.At i → Prop

abbrev AtCode (i : ℕ) (hi : i ≤ a.waves) := w.Code i (a.menuAt hF menu k i hi)

/-- Every accepted branch has a tape and a semantic frame. Validity
also accounts for the weights of words outside the branch index. -/
structure Run (Good : w.Invariant k) (i : ℕ) (hi : i ≤ a.waves) where
  I : Type
  [finite : Fintype I]
  select : Selector I (w.History k i)
  coeff : I → F
  code : I → w.AtCode hF menu k i hi
  good : ∀ j, Good i (select.write j) (code j).frame
  written : ∀ j, (code j).tape = a.path start.tape i (w.tapes (select.write j))
  valid : ∀ c, a.totalCharge start.tape hF menu i hi (w.tapes c) = (select.read c).elim 0 coeff
  value : ∀ u v, w.eval start.frame u v = ∑ j, coeff j * w.eval (code j).frame u v

attribute [instance] Run.finite

/-- The only extension rule needed of a semantic invariant. -/
def Extends (Good : w.Invariant k) (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k) : Prop :=
  ∀ (j : Fin a.waves) (c : w.History k j.val) (s : w.AtCode hF menu k j.val j.isLt.le),
    s.tape = a.path start.tape j.val (w.tapes c) → Good j.val c s.frame →
    ∃ q : w.Branch hF j s → w.AtCode hF menu k (j.val + 1) j.isLt,
      (∀ t, (q t).tape = a.update s.tape ((w.selector hF j s hk).write t)) ∧
      (∀ t, Good (j.val + 1) (Fin.snoc c ((w.localIndex hF j s hk).write t)) (q t).frame) ∧
      ∀ u v, w.eval s.frame u v = ∑ t, w.scalar hF j s t * w.eval (q t).frame u v

variable {Good : w.Invariant k}

private def emptyIndex {X : Type} : Selector Unit (Fin 0 → X) where
  write _ := Fin.elim0
  read _ := some ()
  valid _ _ := ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩

private def first (h : Good 0 Fin.elim0 start.frame) : w.Run hF menu k start Good 0 (Nat.zero_le _) where
  I := Unit
  select := emptyIndex
  coeff _ := 1
  code _ := start
  good _ := h
  written _ := rfl
  valid _ := rfl
  value u v := by simp only [one_mul, Fintype.sum_unique]

private def snocIndex {X : Type} (i : ℕ) : ((Fin i → X) × X) ≃ (Fin (i + 1) → X) :=
  (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => X)

variable (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

theorem path_write (j : Fin a.waves) (c : w.History k j.val) (s : w.AtCode hF menu k j.val j.isLt.le)
    (hc : s.tape = a.path start.tape j.val (w.tapes c)) (t : w.Branch hF j s) :
    a.path start.tape (j.val + 1) (w.tapes (Fin.snoc c ((w.localIndex hF j s hk).write t))) =
      a.update s.tape ((w.selector hF j s hk).write t) := by
  rw [tapes_snoc, Design.path_snoc, ← hc]
  exact congrArg (a.update s.tape) (Sparse.pack_sample _ _ (w.selector_away hF j s hk t))

private theorem more (step : w.Extends hF menu k start Good hk) {i : ℕ} (hi : i < a.waves)
    (p : w.Run hF menu k start Good i hi.le) :
    Nonempty (w.Run hF menu k start Good (i + 1) hi) := by
  let j : Fin a.waves := ⟨i, hi⟩
  choose q ht hg hv using fun x => step j (p.select.write x) (p.code x) (p.written x) (p.good x)
  let S x := w.localIndex hF j (p.code x) hk
  let sel := (p.select.bind S).relabel (snocIndex i)
  let coeff (a : Σ x : p.I, w.Branch hF j (p.code x)) := p.coeff a.1 * w.scalar hF j (p.code a.1) a.2
  refine ⟨{ I := Σ x, w.Branch hF j (p.code x)
            select := sel
            coeff := coeff
            code := fun x => q x.1 x.2
            good := fun x => hg x.1 x.2
            written := ?_
            valid := ?_
            value := ?_ }⟩
  · rintro ⟨x, t⟩
    exact (ht x t).trans (w.path_write hF menu k start hk j _ _ (p.written x) t).symm
  · intro c
    obtain ⟨⟨u, v⟩, rfl⟩ := (snocIndex i).surjective c
    simp only [sel, Selector.relabel, Equiv.symm_apply_apply]
    change a.totalCharge start.tape hF menu (i + 1) hi (w.tapes (Fin.snoc u v)) =
      ((p.select.read u).bind fun x => ((S x).read v).map (Sigma.mk x)).elim 0 coeff
    rw [tapes_snoc, Design.charge_snoc, p.valid]
    cases he : p.select.read u with
    | none => simp
    | some x =>
      have hu := (p.select.valid _ x).mp he
      rw [hu, ← p.written]
      have hw := w.weighted hF j (p.code x) hk (Sparse.pack w.atlas.coord 0 v)
      change _ = ((S x).read v).elim 0 _ at hw
      rw [hw]
      simp only [Option.bind_some, Option.elim_some]
      cases (S x).read v <;> simp [coeff]
  · intro u v
    rw [p.value, Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    rw [hv, Finset.mul_sum]
    exact sum_congr rfl (fun j _ => (mul_assoc _ _ _).symm)

theorem run (h : Good 0 Fin.elim0 start.frame) (step : w.Extends hF menu k start Good hk)
    (i : ℕ) (hi : i ≤ a.waves) : Nonempty (w.Run hF menu k start Good i hi) := by
  induction i with
  | zero => exact ⟨w.first hF menu k start h⟩
  | succ i ih => exact w.more hF menu k start hk step hi (ih (Nat.le_of_succ_le hi)).some

theorem Run.card_le {i : ℕ} {hi : i ≤ a.waves} (p : w.Run hF menu k start Good i hi) :
    Fintype.card p.I ≤ 2 ^ (k * Fintype.card w.V * i) := by
  have h := Fintype.card_le_of_injective p.select.write p.select.injective
  simpa only [History, Fintype.card_fun, Fintype.card_fin, pow_mul] using h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-! # Certificates for the metadata at every prefix of a motion history -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
    (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
    {e : ℕ} (menu : a.Menu F N A e) (k : ℕ) (start : w.Code 0 menu)

def before {X : Type} {i j : ℕ} (c : Fin i → X) (h : j ≤ i) : Fin j → X := c ∘ Fin.castLE h

@[simp] theorem before_self {X : Type} {i : ℕ} (c : Fin i → X) : before c le_rfl = c := rfl

theorem before_snoc {X : Type} {i j : ℕ} (c : Fin i → X) (t : X) (h : j ≤ i) :
    before (Fin.snoc c t) (h.trans (Nat.le_succ i)) = before c h := by
  funext l
  exact Fin.snoc_castSucc (α := fun _ => X) t c (Fin.castLE h l)

/-- Each consecutive pair of prefix tapes is realized by frames
satisfying the same regional energy and time inequalities. -/
def Certified : w.Invariant k := fun i c _ =>
  ∀ (j : Fin a.waves) (h : j.val < i),
    ∃ (p : w.AtCode hF menu k j.val j.isLt.le) (q : w.AtCode hF menu k (j.val + 1) j.isLt),
      p.tape = a.path start.tape j.val (w.tapes (before c h.le)) ∧
      q.tape = a.path start.tape (j.val + 1) (w.tapes (before c h)) ∧
      w.Balanced j p.frame q.frame

theorem certified_snoc (j : Fin a.waves) (c : w.History k j.val) (t : w.V → B k)
    (p : w.AtCode hF menu k j.val j.isLt.le) (q : w.AtCode hF menu k (j.val + 1) j.isLt)
    (hp : p.tape = a.path start.tape j.val (w.tapes c))
    (hq : q.tape = a.path start.tape (j.val + 1) (w.tapes (Fin.snoc c t)))
    (hb : w.Balanced j p.frame q.frame) (hc : w.Certified hF menu k start _ c p.frame) :
    w.Certified hF menu k start _ (Fin.snoc c t) q.frame := by
  intro l hl
  by_cases e : l = j
  · subst l
    rw [before_snoc c t le_rfl, before_self, before_self]
    exact ⟨p, q, hp, hq, hb⟩
  · have hlt : l.val < j.val := by
      have hne := Fin.val_injective.ne e
      omega
    rw [before_snoc c t hlt.le, before_snoc c t hlt]
    exact hc l hlt

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-! # Regional balances throughout the occupied-cell expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
    (w : Scenario F N A a x y) (hF : a.M * (2 * a.D + 1) < Fintype.card F)
    {e : ℕ} (menu : a.Menu F N A e) (k : ℕ) (start : w.Code 0 menu)
    (hk : Frame.budget F a.chart a.g a.H a.M a.D a.U ≤ 2 ^ k)

abbrev CompleteRun := w.Run hF menu k start (w.Certified hF menu k start) a.waves le_rfl

include hk in
theorem run_balanced (hP : 0 < a.chart) (hH : 0 < a.H) : Nonempty (w.CompleteRun hF menu k start) := by
  apply w.run hF menu k start hk
  · intro j hj
    exact (Nat.not_lt_zero _ hj).elim
  · intro j c y hy hc
    obtain ⟨q, ht, hb, hv⟩ := w.step_balanced hF j y hk hP hH
    refine ⟨q, ht, fun i => ?_, hv⟩
    exact w.certified_snoc hF menu k start j c _ y (q i) hy
      ((ht i).trans (w.path_write hF menu k start hk j c y hy i).symm) (hb i) hc

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Scenario
end

/-! # The three selector fields carried at each occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Coloring
open scoped Classical

abbrev Journal (V : Type) (k w z : ℕ) := V → B k × (Fin w → B k) × B z

namespace Journal
variable {V : Type} {m h k w z : ℕ} (c : Journal V k w z) (loc : V ↪ B m × B h)

def join : (V → B k) × (Fin w → V → B k) × (V → B z) ≃ Journal V k w z where
  toFun t v := (t.1 v, fun i => t.2.1 i v, t.2.2 v)
  invFun f := (fun v => (f v).1, fun i v => (f v).2.1 i, fun v => (f v).2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def opening := Sparse.pack loc 0 (fun v => (c v).1)
def moves (i : Fin w) := Sparse.pack loc 0 (fun v => (c v).2.1 i)
def close (pad : B z) := Sparse.pack loc pad (fun v => (c v).2.2)

theorem card [Fintype V] : Fintype.card (Journal V k w z) = 2 ^ ((k + k * w + z) * Fintype.card V) := by
  simp only [Journal, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, pow_mul, pow_add, mul_assoc]

end Journal
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere SphereScale Surface.Local
variable {F V : Type} [Field F] {g ℓ D T b d p l k f : ℕ} (S : Scheme F)
    (sc : Scales g ℓ D T (p ^ l) b d) (z : S.format.obj) (loc : V ↪ B S.m × B S.h)

local notation "Cfg" => design S g ℓ D b d p l
local notation "e" => Format.width (panelQuery S g ℓ D b d p l k)

/-- Deterministic tape after a given prefix of any journal. -/
def page (c : Journal V k (Cfg).waves f) (i : ℕ) (hi : i ≤ (Cfg).waves) :
    ((Cfg).port ((Cfg).widthAt e k i)).obj :=
  (Cfg).path (panelTape S sc z (c.opening loc)) i (Scenario.before (c.moves loc) hi)

abbrev lastPage (c : Journal V k (Cfg).waves f) := page S sc z loc c (Cfg).waves le_rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Composing initialization, all waves, and the named printer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l : ℕ} [ExpChar F p] {W : ℝ}

section
variable (S : Scheme F)
local notation "Cfg" => design S g ℓ D b d p l

abbrev endWidth (g ℓ D b d p l k : ℕ) :=
  let a := design S g ℓ D b d p l
  a.widthAt (panelQuery S g ℓ D b d p l k).width k a.waves

abbrev LocalPrinter (g ℓ D b d p l k r t n u f : ℕ) :=
  let a := design S g ℓ D b d p l
  Print.Printer F (panelKeys a) (B S.k) S.m S.d S.h (endWidth S g ℓ D b d p l k)
    (chunks ℓ D) r t a.R D (Layout.Sharing.allocation g ℓ) n u (p ^ l) f

abbrev lastMenu (hK : Ready K ℓ D g (p ^ l) b d) (hF : (Cfg).M * (2 * (Cfg).D + 1) < Fintype.card F)
    (mobility : B S.ℓ → B S.k → Bool) (k : ℕ) :=
  (Cfg).menuAt hF (localMenu S hK mobility k) k (Cfg).waves le_rfl

end

variable {S : Scheme F} (P : Input F x y S.h D T (d * b) g W) {z : S.format.obj}
    (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)

local notation "Cfg" => design S g ℓ D b d p l

variable (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (mobility : B S.ℓ → B S.k → Bool) (k : ℕ) {r t n u f : ℕ}
    (U : LocalPrinter S g ℓ D b d p l k r t n u f)
    (status : (Print.Children.Header S.m S.d).obj) (pres : S.Presentation z P.diagram)

/-- Geometric and numerical conditions for one complete local expansion. -/
structure ReadyPanel : Prop where
  placed : P.Placed pres A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val)
    (fun v => mobility ((z v.1).2 v.2.1) v.2.2)
  directed : pres.Directed
  ranks : P.LocalRanks
  location : ∀ v, A.coord v = (A.host v.val.1, cellIndex S.h v.val.2)
  parents : Print.Children.Shows P.adj A.host (A.graph, status)
  populated : Nonempty P.V
  init : initialChoices ℓ D b d ≤ 2 ^ k
  waves : Frame.budget F (Cfg).chart (Cfg).g (Cfg).H (Cfg).M (Cfg).D (Cfg).U ≤ 2 ^ k
  first : d * b = chunks ℓ D * r
  second : d = chunks ℓ D * t
  menu : U.menu = printMenu S (lastMenu S hK hF mobility k) first second
  units : u * D ^ (terminalExponent g ℓ) ≤ T
  cap : terminalExponent g ℓ * D * T ≤ u * U.cap
  digits : depth ℓ D g (p ^ l) (d * b) < 2 ^ f

variable {P A sc hK hF mobility k U status pres}
    (h : P.ReadyPanel A hK hF mobility k U status pres)

abbrev InitialShapes (P : Input F x y S.h D T (d * b) g W) (ℓ : ℕ) :=
  P.Occupied → Shape (probes ℓ D) b d

variable (sc)

abbrev ReadyPanel.initial (s : P.InitialShapes ℓ) := P.localCode A sc hK s h.placed h.ranks h.init

abbrev ReadyPanel.Motion (s : P.InitialShapes ℓ) :=
  (P.localWorld A sc hK s).CompleteRun hF (localMenu S hK mobility k) k (h.initial sc s)

/-- The original selectors and term witnesses are retained in a nested finite family. -/
structure Expansion where
  motion : ∀ s, h.Motion sc s
  release : ∀ s i, U.NamedRelease pres ((motion s).code i).tape status
    ((P.localWorld A sc hK s).eval ((motion s).code i).frame) ℓ

def ReadyPanel.expand : Expansion sc h where
  motion s := ((P.localWorld A sc hK s).run_balanced hF _ k (h.initial sc s) h.waves sc.pos sc.Hpos).some
  release s _ := P.localNamedRelease A sc hK s pres h.placed h.directed _ U h.first h.second h.menu
    status h.location h.parents h.populated rfl rfl h.units h.cap h.digits

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Coding a complete expansion by one journal per occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.Expansion
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local Finset Transcript
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {sc : Scales g ℓ D T (p ^ l) b d} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}
    {h : P.ReadyPanel A hK hF mobility k U status pres} (E : Expansion sc h)

local notation "Cfg" => design S g ℓ D b d p l

abbrev I := Σ s, Σ i, (E.release s i).I

abbrev term (i : E.I) := (E.release i.1 i.2.1).term i.2.2
abbrev coeff (i : E.I) := (E.motion i.1).coeff i.2.1 * (E.release i.1 i.2.1).coeff i.2.2

theorem value (a : Val x) (b : Val y) :
    P.diagram.eval a b = ∑ i, E.coeff i * (E.term i).diagram.eval a b := by
  rw [P.start_sum A sc hK, Fintype.sum_sigma]
  refine sum_congr rfl fun s _ => ?_
  have hm := (E.motion s).value a b
  refine hm.trans ?_
  rw [Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => ?_
  rw [← (E.release s i).value, Finset.mul_sum]
  exact sum_congr rfl (fun j _ => (mul_assoc _ _ _).symm)

theorem vacant (s : P.InitialShapes ℓ) (i : (E.motion s).I) :
    ∀ v ∉ Set.range A.coord, U.menu ((((E.motion s).code i).tape v.1).2 v.2) = none := by
  intro v hv
  rw [h.menu]
  exact P.printMenu_away A sc hK s _ h.first h.second v hv

def lastIndex (s : P.InitialShapes ℓ) (i : (E.motion s).I) :=
  (E.release s i).localIndex A.coord (E.vacant s i)

def select : Selector E.I (Journal P.Occupied k (Cfg).waves U.digits) :=
  ((P.localIndex A h.init).bind fun s => (E.motion s).select.bind (E.lastIndex s)).relabel Journal.join

theorem card_le : Fintype.card E.I ≤ 2 ^ ((k + k * (Cfg).waves + U.digits) * Fintype.card P.Occupied) :=
  by
    have hc := Nat.card_le_card_of_injective E.select.write E.select.injective
    have he := Journal.card (V := P.Occupied) (k := k) (w := (Cfg).waves) (z := U.digits)
    simp only [← Nat.card_eq_fintype_card] at he ⊢
    exact hc.trans_eq he

theorem opening (i : E.I) :
    (E.select.write i).opening A.coord = (P.panelSelector A h.init).write i.1 :=
  Sparse.pack_sample _ _ (P.panel_supported A h.init i.1)

theorem moves (i : E.I) :
    (E.select.write i).moves A.coord = (P.localWorld A sc hK i.1).tapes ((E.motion i.1).select.write i.2.1) := rfl

theorem close (i : E.I) :
    (E.select.write i).close A.coord U.pad = (E.release i.1 i.2.1).select.write i.2.2 :=
  Sparse.pack_sample _ _ ((E.release i.1 i.2.1).supported A.coord (E.vacant i.1 i.2.1) i.2.2)

theorem written (i : E.I) :
    lastPage S sc z A.coord (E.select.write i) = ((E.motion i.1).code i.2.1).tape := by
  unfold lastPage page
  rw [Scenario.before_self, E.opening, E.moves]
  exact ((E.motion i.1).written i.2.1).symm

abbrev record (i : E.I) := U.advance (((E.motion i.1).code i.2.1).tape)
  status ((E.release i.1 i.2.1).select.write i.2.2)

abbrev shows (i : E.I) : U.template.Shows (E.record i) (E.term i) :=
  (E.release i.1 i.2.1).shows i.2.2

theorem record_eq (i : E.I) :
    E.record i = U.advance (lastPage S sc z A.coord (E.select.write i)) status
        ((E.select.write i).close A.coord U.pad) := by
  rw [E.written, E.close]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.Expansion
end

/-! # Parameters for the general ordered concentration controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

theorem selectorBits_le_polynomial {A D M T Q c : ℕ} (hQ : Q ≤ (T + 1) ^ c) :
    selectorBits A D M T Q ≤ (A + 2 * (c + 1)) * (1 + Nat.clog 2 (T + 1)) * ((D ^ 5 + 1) * (M + 1)) := by
  let t := Nat.clog 2 (T + 1)
  have hd : T + 1 ≤ 2 ^ t := Nat.le_pow_clog (by decide) _
  have hl : Nat.clog 2 (Q + 1) ≤ t * c + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ' 2 (t * c), pow_mul 2 t c]
    have hOne : 1 ≤ (T + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
    refine (Nat.add_le_add hQ hOne).trans ?_
    rw [← two_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)
  have hb : t * c + 1 ≤ (c + 1) * (1 + t) := by
    rw [add_mul, mul_add, one_mul, mul_one, mul_comm c t]
    omega
  unfold selectorBits
  apply Nat.mul_le_mul_right
  change A * (1 + t) + Nat.clog 2 (Q + 1) * 2 ≤ (A + 2 * (c + 1)) * (1 + t)
  rw [add_mul]
  apply Nat.add_le_add_left
  exact (Nat.mul_le_mul_right 2 (hl.trans hb)).trans_eq (by ring)

theorem layoutParameters (g ℓ D p l b : ℕ) :
    ∃ K₀ : ℕ, ∀ {T d n f : ℕ}, Scales g ℓ D T (p ^ l) b d →
      ∀ (F K : Type) [Field F] [Fintype F] [Field K] [Algebra K F] [ExpChar F p],
      (ready : Ready K ℓ D g (p ^ l) b d) →
      K₀ * (1 + T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ 2 ^ f →
      D = 2 ^ n → D ^ (terminalExponent g ℓ) ≤ T →
      ∀ (S : Scheme F) (mobility : B S.ℓ → B S.k → Bool),
      2 ^ (S.d + 1) ≤ D ^ (Layout.Sharing.allocation g ℓ) + 1 →
        let k := selectorBits K₀ D (room ℓ D g) T (Nat.card F)
        let u := T / D ^ (terminalExponent g ℓ)
        ∃ (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
          (r t : ℕ) (U : LocalPrinter S g ℓ D b d p l k r t n u f),
          U.cap = 2 * terminalExponent g ℓ * D * D ^ (terminalExponent g ℓ) ∧
            ∀ {x y : Wire} {W : ℝ} (P : Input F x y S.h D T (d * b) g W) {z : S.format.obj}
              (chart : P.HostChart S z)
              (status : (Print.Children.Header S.m S.d).obj)
              (pres : S.Presentation z P.diagram),
              P.Placed pres chart.coord (fun i => (chart.tone (2 * D ^ 5 + 2) i).val)
                (fun v => mobility ((z v.1).2 v.2.1) v.2.2) →
              pres.Directed → P.LocalRanks →
              (∀ v, chart.coord v = (chart.host v.val.1, cellIndex S.h v.val.2)) →
              Print.Children.Shows P.adj chart.host (chart.graph, status) → Nonempty P.V →
              P.ReadyPanel chart (hK := ready) hF mobility k U status pres := by
  obtain ⟨K₀, bounds⟩ := selector_bound g ℓ D (p ^ l) b
  refine ⟨K₀, ?_⟩
  intro T d n f sc F K _ _ _ _ _ ready fieldLo fieldHi hD hT S mobility degree
  dsimp only
  obtain ⟨field, initial, waves, _⟩ := bounds sc F
  let k := selectorBits K₀ D (room ℓ D g) T (Nat.card F)
  let C := terminalExponent g ℓ
  let u := T / D ^ C
  let cap := 2 * C * D * D ^ C
  have hf : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F := field.trans_le fieldLo
  have enough : depth ℓ D g (p ^ l) (d * b) < 2 ^ f := by
    have hm : 0 < room ℓ D g := by unfold SphereScale.room SphereScale.slots; positivity
    have hN : depth ℓ D g (p ^ l) (d * b) ≤ 2 * depth ℓ D g (p ^ l) (d * b) + 1 := by omega
    exact ((hN.trans (Nat.le_mul_of_pos_left _ hm)).trans_lt hf).trans_le fieldHi
  obtain ⟨uPos, lower, upper⟩ := floor_units (B:=D ^ C) (pow_pos sc.Dpos _) hT
  have hc : C * D * T ≤ u * cap := (Nat.mul_le_mul_left _ upper).trans_eq (by unfold cap u; ring)
  obtain ⟨t, ht⟩ := sc.divides
  let r := t * b
  have hr : d * b = chunks ℓ D * r := by rw [ht, mul_assoc]
  have hd4 : 4 ≤ D := (by decide : 4 ≤ 10000000).trans sc.bound
  let U : LocalPrinter S g ℓ D b d p l k r t n u f :=
    ⟨printMenu S (lastMenu S ready hf mobility k) hr ht, hD, hd4, sc.chunks_le,
      by simpa only [mul_one] using degree, cap, uPos⟩
  refine ⟨hf, r, t, U, rfl, ?_⟩
  intro x y W P z chart status pres placed directed ranks atCell parents populated
  exact ⟨placed, directed, ranks, atCell, parents, populated, initial, waves, hr, ht, rfl, lower, hc, enough⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Preparing the common printer for a supplied bundle dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

theorem ordered_parameters (g ℓ D p l b : ℕ) (hD : 2 * budget g ≤ D) :
    ∃ K₀ : ℕ, ∀ {T d n f : ℕ}, Scales g ℓ D T (p ^ l) b d →
      ∀ (F K : Type) [Field F] [Fintype F] [Field K] [Algebra K F] [ExpChar F p],
      (ready : Ready K ℓ D g (p ^ l) b d) →
      K₀ * (1 + T) ^ K₀ ≤ Fintype.card F → Fintype.card F ≤ 2 ^ f →
      D = 2 ^ n → D ^ (terminalExponent g ℓ) ≤ T →
      ∀ {a e : ℕ} (m h : ℕ) (read : BundleReader F a e),
        let S := bundleScheme read m h g D T
        let k := selectorBits K₀ D (room ℓ D g) T (Nat.card F)
        let u := T / D ^ (terminalExponent g ℓ)
        ∃ (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
          (r t : ℕ) (U : LocalPrinter S g ℓ D b d p l k r t n u f),
          U.cap = 2 * terminalExponent g ℓ * D * D ^ (terminalExponent g ℓ) ∧
            ∀ {x y : Wire} {W : ℝ} (P : Input F x y h D T (d * b) g W)
              (v : P.Seating m) (o : BundleOrder P.diagram read), Nonempty P.V →
                (v.ordered o).ReadyPanel (v.next o) ready hF (mobility a e g D T) k U v.tape.2 (v.pres o) := by
  obtain ⟨K₀, go⟩ := layoutParameters g ℓ D p l b
  refine ⟨K₀, ?_⟩
  intro T d n f sc F K _ _ _ _ _ ready lo hi dyad ht a e m h read
  obtain ⟨hf, r, t, U, hc, hh⟩ := go sc F K ready lo hi dyad ht (bundleScheme read m h g D T)
    (mobility a e g D T) (channel_cap hD)
  refine ⟨hf, r, t, U, hc, ?_⟩
  intro x y W P v o populated
  exact hh (v.ordered o) (v.next o) v.tape.2 (v.pres o)
    (v.placed o) (v.directed o) (v.ranks o) (v.location o) (v.parents o) populated

namespace Seating
variable {F : Type} [Field F] {x y : Wire} {h D T R g a e m : ℕ} {W : ℝ}
    {P : Input F x y h D T R g W} {read : BundleReader F a e}
    (v : P.Seating m) (o : BundleOrder P.diagram read)

theorem return_concentrated {u C d ℓ : ℕ} {Z : LocalTerm F x y h u}
    (hz : Concentrated (v.ordered o) Z C d ℓ) : Concentrated P Z C d ℓ :=
  ⟨hz.cells, hz.coreDegree, hz.fullDegree, hz.frozenCount, hz.frozenMax, hz.frozenSquare, hz.coreMax, hz.coreSum⟩

end Seating
end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Factoring the expansion into one weight per occupied cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local Finset Transcript
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {sc : Scales g ℓ D T (p ^ l) b d} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}
    {h : P.ReadyPanel A hK hF mobility k U status pres} (E : Expansion sc h)

local notation "Cfg" => design S g ℓ D b d p l

section
variable (S sc hK hF mobility U z) {V : Type} (loc : V ↪ B S.m × B S.h)

def journalWeight (c : Journal V k (Cfg).waves U.digits) (v : B S.m × B S.h) : F :=
  panelGuard S sc k ((panelAround S sc z (c.opening loc) v.1).2 v.2) *
  ((Cfg).localCharge (panelTape S sc z (c.opening loc)) hF (localMenu S hK mobility k)
    (Cfg).waves le_rfl (c.moves loc) v *
    U.tariff ((U.around (lastPage S sc z loc c) (c.close loc U.pad) v.1).2 v.2))

end

namespace Expansion

theorem valid (c : Journal P.Occupied k (Cfg).waves U.digits) :
    (∏ v, journalWeight S z sc hK hF mobility U A.coord c (A.coord v)) =
      (E.select.read c).elim 0 E.coeff := by
  obtain ⟨⟨i, j, t⟩, rfl⟩ := Journal.join.surjective c
  let ini := P.localIndex A h.init
  let c := Journal.join (i, j, t)
  simp only [select, Selector.relabel, Equiv.symm_apply_apply]
  change (∏ v, journalWeight S z sc hK hF mobility U A.coord c (A.coord v)) =
    ((ini.read i).bind (fun b =>
      (((E.motion b).select.read j).bind fun l => ((E.lastIndex b l).read t).map (Sigma.mk l)).map
        (Sigma.mk b))).elim 0 E.coeff
  have hi := (P.guard_occupied A sc h.placed i).symm.trans (P.localWeight A sc h.placed h.init _)
  change (∏ v, panelGuard S sc k ((panelAround S sc z (c.opening A.coord) (A.coord v).1).2 (A.coord v).2)) =
    (ini.read i).elim 0 (fun _ => 1) at hi
  simp only [journalWeight, prod_mul_distrib, hi]
  cases e : ini.read i with
  | none => simp
  | some b =>
    have hb := (ini.valid _ _).mp e
    let w := P.localWorld A sc hK b
    have open_eq : panelTape S sc z (c.opening A.coord) = (h.initial sc b).tape := by
      change panelTape S sc z (Sparse.pack A.coord 0 i) = _
      rw [hb]
      exact congrArg _ (Sparse.pack_sample _ _ (P.panel_supported A h.init b))
    have moves_eq : c.moves A.coord = w.tapes j := rfl
    have hm := (w.charge_occupied hF _ (h.initial sc b) _ le_rfl j).symm.trans ((E.motion b).valid j)
    rw [open_eq, moves_eq]
    erw [hm]
    simp only [Option.elim_some, Option.bind_some, one_mul]
    cases ej : (E.motion b).select.read j with
    | none => simp
    | some l =>
      have hl := ((E.motion b).select.valid _ _).mp ej
      have hw : lastPage S sc z A.coord c = ((E.motion b).code l).tape := by
        unfold lastPage page
        rw [Scenario.before_self, open_eq, moves_eq, hl]
        exact ((E.motion b).written l).symm
      rw [hw]
      have hf := (U.score_occupied _ A.coord (E.vacant b l) t).symm.trans ((E.release b l).valid _)
      change (∏ v, U.tariff ((U.around ((E.motion b).code l).tape (c.close A.coord U.pad)
        (A.coord v).1).2 (A.coord v).2)) = ((E.lastIndex b l).read t).elim 0 (E.release b l).coeff at hf
      rw [hf]
      simp only [Option.elim_some, Option.bind_some]
      cases (E.lastIndex b l).read t <;> simp [coeff]

end Expansion
end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end
