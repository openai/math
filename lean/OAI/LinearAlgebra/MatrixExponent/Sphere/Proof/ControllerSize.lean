import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.ScalarHost
import OAI.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Decoding
import OAI.LinearAlgebra.MatrixExponent.Sphere.Copy.Overlay
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Accept
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior

/-! # Uniform sizes of the fixed parts of a binary controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere SphereScale Surface.Local Geometry
open scoped Classical

def wordWidth (D T : ℕ) := Nat.clog 2 (100 * D * T + 1)

theorem wordWidth_bounds (D T f : ℕ) (hT : T ≤ 2 ^ f) :
    100 * D * T < 2 ^ wordWidth D T ∧ wordWidth D T ≤ f + Nat.clog 2 (100 * D + 1) := by
  refine ⟨Nat.le_pow_clog (by decide) _, Nat.clog_le_of_le_pow ?_⟩
  rw [pow_add, mul_comm (2 ^ f)]
  exact (Nat.add_le_add (Nat.mul_le_mul_left _ hT) (Nat.one_le_pow _ _ (by decide))).trans
    ((by rw [add_mul, one_mul] : 100 * D * 2 ^ f + 2 ^ f ≤ (100 * D + 1) * 2 ^ f).trans
      (Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide : 1 < 2) (100 * D + 1))))

namespace Controller

def core (g ℓ D n A deg seats : ℕ) :=
  let W := Neighborhood.paletteSize deg (2 * D ^ 5 + 2) * room ℓ D g
  let R := (W + 1) * (2 * D ^ 5 + 4)
  growth g ℓ D n A deg seats + 2 ^ seats +
    indexWidth (Credits g ℓ D W) + indexWidth (Credits.Caps g ℓ D W) +
    R + 2 ^ ((deg + 1) * R) + Nat.clog 2 (100 * D + 1) + 1

def tag (J : ℕ) := J * J + J
def check (J : ℕ) := J + J + (1 + J * J + J) * tag J
def flags (J : ℕ) := J + J * (J + 1) + J * J + J * J * (J * J + 1) + J * J
def keys (J : ℕ) := J * 2 + 1
def reader (J : ℕ) :=
  (3 * tag J + 2) * J + 1 + ((3 * (tag J + keys J) + 2) * (J * 2 ^ keys J) + 1)

theorem flags_bound {w d e k J : ℕ} (hw : 2 ^ w ≤ J) (hd : 2 ^ d ≤ J)
    (he : 2 ^ e ≤ J) (hk : 2 ^ k ≤ J) :
    Fintype.card (Blueprint.Flags w d e k) ≤ flags J := by
  simp only [Blueprint.Flags, flags, Fintype.card_sum, Fintype.card_prod, Fintype.card_option,
    Fintype.card_fin, pow_zero, one_mul, add_assoc, mul_assoc]
  gcongr

theorem keys_bound {k J : ℕ} (hk : 2 ^ k ≤ J) : Fintype.card (Blueprint.LengthKey k) ≤ keys J := by
  simp only [Blueprint.LengthKey, keys, Fintype.card_prod, Fintype.card_option, Fintype.card_bool, Fintype.card_fin]
  gcongr

theorem reader_bound {T X : Type} [Fintype T] [Fintype X] {k J : ℕ}
    (hk : 2 ^ k ≤ J) (ht : Nat.card T ≤ J) (hx : Fintype.card X ≤ tag J) :
    Blueprint.readCost T X k ≤ reader J := by
  have hy := keys_bound hk
  rw [Nat.card_eq_fintype_card] at ht
  simp only [Blueprint.readCost, reader, Fintype.card_prod, Fintype.card_sum, Fintype.card_fun, Fintype.card_bool]
  gcongr

end Controller

variable {F : Type} [Field F] (S : Scheme F) {g ℓ D b d p l k r t n u f A : ℕ}
    (U : LocalPrinter S g ℓ D b d p l k r t n u f)
local notation "Cfg" => design S g ℓ D b d p l
local notation "W" => Design.waves Cfg

abbrev readerFlags := Blueprint.Flags U.childBits U.template.scheme.d U.spanBits S.k

abbrev readUnit := Blueprint.readCost (U.Tag S g ℓ W) (U.tagPins S g ℓ W) S.k

structure CoreBounds (J : ℕ) : Prop where
  growth : GrowthBounds S U J
  seats : 2 ^ S.k ≤ J
  rounds : Copy.radius Cfg ≤ J
  reach : 2 ^ ((S.d + 1) * Copy.radius Cfg) ≤ J
  digit : Nat.clog 2 (100 * D + 1) + 1 ≤ J
  tag : U.tagWidth S g ℓ W ≤ Controller.tag J
  check : U.checkWidth S g ℓ Cfg ≤ Controller.check J
  flags : Fintype.card (readerFlags S U) ≤ Controller.flags J
  keys : Fintype.card (Blueprint.LengthKey S.k) ≤ Controller.keys J
  reader : readUnit S U ≤ Controller.reader J

private theorem GrowthBounds.mono {i j : ℕ} (h : GrowthBounds S U i) (le : i ≤ j) :
    GrowthBounds S U j :=
  ⟨h.waves.trans le, h.radius.trans le, h.child.trans le, h.span.trans le, h.degree.trans le,
    h.plan.trans le, h.tags.trans le, h.selectors.trans (Nat.mul_le_mul_right _ le),
    h.address.trans (Nat.mul_le_mul_right _ le)⟩

private theorem core_parts {J a b c d x y z : ℕ} (h : J = a + b + c + d + x + y + z + 1) :
    a ≤ J ∧ b ≤ J ∧ c ≤ J ∧ d ≤ J ∧ x ≤ J ∧ y ≤ J ∧ z + 1 ≤ J := by omega

theorem core_bounds (h : GrowthBounds S U (growth g ℓ D n A S.d S.k)) :
    CoreBounds S U (Controller.core g ℓ D n A S.d S.k) := by
  let J := Controller.core g ℓ D n A S.d S.k
  have hj : J = growth g ℓ D n A S.d S.k + 2 ^ S.k + indexWidth (Credits g ℓ D W) +
      indexWidth (Credits.Caps g ℓ D W) + Copy.radius Cfg + 2 ^ ((S.d + 1) * Copy.radius Cfg) +
        Nat.clog 2 (100 * D + 1) + 1 := rfl
  obtain ⟨hJ, hk, hc₁, hc₂, hr, he, hz⟩ := core_parts hj
  have hg : GrowthBounds S U J := h.mono S U hJ
  have ht : U.tagWidth S g ℓ W ≤ Controller.tag J :=
    Nat.add_le_add (Nat.mul_le_mul hg.child hg.plan) hc₁
  have hc : U.checkWidth S g ℓ Cfg ≤ Controller.check J :=
    Nat.add_le_add (Nat.add_le_add hk hc₂)
      (Nat.mul_le_mul (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul hg.child hg.degree) 1) hg.radius) ht)
  change CoreBounds S U J
  refine ⟨hg, hk, hr, he, hz, ht, hc, Controller.flags_bound hg.child hg.degree hg.span hk,
    Controller.keys_bound hk, ?_⟩
  exact Controller.reader_bound hk hg.tags ((U.tagSize S g ℓ W).le.trans ht)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Linear work and constant round bound for the binary controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere SphereScale Surface.Local Geometry
open scoped Classical

namespace Controller

def formula (n : ℕ) := (3 * n + 2) * 2 ^ n + 1

private theorem mono_formula : Monotone formula := by
  intro a b h
  unfold formula
  gcongr

def tests (J : ℕ) := formula (tag J) + formula (check J) + tag J + check J + 2

def read (J : ℕ) := (reader J * (flags J + J * J) + tag J + keys J + flags J + J * J) * J

def copies (J : ℕ) := (J + 1) * J * (J * (J + J) + check J)

def bound (J : ℕ) := tests J + read J + copies J + (1 + J + tag J)

theorem bound_parts (J : ℕ) : J ≤ bound J ∧ J + tag J ≤ bound J := by
  unfold bound
  omega

end Controller

def controllerBound (g ℓ D n A deg seats : ℕ) := Controller.bound (Controller.core g ℓ D n A deg seats)

variable {F : Type} [Field F] (S : Scheme F) {g ℓ D b d p l k r t n u f : ℕ}
    (U : LocalPrinter S g ℓ D b d p l k r t n u f)

local notation "Cfg" => design S g ℓ D b d p l
local notation "W" => Design.waves Cfg
local notation "tag" => Print.Printer.tagWidth S U g ℓ W
local notation "chk" => Print.Printer.checkWidth S U g ℓ Cfg
local notation "rad" => Copy.radius Cfg

/-- Both validity formulas, their input pins and their outputs. -/
def controllerChecks := Controller.formula tag + Controller.formula chk + tag + chk + 2

/-- Truth-table work for the complete reader, plus its input and output pins. -/
def controllerRead (w : ℕ) :=
  let a := Fintype.card (readerFlags S U)
  let b := 2 ^ U.childBits * 2 ^ U.spanBits
  readUnit S U * (a + b) * (w + 1) + (tag + Fintype.card (Blueprint.LengthKey S.k) * w) + (a + b * w)

/-- Registers for both label deliveries and for the verifier inputs.
The ball factor allows all requests visiting a host to be counted there. -/
def controllerCopies := (rad + 1) * 2 ^ ((S.d + 1) * rad) * (2 ^ U.childBits * (U.addressBits S + U.labelBits) + chk)

def controllerWork (w : ℕ) :=
  controllerChecks S U + controllerRead S U w + controllerCopies S U + (1 + S.ℓ + U.labelBits + tag + f)

structure ControllerBounds (T H : ℕ) : Prop where
  rounds : rad ≤ H
  selectors : k + k * W + U.digits + tag ≤ H * (1 + f)
  count : k + k * W + U.digits + Nat.clog 2 (Nat.card (U.Tag S g ℓ W)) ≤ H * (1 + f)
  address : U.addressBits S ≤ H * (1 + S.ℓ + f)
  work : controllerWork S U (wordWidth D T) ≤ H * (1 + S.ℓ + f)

private theorem reader_le {a b c l t w : ℕ} :
    c * (a + b) * (w + 1) + (t + l * w) + (a + b * w) ≤ (c * (a + b) + t + l + a + b) * (w + 1) := by
  rw [add_mul, add_mul, add_mul, add_mul]
  simp only [mul_add, mul_one]
  omega

/-- The bound is independent of the number of occurrences, field,
long record widths and species counts. -/
theorem controller_bounds {A T : ℕ}
    (hc : U.cap = 2 * terminalExponent g ℓ * D * D ^ terminalExponent g ℓ)
    (hk : k ≤ slope A D (room ℓ D g) * (1 + f)) (hT : T ≤ 2 ^ f) :
    ControllerBounds S U T (controllerBound g ℓ D n A S.d S.k) := by
  let J := Controller.core g ℓ D n A S.d S.k
  have h : CoreBounds S U J := core_bounds S U (growth_bounds S U hc hk)
  have hb := h.growth
  have hp := Controller.bound_parts J
  let X := 1 + S.ℓ + f
  have hX : 0 < X := by unfold X; omega
  have lift (z : ℕ) : z ≤ z * X := Nat.le_mul_of_pos_right z hX
  have word : wordWidth D T + 1 ≤ J * X := by
    have hw := (wordWidth_bounds D T f hT).2
    have he := h.digit
    have hJ : 0 < J := lt_of_lt_of_le (Nat.succ_pos _) he
    have hf := Nat.le_mul_of_pos_left f hJ
    unfold X
    rw [mul_add, mul_add, mul_one]
    omega
  have label : U.labelBits ≤ J * X := le_trans
    ((Nat.le_add_right _ _).trans (Nat.le_add_left _ _)) hb.address
  have tags := h.tag
  have checks := h.check
  have child := hb.child
  have span := hb.span
  have ct : controllerChecks S U ≤ Controller.tests J * X := by
    apply le_trans _ (lift _)
    unfold controllerChecks Controller.tests
    have t := Controller.mono_formula tags
    have c := Controller.mono_formula checks
    omega
  have cr : controllerRead S U (wordWidth D T) ≤ Controller.read J * X := by
    unfold controllerRead Controller.read
    rw [mul_assoc _ J X]
    refine reader_le.trans (Nat.mul_le_mul ?_ word)
    have pair := Nat.mul_le_mul child span
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul h.reader (Nat.add_le_add h.flags pair)) tags)
        h.keys) h.flags) pair
  have cp : controllerCopies S U ≤ Controller.copies J * X := by
    have hh : U.addressBits S ≤ J * X := hb.address
    have reach := Nat.mul_le_mul (Nat.add_le_add_right h.rounds 1) h.reach
    have bits := Nat.mul_le_mul child (Nat.add_le_add hh label)
    unfold controllerCopies Controller.copies
    calc
      _ ≤ (J + 1) * J * (J * (J * X + J * X) + Controller.check J * X) :=
        Nat.mul_le_mul reach (Nat.add_le_add bits (checks.trans (lift _)))
      _ = _ := by simp only [add_mul, mul_assoc]
  have cs : 1 + S.ℓ + U.labelBits + tag + f ≤ (1 + J + Controller.tag J) * X := by
    have ht := tags.trans (lift _)
    rw [add_mul, add_mul, one_mul]
    unfold X at *
    omega
  change ControllerBounds S U T (Controller.bound J)
  refine ⟨h.rounds.trans hp.1, ?_, hb.selectors.trans (Nat.mul_le_mul_right _ hp.1),
    hb.address.trans (Nat.mul_le_mul_right _ hp.1), ?_⟩
  · refine le_trans ?_ (Nat.mul_le_mul_right (1 + f) hp.2)
    rw [add_mul]
    exact Nat.add_le_add ((Nat.le_add_right _ _).trans hb.selectors)
      (tags.trans (Nat.le_mul_of_pos_right _ (by omega)))
  · change _ ≤ Controller.bound J * X
    unfold controllerWork Controller.bound
    rw [add_mul, add_mul, add_mul]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ct cr) cp) cs

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # One copy schedule for all proposed histories and layouts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Copy.Plan
open Coloring
open scoped Classical

variable {Ω I : Type*} {m h d r : ℕ} {src src' : Source Ω m h} {nav : B m → B d → B m}
    {dest : I → Sites m h} {value : I → Ω → Bool}

def widen (p : Plan src nav r dest value) (hs : ∀ v, src v ⊆ src' v) :
    Plan src' nav r dest value :=
  {p with start := fun i => (p.start i).imp_right (fun hi => hs _ hi)}

def load [Fintype I] (p : Plan src nav r dest value) (v : Sites m h) :=
  Fintype.card {t : p.Event // p.site t = v}

theorem sigma_load {V : Type} [Fintype V] (loc : V ↪ Sites m h) (Q : V → Type) [∀ v, Fintype (Q v)]
    {out : (Σ v, Q v) → Ω → Bool} (p : Plan src nav r (fun i : Σ v, Q v => loc i.1) out)
    {n : ℕ} (hn : ∀ v, Nat.card (Q v) ≤ n) (v : Sites m h) :
    p.load v ≤ (r + 1) * 2 ^ ((d + 1) * r) * n := by
  simp only [Nat.card_eq_fintype_card] at hn
  let idAt (w : V) : Q w ↪ Fin n := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (hn w))
  let slot (i : Σ v, Q v) := idAt i.1 i.2
  have inj : Function.Injective (fun i : Σ v, Q v => (loc i.1, slot i)) := by
    rintro ⟨x, a⟩ ⟨y, b⟩ eq
    obtain ⟨hl, hs⟩ := Prod.mk.inj eq
    have he : x = y := loc.injective hl
    subst y
    exact congrArg (Sigma.mk x) ((idAt x).injective hs)
  have hw := p.congestion slot inj v
  rw [Fintype.card_fin] at hw
  exact hw

end OAI.LinearAlgebra.MatrixExponent.Sphere.Copy.Plan

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}
    (h : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

local notation "Cfg" => design S g ℓ D b d p l
local notation "R" => Copy.radius Cfg

abbrev Assignment := h.Book × (P.Occupied → h.Guess)

abbrev resources : Copy.Source h.Assignment S.m S.h :=
  Copy.sources S U (fun _ => z) A.coord Prod.fst Prod.snd

abbrev proposed (a : h.Assignment) :=
  U.overlay S z (h.printing sc a.1) (U.complete S A.coord (fun i => (a.2 i).1))

variable (c₀ : h.Book)

structure Program where
  raw : Copy.Delivery A.coord (Copy.Code.final S U)
    (fun a i => ((h.printing sc a.1).1 i).2) h.resources A.graph R
  overlay : Copy.Delivery A.coord (Copy.Code.overlay S U)
    (fun a i => ((h.proposed sc a).1 i).2) h.resources A.graph R
  checks : Copy.Plan h.resources A.graph ((Cfg).U + 1)
    (fun i : h.requests sc => A.coord i.1) (fun i a => h.checkInputs sc c₀ a.2 i.1 i.2)

def program : h.Program sc c₀ where
  raw := (Copy.rawDelivery S U sc (fun _ : h.Assignment => z) A.coord Prod.fst (fun _ => status)
    U.pad (fun _ _ => rfl) A.sym).widen (fun _ => Set.subset_union_left)
  overlay := Copy.overlayDelivery S U sc (fun _ : h.Assignment => z) A.coord Prod.fst (fun _ => status)
    U.pad (fun _ _ => rfl) A.sym Prod.snd
  checks := h.checkPlan sc c₀ Prod.snd (fun v i => .inr ⟨v, rfl, i, rfl⟩)

variable {h sc c₀} (w : h.Program sc c₀)

theorem Program.legal (hx : NoExtras A status) :
    w.raw.On A.host P.adj ∧ w.overlay.On A.host P.adj ∧ w.checks.On A.host P.adj :=
  ⟨h.deliveries hx w.raw, h.deliveries hx w.overlay,
    w.checks.on_host A.host P.adj A.sym (h.nav_suitable hx) (fun i => ⟨i.1.val.1, rfl⟩)⟩

private theorem radius_le (a : Surface.Local.Design) : a.U + 1 ≤ Copy.radius a :=
  le_trans (show a.U + 1 ≤ 2 * a.U + 4 by omega) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

theorem Program.cost_delivery (v : Copy.Sites S.m S.h) :
    w.raw.load v + w.overlay.load v + w.checks.load v ≤ controllerCopies S U := by
  have hh : ∀ v, Nat.card (h.checkPins sc v) ≤ U.checkWidth S g ℓ Cfg := by
    intro v
    have hg := U.check_size S (P.localWorld A sc hK h.zeroShape) g ℓ v
    rw [← Nat.card_eq_fintype_card] at hg
    exact hg
  have he := Copy.Plan.sigma_load A.coord (h.checkPins sc) w.checks hh v
  have hw := radius_le Cfg
  let q := (R + 1) * 2 ^ ((S.d + 1) * R)
  have ht : w.checks.load v ≤ q * U.checkWidth S g ℓ Cfg := by
    refine he.trans ?_
    unfold q
    gcongr
  have hd : w.raw.load v ≤ q * (2 ^ U.childBits * U.labelBits) := w.raw.bounds.2.2 v
  have hu : w.overlay.load v ≤ q * (2 ^ U.childBits * U.addressBits S) := w.overlay.bounds.2.2 v
  refine (Nat.add_le_add (Nat.add_le_add hd hu) ht).trans_eq ?_
  change _ = q * (2 ^ U.childBits * (U.addressBits S + U.labelBits) + U.checkWidth S g ℓ Cfg)
  ring

theorem Program.total_delivery :
    Fintype.card w.raw.Event + Fintype.card w.overlay.Event + Fintype.card w.checks.Event ≤
      Fintype.card P.Occupied * controllerCopies S U := by
  have hw := radius_le Cfg
  have hc := h.requests_bound sc
  let q := (R + 1) * 2 ^ ((S.d + 1) * R)
  have hq : R + 1 ≤ q := Nat.le_mul_of_pos_right _ (by positivity)
  have hv : (Cfg).U + 1 + 1 ≤ q := (Nat.add_le_add_right hw 1).trans hq
  have ht := Nat.mul_le_mul hv hc
  rw [w.raw.bounds.1, w.overlay.bounds.1, w.checks.copies]
  refine (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ hq) (Nat.mul_le_mul_right _ hq)) ht).trans_eq ?_
  change _ = _ * (q * (2 ^ U.childBits * (U.addressBits S + U.labelBits) + U.checkWidth S g ℓ Cfg))
  ring

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Reading a proposed geometry from the local selector and old lengths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "L" => wordWidth D T
local notation "waves" => Design.waves (design S g ℓ D b d p l)
local notation "Pins" => Blueprint.ReadIn (U.tagPins S g ℓ waves) S.k L
local notation "Out" => Blueprint.ReadOut (readerFlags S U) U.childBits U.spanBits L

variable (h : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

include h in
theorem exterior_fits (i : B S.m) (j : B S.h) (a : Option (B S.k)) (b₀ : Bool) :
    S.extWidth ((z i).2 j) a b₀ < 2 ^ L := by
  refine lt_of_le_of_lt (b := 100 * D * T) ?_ (Nat.le_pow_clog (by decide) _)
  cases a with
  | none => exact Nat.zero_le _
  | some a =>
    let v : S.Vtx := (i, j, a)
    change S.extWidth ((z v.1).2 v.2.1) (some v.2.2) b₀ ≤ _
    by_cases hz : S.extWidth ((z v.1).2 v.2.1) (some v.2.2) b₀ = 0
    · rw [hz]; exact Nat.zero_le _
    obtain ⟨e, he, _⟩ := (pres.extWidth_ne_zero h.directed v b₀).mp hz
    let w := Packing.portEnd P.diagram e
    have hw : pres.vertex w = v := (Payload.owner pres e).symm.trans he
    rw [← hw, ← pres.exterior_width h.directed w b₀]
    have mass : (P.diagram.arity w : ℝ) ≤ 100 * D * T := by
      refine le_trans ?_ (P.mass (P.place w))
      unfold Packing.push
      simpa using Finset.single_le_sum (s := Finset.univ)
        (f := fun v => if P.place v = P.place w then (P.diagram.arity v : ℝ) else 0)
        (fun _ _ => by positivity) (Finset.mem_univ w)
    refine le_trans (b := P.diagram.arity w) ?_ (by exact_mod_cast mass)
    cases b₀
    · exact (List.length_filterMap_le Diagram.pickLeft _).trans_eq List.length_ofFn
    · exact (List.length_filterMap_le Diagram.pickRight _).trans_eq List.length_ofFn

include h sc in
theorem unit_fits : u < 2 ^ L := by
  refine lt_of_le_of_lt (b := 100 * D * T) ?_ (Nat.le_pow_clog (by decide) _)
  have hd := sc.Dpos
  exact le_trans ((Nat.le_mul_of_pos_right _ (by positivity)).trans h.units)
    (Nat.le_mul_of_pos_left _ (by positivity))

private def digit (m : ℕ) (i : Fin L) := m.testBit i.val

def readerInput (c : h.Paths sc) (v : P.Occupied) : Pins → Bool :=
  Blueprint.readIn (U.tagCode S g ℓ waves) L digit (c.2.val v) u
    (S.extWidth ((z (A.coord v).1).2 (A.coord v).2))

def readerOutput (c : h.Paths sc) (v : P.Occupied) : Out → Bool :=
  let o := A.coord v
  Sum.elim (Blueprint.flags (h.geometry sc c o.1 o.2))
    (fun i => digit ((U.revised S).scheme.width (h.data sc c).1 (U.centerAt S o.1 o.2 i.1, i.2.1)) i.2.2)

/-- One family of formulas reads all occupied cells of every admissible path.
The word bounds ensure that every reported length is represented in full. -/
def Reader : Prop :=
  u < 2 ^ L ∧
  (∀ i j a side, S.extWidth ((z i).2 j) a side < 2 ^ L) ∧
  (∀ (c : h.Paths sc) (v : U.Actors S) (s : B U.spanBits), (U.revised S).scheme.width (h.data sc c).1 (v, s) < 2 ^ L) ∧
  ∃ a : Out → BitFormula Pins,
    (∀ c v i, (a i).eval (h.readerInput sc c v) = h.readerOutput sc c v i) ∧
      (∑ i, (a i).cost) + Fintype.card Pins + Fintype.card Out ≤ controllerRead S U L

private theorem reader_eq (c : h.Paths sc) (v : P.Occupied) :
    Blueprint.readOut (fun a : h.Guess => a.1) (fun a => Blueprint.flags a.1) U.outer L digit
      (c.2.val v) u (S.extWidth ((z (A.coord v).1).2 (A.coord v).2)) = h.readerOutput sc c v := by
  let o := A.coord v
  have eq : h.geometry sc c o.1 o.2 = (c.2.val v).1 := U.complete_here S A.coord _ v
  funext i
  rcases i with i|⟨q, s, j⟩
  · exact congrArg (fun a => Blueprint.flags a i) eq.symm
  · change digit _ j = digit ((U.revised S).scheme.width (h.data sc c).1 (U.centerAt S o.1 o.2 q, s)) j
    rw [data, U.width_overlay, U.local_center, U.original_center, eq]

theorem reader : h.Reader sc := by
  refine ⟨h.unit_fits sc, h.exterior_fits, ?_, ?_⟩
  · intro c v s
    rw [data, U.width_overlay]
    unfold Outline.width
    split_ifs
    · exact h.unit_fits sc
    · exact h.exterior_fits _ _ _ _
    · exact h.exterior_fits _ _ _ _
    · positivity
  obtain ⟨a, ha, _, hc⟩ := Blueprint.read_net (U.tagCode S g ℓ waves)
    (fun a => a.1) (fun a => Blueprint.flags a.1) U.outer L digit
  refine ⟨a, ?_, ?_⟩
  · intro c v i
    rw [← h.reader_eq sc c v]
    exact ha (c.2.val v) u _ (fun _ => rfl) i
  · have hi : Fintype.card Pins = U.tagWidth S g ℓ waves + Fintype.card (Blueprint.LengthKey S.k) * L := by
      unfold Blueprint.ReadIn
      rw [Fintype.card_sum, U.tagSize, Fintype.card_prod, Fintype.card_fin]
    have ho : Fintype.card Out = Fintype.card (readerFlags S U) + 2 ^ U.childBits * 2 ^ U.spanBits * L := by
      unfold Blueprint.ReadOut
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod]
      simp only [B, Fintype.card_fin, mul_assoc]
    rw [hi, ho]
    exact Nat.add_le_add_right (Nat.add_le_add_right hc _) _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-! # Checks and communication on a fixed host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}
variable (h sc)

/-- The short checks do not inspect tables or long labels. Copies
and transmissions are counted even at sites used only as relays. -/
structure Binary : Prop where
  tags : ∃ tag : BitFormula (U.tagPins S g ℓ (Cfg).waves),
    tag.cost ≤ Controller.formula (U.tagWidth S g ℓ (Cfg).waves) ∧
    ∀ v, tag.eval v = true ↔ ∃ b, U.tagCode S g ℓ (Cfg).waves b = v
  check : ∀ c₀ : h.Book, ∃ test : ∀ v, BitFormula (h.checkPins sc v),
    (∀ v, (test v).cost ≤ Controller.formula (U.checkWidth S g ℓ Cfg)) ∧
    ∀ c a, h.admissible sc c a ↔ ∀ v, (test v).eval (h.checkInputs sc c₀ a v) = true
  delivery : ∀ c₀ : h.Book, ∃ w : h.Program sc c₀,
    w.raw.On A.host P.adj ∧ w.overlay.On A.host P.adj ∧ w.checks.On A.host P.adj ∧
    (∀ v, w.raw.load v + w.overlay.load v + w.checks.load v ≤ controllerCopies S U) ∧
    Fintype.card w.raw.Event + Fintype.card w.overlay.Event + Fintype.card w.checks.Event ≤
      Fintype.card P.Occupied * controllerCopies S U

theorem binary (hn : NoExtras A status) : h.Binary sc := by
  refine ⟨U.valid_formula S g ℓ (Cfg).waves, h.admissible_binary sc, ?_⟩
  intro c₀
  let w := h.program sc c₀
  obtain ⟨h₁, h₂, h₃⟩ := w.legal hn
  exact ⟨w, h₁, h₂, h₃, w.cost_delivery, w.total_delivery⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end

/-!
# Local concentration with binary bookkeeping

The visible indices specify a layout and a bounded credit account
for every occupied occurrence. The identity sums over exactly the
admitted bit strings, including those carrying zero coefficients.
Long labels are copied. Only the table dictionary evaluates the
interpolation coefficients and compares the proposal with the
underlying sphere expansion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}
variable (h sc)

/-- Bounds for one common template and every term on it. -/
structure Bookkeeping (B a : ℕ) : Prop where
  identity : ∀ v w, P.diagram.eval v w = ∑ c : h.Paths sc, (h.summand sc c).diagram.eval v w
  bounded : ∀ c : h.Paths sc, Concentrated P (h.summand sc c) (exponent g ℓ) n ℓ
  trivalent : ∀ (c : h.Paths sc) v, ((h.summand sc c).frame.C v).card ≤ 3
  count : Nat.card (h.Paths sc) ≤ 2 ^ ((B * (1 + Nat.clog 2 (T + 1))) * Fintype.card P.Occupied)
  selectors : Fintype.card h.ControlPins ≤ B * (1 + Nat.clog 2 (T + 1))
  unique : Function.Injective (h.controls sc)
  valid : ∀ c₀ bits, bits ∈ Set.range (h.controls sc) ↔
    ∃ a' : P.Occupied → h.Guess,
      (∀ v, U.tagCode S g ℓ (Cfg).waves (a' v) = bits v ∘ Sum.inr) ∧ h.admissible sc c₀ a'
  slots : Fintype.card (ChildSlot g ℓ D n) ≤ D ^ (terminalExponent g ℓ) + 1
  common : ∀ c c' : h.Paths sc,
    (h.summand sc c).V = (h.summand sc c').V ∧
    (h.summand sc c).frame.N = (h.summand sc c').frame.N ∧
    (h.summand sc c).frame.C = (h.summand sc c').frame.C ∧
    (h.summand sc c).frame.frozen = (h.summand sc c').frame.frozen
  nearby : ∀ (c : h.Paths sc) v w, w ∈ (h.summand sc c).frame.N v →
    h.scalarParent sc c w ∈ insert (h.scalarParent sc c v) (P.adj (h.scalarParent sc c v))
  exterior : ∀ (c : h.Paths sc) (i : MatrixExponent.slots x ⊕ MatrixExponent.slots y),
    let v := (h.summand sc c).frame.place (Packing.portEnd (h.summand sc c).diagram i)
    (h.scalarParent sc c v.1, v.2) = P.place (Packing.portEnd P.diagram i)
  table : ∀ (c : h.Paths sc) v,
    (h.summand sc c).diagram.table v = dictionary S hK hF mobility U sc (h.ticket sc c v)
  labels : Function.Injective (encode S U) ∧ Fintype.card (Pins S U) ≤ B * (1 + a + Nat.clog 2 (T + 1))
  binary : h.Binary sc
  reader : h.Reader sc
  rounds : Copy.radius Cfg ≤ B
  work : controllerWork S U (wordWidth D T) ≤ B * (1 + a + Nat.clog 2 (T + 1))

theorem complete {J B a : ℕ} (hx : NoExtras A status) (hc : ControllerBounds S U T J)
    (hJ : J ≤ B) (hw : J * (1 + f) ≤ B * (1 + Nat.clog 2 (T + 1)))
    (hb : 2 * J * (1 + S.ℓ + f) ≤ B * (1 + a + Nat.clog 2 (T + 1))) : h.Bookkeeping sc B a := by
  have h₀ : 1 + S.ℓ + U.labelBits + U.tagWidth S g ℓ (Cfg).waves ≤ controllerWork S U (wordWidth D T) :=
    (Nat.le_add_right _ f).trans (Nat.le_add_left ..)
  have he : U.addressBits S + (1 + S.ℓ + U.labelBits + U.tagWidth S g ℓ (Cfg).waves) ≤ B * (1 + a + Nat.clog 2 (T + 1)) :=
    (Nat.add_le_add hc.address (h₀.trans hc.work)).trans (by rw [←two_mul, ←mul_assoc]; exact hb)
  refine ⟨h.exact_sum sc, h.bounded sc, h.core_degree sc, ?_, ?_, h.controls_injective sc, h.controls_range sc,
    h.scalar_count sc, h.scalar_common sc, fun c _ _ => h.scalar_mem sc c, h.scalar_ext sc,
    h.table sc, ⟨encode_injective S U, (pin_count S U).le.trans he⟩,
    h.binary sc hx, h.reader sc, hc.rounds.trans hJ, ?_⟩
  · exact (h.count sc).trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ (hc.count.trans hw)))
  · rw [h.control_size]
    exact hc.selectors.trans hw
  · exact hc.work.trans ((Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left J (by decide))).trans hb)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.ReadyPanel
end
