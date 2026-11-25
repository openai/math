import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Price
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Scales
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Work
import OAI.LinearAlgebra.MatrixExponent.Sphere.Price.Allowance

/-! # Publishing a term of the printed expansion -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Sphere Assembly Coloring Rounds
open scoped Classical

namespace Assembly.Template.Binning.Trial
variable {F : Type} [Field F] {x y : Wire} {D : Template F} {a H T R : ℕ} {θ L : ℝ}
  {b : D.Binning a H T R θ} {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h}
  {p : D.Presents r P}

theorem centered (t : b.Trial p L) : Payload.Centered t.order := by
  intro i
  let v := Packing.portEnd t.input.diagram i
  have he := t.flag v
  have hv : ¬t.input.mobile v := t.input.ext i
  simp only [mobile, decide_eq_decide] at he
  exact not_not.mp (mt he.mpr hv)

end Assembly.Template.Binning.Trial

namespace Sphere.Print.Printer
variable {F K N : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F}
  {d ℓ M r t q D k n u j z' : ℕ}

def family (U : Printer F K N S.m d S.h ℓ M r t q D k n u j z') :
    Payload.Family S U.template.scheme U.childBits := ⟨U.split, U.outer, rfl⟩

variable {s : Rounds.Plan} {T R g e z height : ℕ} {L : ℝ}
  (U : Printer F K N S.m d S.h ℓ M r t q s.D k s.d (s.b * z) j z')
  {P : Input F x y S.h s.D T R g (10000 * L)} {tape : S.format.obj}
  {pres : S.Presentation tape P.diagram} {dir : pres.Directed}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj} {f : Val x → Val y → F}

/-- The old selector tape stays with the new term until its exterior
payload has been transferred to the child hosts. -/
def publish (A : P.HostChart S tape) (radius : ℕ) (hC : Input.terminalExponent g 10 = s.C)
    (center : Payload.Centered (pres.toOrdered dir)) (old : B e → B S.ℓ)
    (metadata : (Fmt.rows S.m S.d S.h (.addr e)).obj)
    (read : ∀ v j, old ((metadata v).2 j) = (tape v).2 j)
    (fits : S.Fits tape (2 ^ S.m + wd x + wd y) height)
    (out : U.Release (P := A.normalized pres dir radius) (pres.toOrdered dir) data status f 10)
    (i : out.I) : Payload.Pending (x := x) (y := y) (U.family (S := S)) old s T L z height where
  out := {
    R := R, g := g, P := A.normalized pres dir radius, Q := out.term i
    ready := by rw [← hC]; exact out.bound i
    live := out.populated i
    r := U.advance data status (out.select.write i)
    showing := out.shows i
    fits := (out.retains i).fits fits }
  G := P.diagram
  data := tape
  initial := pres
  dir := dir
  tape := metadata
  read := read
  fits := fits
  center := center
  retains := out.retains i

end Sphere.Print.Printer
end OAI.LinearAlgebra.MatrixExponent
end

/-!
# Combining host, block and exterior costs

Fixed factors are absorbed by increasing the common exponent.
The base in the last term is independent of the label width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
open Assembly
open BatchDescent.Phase.Poly (pow_sum)
variable {F : Type} [Field F] (S : Scheme F) (q : Contraction.Prices F) (h f N : ℕ)

local notation "P" => portBase S q h
local notation "R" => rowBase S q h f
local notation "H" => hostBase S q h f
local notation "C" => fullCost S q h f N

theorem layers : 1000 + h + q.W ≤ P ∧ P + S.ℓ + f ≤ R ∧ R + S.m + q.w ^ q.power ≤ H := by
  unfold hostBase rowBase portBase
  have := Nat.zero_le (2 ^ S.e)
  omega

theorem cost_mono {i j : ℕ} (he : i ≤ j) : C i ≤ C j := by
  have hb := layers S q h f
  have ht := Nat.zero_le (q.w ^ q.power)
  unfold fullCost
  gcongr <;> omega

theorem cost_add (i j : ℕ) : C i + C j ≤ C (max i j + 1) := by
  have hb := layers S q h f
  have ht := Nat.zero_le (q.w ^ q.power)
  have aux (x y : ℕ) (hy : 2 ≤ y) := Nat.mul_le_mul_left x (pow_sum hy i j)
  have a := aux (2 ^ S.m) H (by omega)
  have b := aux (2 ^ (S.m + S.h)) R (by omega)
  have c := aux N P (by omega)
  simp only [mul_add] at a b c
  unfold fullCost
  omega

def shortRate (J : ℕ) := J * R
def longRate (J : ℕ) := (20 * (J + 1)) * H

theorem rates_fit (J : ℕ) :
    1000 + 10 * S.m + 10 * shortRate S q h f J ≤ longRate S q h f J ∧
      1 + q.w ^ q.power ≤ longRate S q h f J := by
  have hb := layers S q h f
  have ht := Nat.zero_le (q.w ^ q.power)
  have hi := Nat.mul_le_mul_left J (show R ≤ H by omega)
  unfold shortRate longRate
  rw [mul_assoc 20, add_mul, one_mul]
  omega

private theorem inflate {n : ℕ} (h : 2 ≤ n) (c i : ℕ) : (c * n) ^ i ≤ n ^ ((c + 1) * i) := by
  rw [pow_mul n, pow_succ n c]
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_right n
    (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left h c))) _

def exponent (J i : ℕ) := max ((20 * (J + 1) + 1) * i) (J * (J + 2) + 1) + 1

theorem price_into_cost (J i : ℕ) (v : ℕ)
    (hv : v ≤ 2 ^ S.m * J + (h + 1) * (2 * (2 ^ S.m + N))) :
    2 ^ S.m * (longRate S q h f J) ^ i + 2 ^ (S.m + S.h) * (shortRate S q h f J) ^ i + J * v ≤
      C (exponent J i) := by
  have hb := layers S q h f
  have ht := Nat.zero_le (q.w ^ q.power)
  let k := (20 * (J + 1) + 1) * i
  let j := J * (J + 2) + 1
  have hw : 2 ^ S.m * (longRate S q h f J) ^ i + 2 ^ (S.m + S.h) * (shortRate S q h f J) ^ i ≤ C k := by
    refine (Nat.add_le_add (Nat.mul_le_mul_left _ (inflate (by omega : 2 ≤ H) _ i))
      (Nat.mul_le_mul_left _ ((inflate (by omega : 2 ≤ R) J i).trans ?_))).trans (Nat.le_add_right ..)
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.mul_le_mul_right i (by omega)
  have hc (n : ℕ) (hn : P ≤ n) : J * (J + 2 * (h + 1)) ≤ n ^ j := by
    have hy : h + 1 ≤ n := by omega
    have he : J + 2 * (h + 1) ≤ (J + 2) * n := by
      rw [add_mul]
      exact Nat.add_le_add (Nat.le_mul_of_pos_right _ (by omega)) (Nat.mul_le_mul_left _ hy)
    have hj : J * (J + 2) * n ≤ n ^ (J * (J + 2) + 1) := by
      simpa only [pow_one, mul_one] using inflate (by omega : 2 ≤ n) (J * (J + 2)) 1
    rw [mul_assoc] at hj
    exact (Nat.mul_le_mul_left J he).trans hj
  have he : J * v ≤ C j := calc
    _ ≤ J * (2 ^ S.m * J + (h + 1) * (2 * (2 ^ S.m + N))) := Nat.mul_le_mul_left _ hv
    _ = 2 ^ S.m * (J * (J + 2 * (h + 1))) + N * (J * (2 * (h + 1))) := by ring
    _ ≤ 2 ^ S.m * H ^ j + N * P ^ j := Nat.add_le_add (Nat.mul_le_mul_left _ (hc H (by omega)))
      (Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (Nat.le_add_left ..)).trans (hc P le_rfl)))
    _ ≤ _ := Nat.add_le_add_right (Nat.le_add_right ..) _
  exact (Nat.add_le_add hw he).trans (cost_add S q h f N k j)

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-! # Applying a family of controlled emissions to a moved layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Sphere SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d : ℕ} {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)

local notation "deg" => ((4 * 5) ^ 300 : ℕ)

section

-- Work at an arbitrary tape width to avoid expanding the recursive bound
-- on all the preceding waves when comparing input and output formats.
private abbrev Flexible (p l k r t z f : ℕ) :=
  let cfg := Input.design B.target deg 10 s.D b d p l
  Print.Printer F (Input.panelKeys cfg) (Coloring.B B.target.k) B.target.m B.target.d B.target.h
    k (chunks 10 s.D) r t cfg.R s.D
    (Sphere.Layout.Sharing.allocation deg 10) s.d (s.b * z) (p ^ l) f

variable {p l k r t z f : ℕ}
    (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales deg 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D deg (p ^ l) b d)
    (U : P.Flexible B p l k r t z f)

variable (menu : (Input.design B.target ((4 * 5) ^ 300) 10 s.D b d p l).Menu F (Coloring.B B.target.k) (Coloring.B B.target.ℓ) k)
private abbrev finished := Sphere.Surface.Local.snapshot (P.panelWorld B trials sc hK) (P.panelPort B)
  (P.panelPayload B trials) (Input.design B.target deg 10 s.D b d p l).waves menu

private abbrev Emissions := ∀ i : (P.finished B trials sc hK menu).state,
  U.Release (P := (trials i.1.1).normal (panelRadius s.D)) (trials i.1.1).order
    i.2.tape (B.status (P.data i.1.1)) ((P.finished B trials sc hK menu).eval i) 10

variable
    (releases : P.Emissions B trials sc hK U menu)
    (hC : Input.terminalExponent deg 10 = s.C)

local notation "srcPort" => P.finished B trials sc hK menu
local notation "old" => fun i => Prod.fst (menu i)
local notation "dstPort" => Payload.pending (x := x) (y := y) (U.family (S := B.target)) (old) s T L z P.height
local notation "bitsPort" => Fmt.payload B.target.m (P.groupedVolume B) P.height

private def chosen : Selected (srcPort) (dstPort) U.selectors where
  choice i := (releases i).I
  finite i := (releases i).finite
  index i := (releases i).select
  next i j := U.publish (s := s) (S := B.target) (trials i.1.1).chart (panelRadius s.D)
    hC (trials i.1.1).centered (old) i.2.tape
    (fun v w => congrArg Prod.fst (i.2.read (v, w))) ((trials i.1.1).fits (P.fits i.1.1))
    (releases i) j
  scalar i := (releases i).coeff
  expands i v w := ((releases i).value v w).symm

include releases hC in
private theorem printFin (q : Contraction.Prices F) {u : ℕ} {labels : Set (Table F)}
    (hu : 3 ≤ u) (hw : 2 * U.window.width ≤ u) (hm : B.target.m + (B.target.d + 1) * 1 ≤ q.w)
    (hk : U.gate ∈ labels) :
    Transforms F u labels (srcPort) (dstPort) (U.price q bitsPort) := by
  let sel := P.chosen B trials sc hK U menu releases hC
  refine U.transfer q (Z := bitsPort) (I := (srcPort).state) (J := (dstPort).state)
    (f := (srcPort).eval) (g := (dstPort).eval) (X := (srcPort).encode) (Y := (dstPort).encode) sel hu hw hm hk ?_ ?_ ?_
  · intro i a b
    exact (releases i).reciprocal
  · intro i a b
    exact (releases i).valid
  · intro i a b j
    rfl

end

variable [Fintype F] {p l k r t z f : ℕ} [ExpChar F p]
    (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales deg 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D deg (p ^ l) b d)
    (hF : room 10 s.D deg *(2 * depth 10 s.D deg (p ^ l) (d * b) + 1) < Fintype.card F)
    (U : P.Printer B p l k r t z f)
    (releases : P.Releases B trials sc hK hF U)
    (hC : Input.terminalExponent deg 10 = s.C)

local notation "srcPort" => P.moved B trials sc hK hF k
local notation "old" => fun i => Prod.fst (P.movedMenu B hK hF k i)
local notation "dstPort" => Payload.pending (x := x) (y := y) (U.family (S := B.target)) (old) s T L z P.height
local notation "bitsPort" => Fmt.payload B.target.m (P.groupedVolume B) P.height

include releases hC in
theorem printReleases (q : Contraction.Prices F) {u : ℕ} {labels : Set (Table F)}
    (hu : 3 ≤ u) (hw : 2 * U.window.width ≤ u) (hm : B.target.m + (B.target.d + 1) * 1 ≤ q.w)
    (hk : U.gate ∈ labels) :
    Transforms F u labels (srcPort) (dstPort) (U.price q bitsPort) :=
  P.printFin B trials sc hK U (P.movedMenu B hK hF k) releases hC q hu hw hm hk

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Printing all the states of the completed movement schedule -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {g ℓ D T b d p l j : ℕ} {W : ℝ} {S : Scheme F}
    (P : Input F x y S.h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "world" => P.localWorld A sc hK s
local notation "Cfg" => design S g ℓ D b d p l

private def releaseCode (pres : S.Presentation z P.diagram) {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
    (h : P.Placed pres A.coord tone mobile) (hd : pres.Directed)
    {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j} (c : (world).Code (Cfg).waves menu)
    {M r t k n u e : ℕ}
    (U : Print.Printer F (panelKeys Cfg) (B S.k) S.m S.d S.h j M r t (Cfg).R D k n u (p ^ l) e)
    (ha : d * b = M * r) (hb : d = M * t) (hm : U.menu = printMenu S menu ha hb)
    (status : (Print.Children.Header S.m S.d).obj)
    (loc : ∀ v, A.coord v = (A.host v.val.1, cellIndex S.h v.val.2))
    (parents : Print.Children.Shows P.adj A.host (A.graph, status)) (hn : Nonempty P.V)
    (hM : M = chunks ℓ D) (hk : k = Sphere.Layout.Sharing.allocation g ℓ)
    (hu : u * D ^ (terminalExponent g ℓ) ≤ T)
    (hc : terminalExponent g ℓ * D * T ≤ u * U.cap) (hz : depth ℓ D g (p ^ l) (d * b) < 2 ^ e) :
    U.Release pres c.tape status ((world).eval c.frame) ℓ := by
  have sig := P.printSignal A sc hK s pres h hd c U ha hb hm status loc parents
  have bd := P.panelBounds A sc hK s c.frame
  exact sig.1.release sig.2 hn bd sc ha hb rfl rfl hM hk hu hc hz

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Sphere SphereScale
open scoped Classical

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d : ℕ} {θ L : ℝ} {p l k r t z f : ℕ} [ExpChar F p]
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)

local notation "g" => ((4 * 5) ^ 300 : ℕ)

variable (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales g 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D g (p ^ l) b d)
    (hF : room 10 s.D g *(2 * depth 10 s.D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (U : P.Printer B p l k r t z f)
    (ha : d * b = chunks 10 s.D * r) (hb : d = chunks 10 s.D * t)
    (hm : U.menu = Input.printMenu B.target (P.movedMenu B hK hF k) ha hb)
    (hC : Input.terminalExponent g 10 = s.C)
    (hLive : ∀ i, Nonempty (P.board i).V)
    (hUnits : (s.b * z) * s.D ^ s.C ≤ T)
    (hCap : s.C * s.D * T ≤ (s.b * z) * U.cap)
    (hDepth : depth 10 s.D g (p ^ l) (d * b) < 2 ^ f)

include ha hb hm hC hLive hUnits hCap hDepth

private def releases : P.Releases B trials sc hK hF U := by
  rintro ⟨⟨i, shape⟩, code⟩
  let rad := panelRadius s.D
  let tr := trials i
  let A := tr.atlas rad
  let input := tr.normal rad
  rw [← hC] at hUnits hCap
  exact input.releaseCode A sc hK shape tr.order (tr.placed rad) tr.directed_order code U ha hb hm
    (B.status (P.data i)) (fun _ => rfl) (tr.parents rad) (tr.nonempty rad (hLive i))
    rfl rfl hUnits hCap hDepth

/-- The printed diagrams carry their old exterior payload until its
transfer to the children. -/
theorem printLayer (q : Contraction.Prices F) {u : ℕ} {labels : Set (Table F)}
    (hu : 3 ≤ u) (hw : 2 * U.window.width ≤ u) (hm' : B.target.m + (B.target.d + 1) * 1 ≤ q.w)
    (hk : U.gate ∈ labels) :
    Transforms F u labels (P.moved B trials sc hK hF k)
      (Payload.pending (U.family (S := B.target)) (fun i => (P.movedMenu B hK hF k i).1) s T L z P.height)
      (U.price q (Fmt.payload B.target.m (P.groupedVolume B) P.height)) := by
  let out := P.releases B trials sc hK hF U ha hb hm hC hLive hUnits hCap hDepth
  exact P.printReleases B trials sc hK hF U out hC q hu hw hm' hk

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Movement and printing costs of a grouped concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Assembly Coloring SphereScale

def SphereScale.costExponent (J : ℕ) := max (exponent (J + 1) 218) (exponent (J + 1) 225) + 1

namespace Layer
variable {F : Type} [Field F] {x y : Wire} {s : Plan} {a T b d p l k r t z f J : ℕ} {θ : ℝ}
  (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)
  (q : Contraction.Prices F) (U : P.Printer B p l k r t z f)
local notation "S" => B.target
local notation "Cfg" => Input.design (S) ((4 * 5) ^ 300) 10 s.D b d p l
local notation "Z" => Fmt.payload B.target.m (P.groupedVolume B) P.height

theorem programCost_bound (hJ : 10001 + 4 * (Cfg).waves + 2 ^ (S).d ≤ J)
    (hC : (Cfg).inflation * (1 + (S).ℓ + k) ≤ J * (1 + (S).ℓ + f))
    (hU : 10000 + 1 + U.window.width + U.labelBits + 2 ^ ((S).d + 1) + 2 ^ U.childBits+
      2 ^ U.template.scheme.d + 2 ^ (1 + 2 ^ (S).d + 12 * (2 ^ (S).d) ^ 3 + 2 ^ U.childBits) ≤ J * (1 + (S).ℓ + f)) :
    (Cfg).work q (S).ℓ k (P.panelPort B) + U.price q Z ≤
      fullCost (S) q P.height f (wd x + wd y) (costExponent J) := by
  let n := J + 1
  let X := longRate (S) q P.height f n
  let Y := shortRate (S) q P.height f n
  obtain ⟨hx, hw⟩ := rates_fit (S) q P.height f n
  obtain ⟨hp, hr, _⟩ := layers (S) q P.height f
  have hy : 1 + q.W + J * (1 + (S).ℓ + f) ≤ Y := by
    have he := Nat.mul_le_mul_left J (show 1 + (S).ℓ + f ≤ rowBase (S) q P.height f by omega)
    unfold Y shortRate n
    rw [add_mul, one_mul]
    omega
  have hb : 8 + 4 * (Cfg).waves ≤ n ∧ 1 + 2 ^ (S).d ≤ n ∧ 100 ≤ n := by
    generalize 2 ^ (S).d = v at hJ ⊢
    unfold n
    omega
  let w := (P.height + 1) * (2 * (2 ^ (S).m + (wd x + wd y)))
  have hz : (Z).width ≤ w := by
    unfold w groupedVolume
    rw [← add_assoc (2 ^ (S).m)]
    exact Fmt.width_payload ..
  have hp' : (P.panelPort B).width ≤ 2 ^ (S).m * n + w := by
    rw [panelPort, Format.width_pair, Template.Binning.Flags, Format.width_vec,
      Format.width_pair, Format.width_vec, Format.width_bit, mul_one]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hb.2.1) hz
  have hmove := (Cfg).work_bound q (S).ℓ k (P.panelPort B) X Y hx
    ((Nat.le_add_right ..).trans hy) hw (hC.trans ((Nat.le_add_left ..).trans hy))
  have hprint := U.work_bound q Z X Y hx hw (by omega)
  have hh (i v c) (hv : v ≤ 2 ^ (S).m * n + w) (hc : c ≤ n) :
      2 ^ (S).m * X ^ i + 2 ^ ((S).m + (S).h) * Y ^ i + c * v ≤
        fullCost (S) q P.height f (wd x + wd y) (exponent n i) :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hc) _).trans
      (price_into_cost (S) q P.height f (wd x + wd y) n i v hv)
  exact (Nat.add_le_add (hmove.trans (hh 218 _ _ hp' hb.1))
    (hprint.trans (hh 225 _ _ (hz.trans (Nat.le_add_left ..)) hb.2.2))).trans
      (cost_add (S) q P.height f (wd x + wd y) _ _)

end Layer
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Executing a local concentration with one shared dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Sphere SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d : ℕ} {θ L : ℝ} {p l k r t z f : ℕ} [ExpChar F p]
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)

local notation "g" => ((4 * 5) ^ 300 : ℕ)
local notation "Cfg" => Input.design B.target g 10 s.D b d p l
variable (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales g 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D g (p ^ l) b d)
    (hF : room 10 s.D g *(2 * depth 10 s.D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (U : P.Printer B p l k r t z f) (q : Contraction.Prices F)
local notation "A" => U.family (S := B.target)

def sphereCalls := insert ((A).gate (P.height + 1) (fun i => (P.movedMenu B hK hF k i).1))
  (insert U.gate (P.motionCalls B sc hK hF k))

theorem card_sphereCalls : (P.sphereCalls B sc hK hF U).card ≤ (Cfg).waves + 3 :=
  (Finset.card_insert_le ..).trans (Nat.succ_le_succ
    ((Finset.card_insert_le ..).trans (Nat.succ_le_succ (P.card_motionCalls B sc hK hF k))))

def sphereCost := (Cfg).work q B.target.ℓ k (P.panelPort B) +
  U.price q (Fmt.payload B.target.m (P.groupedVolume B) P.height) +
    Payload.price A P.height q (P.motionWidth B p l k) (wd x + wd y)

theorem executeSphere (ha : d * b = chunks 10 s.D * r) (hb : d = chunks 10 s.D * t)
    (hm : U.menu = Input.printMenu B.target (P.movedMenu B hK hF k) ha hb)
    (hC : Input.terminalExponent g 10 = s.C)
    (hLive : ∀ i, Nonempty (P.board i).V)
    (hUnits : (s.b * z) * s.D ^ s.C ≤ T)
    (hCap : s.C * s.D * T ≤ (s.b * z) * U.cap)
    (hDepth : depth 10 s.D g (p ^ l) (d * b) < 2 ^ f)
    (hi : initialChoices 10 s.D b d ≤ 2 ^ k)
    (hk : Surface.Local.Frame.budget F (Cfg).chart (Cfg).g (Cfg).H (Cfg).M (Cfg).D (Cfg).U ≤ 2 ^ k)
    (w : ℕ) (hw : (Cfg).arity B.target.ℓ k ≤ w) (hw' : 2 * U.window.width ≤ w)
    (hw'' : (A).arity (P.height + 1) (P.motionWidth B p l k) ≤ w)
    (hp : B.target.m + (Cfg).hops ≤ q.w)
    (hp' : U.template.scheme.m + U.childBits + P.height + 2 ≤ q.w) :
    Transforms F w (↑(P.sphereCalls B sc hK hF U)) (P.masked B trials (panelRadius s.D))
      (Contraction.publication U.template s T L z P.height) (P.sphereCost B U q) := by
  let W : Set (Table F) := P.sphereCalls B sc hK hF U
  have hu : 3 ≤ w := (Nat.le_add_right ..).trans hw
  have hq : B.target.m + (B.target.d + 1) * 1 ≤ q.w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))) _).trans hp
  have pos : 1 ≤ B.target.m := by
    change 1 ≤ P.template.scheme.m + (P.template.scheme.h - a + 1)
    omega
  have h₀ := P.moveLayer B trials sc hK hF q (labels := W) hi hk hp hw
    (fun _ h => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have h₁ := P.printLayer B trials sc hK hF U ha hb hm hC hLive hUnits hCap hDepth q (labels := W)
    hu hw' hq (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  have h₂ := Payload.transfer (x := x) (y := y) A (fun i => (P.movedMenu B hK hF k i).1) s T L z P.height q
    (labels := W) hu hw'' (Finset.mem_insert_self ..) pos (Nat.le_add_right ..) hp'
  exact (h₀.comp h₁).comp h₂

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Common bounds for every reachable diagram in a layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Sphere SphereScale
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {s : Rounds.Plan} {a T b d : ℕ} {θ : ℝ}
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)
    {p l k r t z f : ℕ} (U : P.Printer B p l k r t z f)
local notation "S" => B.target
local notation "e" => P.motionWidth B p l k
local notation "Cfg" => Input.design B.target ((4 * 5) ^ 300 : ℕ) 10 s.D b d p l

structure Limits (J : ℕ) : Prop where
  common : 10001 + 4 * (Cfg).waves + 2 ^ (S).d ≤ J
  hops : (Cfg).hops ≤ J
  child : 2 * U.childBits + 2 ≤ J
  parent : 2 ^ (S).d ≤ J
  contacts : 2 ^ U.childBits ≤ J
  degree : 2 ^ U.template.scheme.d ≤ J
  span : 2 ^ U.template.scheme.e ≤ J
  labels : U.template.scheme.ℓ + U.template.count + e ≤ J * (1 + (S).ℓ + f)
  move : (Cfg).inflation * (1 + (S).ℓ + k) ≤ J * (1 + (S).ℓ + f)
  print : 10000 + 1 + U.window.width + U.labelBits + 2 ^ ((S).d + 1) + 2 ^ U.childBits+
    2 ^ U.template.scheme.d + 2 ^ (1 + 2 ^ (S).d + 12 * (2 ^ (S).d) ^ 3 + 2 ^ U.childBits) ≤ J * (1 + (S).ℓ + f)
  ship : (U.family («S» := S)).arity (P.height + 1) e ≤ fullArity S P.height f J

private theorem budgeted (cfg : Sphere.Surface.Local.Design) (label sel start finish : ℕ)
    (begin : start = cfg.entryWidth label sel)
    (fits : cfg.inflation * (1 + label + sel) ≤ finish) :
    cfg.widthAt start sel cfg.waves ≤ finish := by
  rw [begin]
  exact (cfg.last_fits label sel).trans ((cfg.arity_bound label sel).trans fits)

set_option exponentiation.threshold 300 in
theorem limits {A J : ℕ} (hd : P.template.scheme.d ≤ 4) (hJ : upper s A ≤ J)
    (hc : U.cap = cap s) (hk : k ≤ slope A s.D (Cfg).M * (1 + f)) : P.Limits B U J := by
  let R := reserve s A Cfg
  have h := R.fits ((reserve_le S s A b d p l (B.nav_bound hd)).trans hJ)
  let X := 1 + (S).ℓ + f
  have hX : 0 < X := by unfold X; omega
  have hm : (Cfg).inflation * (1 + (S).ℓ + k) ≤ R.motion * X := R.motion_bound hk
  have hw : e ≤ R.motion * X :=
    budgeted Cfg (S).ℓ k (Input.panelQuery S ((4 * 5) ^ 300 : ℕ) 10 s.D b d p l k).width (R.motion * X)
      (panelWidth_eq S _ _ _ _ _ _ _ _) hm
  have hw' : U.window.width ≤ R.window * X := by
    rw [U.window_width, mul_one]
    have he : U.digits = f * R.digits := mul_assoc ..
    rw [he]
    exact R.window_bound hw (by unfold X; omega)
  obtain ⟨hlabel, hprice⟩ := h.priced hX hw hw'
  have hspan : U.template.scheme.e = R.span := by
    change Print.indexBits (Print.Band U.lane U.cap) = _
    rw [hc]
    rfl
  refine ⟨h.common, h.hops, h.child, h.parent, h.contacts, h.degree, hspan.symm ▸ h.span,
    ?_, hm.trans (Nat.mul_le_mul_right X h.motion), ?_, ?_⟩
  · change U.labelBits + U.labelBits + e ≤ J * X
    rw [←two_mul, add_comm]
    exact hlabel
  · have rearrange (v w x y g h i : ℕ) :
        10000 + 1 + v + w + x + y + g + h ≤ i ↔ 10001 + x + y + g + h + v + w ≤ i := by omega
    rw [rearrange]
    exact hprice
  · rw [Payload.Family.width]
    have hs := h.transferred (h := (S).h) («e» := (S).e) (w := P.height) hX hw hw'
    unfold Payload.Family.depth
    rw [hspan, fullArity, show 1 + (S).ℓ + (S).e + (S).h + P.height + f = X + (S).h + (S).e + P.height by unfold X; omega]
    exact hs

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Total cost of running the three parts of the controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Sphere SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d : ℕ} {θ L : ℝ} {p l k r t z f : ℕ} [ExpChar F p]
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)

local notation "g" => ((4 * 5) ^ 300 : ℕ)
local notation "Cfg" => Input.design B.target g 10 s.D b d p l
variable (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales g 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D g (p ^ l) b d)
    (hF : room 10 s.D g *(2 * depth 10 s.D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (U : P.Printer B p l k r t z f) (q : Contraction.Prices F)
local notation "A" => U.family (S := B.target)
local notation "v" => fullCost B.target q P.height f (wd x + wd y)

theorem executePriced (ha : d * b = chunks 10 s.D * r) (hb : d = chunks 10 s.D * t)
    (hm : U.menu = Input.printMenu B.target (P.movedMenu B hK hF k) ha hb)
    (hC : Input.terminalExponent g 10 = s.C)
    (hLive : ∀ i, Nonempty (P.board i).V)
    (hUnits : (s.b * z) * s.D ^ s.C ≤ T)
    (hCap : s.C * s.D * T ≤ (s.b * z) * U.cap)
    (hDepth : depth 10 s.D g (p ^ l) (d * b) < 2 ^ f)
    (hi : initialChoices 10 s.D b d ≤ 2 ^ k)
    (hk : Surface.Local.Frame.budget F (Cfg).chart (Cfg).g (Cfg).H (Cfg).M (Cfg).D (Cfg).U ≤ 2 ^ k)
    {J J' E : ℕ} (h : P.Limits B U J)
    (hp : Payload.price A P.height q (P.motionWidth B p l k) (wd x + wd y) ≤ v E)
    (hsize : max (costExponent J) E + 1 ≤ J') (hJ : J ≤ J') (hw : B.target.m + P.height + J' ≤ q.w) :
    Transforms F (fullArity B.target P.height f J') (↑(P.sphereCalls B sc hK hF U))
      (P.masked B trials (panelRadius s.D)) (Contraction.publication U.template s T L z P.height) (v J') := by
  let w := fullArity B.target P.height f J'
  have ht : J * (1 + B.target.ℓ + f) ≤ w := Nat.mul_le_mul hJ (by omega)
  have h₀ := ((Cfg).arity_bound B.target.ℓ k).trans (h.move.trans ht)
  have h₁ : 2 * U.window.width ≤ w := by
    have he := h.labels.trans ht
    change U.window.width + U.childBits + (U.window.width + U.childBits) + P.motionWidth B p l k ≤ w at he
    omega
  have h₂ := h.ship.trans (show fullArity B.target P.height f J ≤ w from Nat.mul_le_mul_right _ hJ)
  have hg : B.target.m + (Cfg).hops ≤ q.w :=
    (Nat.add_le_add (Nat.le_add_right ..) (h.hops.trans hJ)).trans hw
  have hf : U.template.scheme.m + U.childBits + P.height + 2 ≤ q.w := by
    have := h.child
    change B.target.m + U.childBits + U.childBits + P.height + 2 ≤ q.w
    omega
  have exec := P.executeSphere B trials sc hK hF U q ha hb hm hC hLive hUnits hCap hDepth hi hk w h₀ h₁ h₂ hg hf
  have hc := P.programCost_bound B q U h.common h.move h.print
  exact exec.mono ((Nat.add_le_add hc hp).trans ((cost_add ..).trans (cost_mono _ _ _ _ _ hsize)))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Building the common template before selecting a branch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Sphere SphereScale
variable {F K : Type} [Field F] [Field K] [Fintype F] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d p l k r t z f : ℕ} [ExpChar F p] {θ : ℝ}
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)
    (sc : Scales ((4 * 5) ^ 300) 10 s.D T (p ^ l) b d)
    (hK : SphereScale.Ready K 10 s.D ((4 * 5) ^ 300) (p ^ l) b d)
    (hF : room 10 s.D ((4 * 5) ^ 300) *(2 * depth 10 s.D ((4 * 5) ^ 300) (p ^ l) (d * b) + 1) < Fintype.card F)

include sc in
theorem setupPrinter (ha : d * b = chunks 10 s.D * r) (hb : d = chunks 10 s.D * t)
    (hd : P.template.scheme.d ≤ 4) (hz : 0 < s.b * z) :
    ∃ U : P.Printer B p l k r t z f, U.cap = cap s ∧
      U.menu = Input.printMenu B.target (P.movedMenu B hK hF k) ha hb := by
  have hlarge : 4 ≤ s.D := (by decide : 4 ≤ 10000000).trans sc.bound
  have aux (g S : ℕ) : 10 ≤ Layout.Sharing.allocation g S := by as_aux_lemma => exact Nat.le_add_left ..
  have he : 10 ≤ allot := aux _ _
  have hn : 2 ^ ((B.target.d + 1) * 1) ≤ s.D ^ allot + 1 := by
    rw [mul_one]
    exact ((B.nav_bound hd).trans (Nat.pow_le_pow_right sc.Dpos he)).trans (Nat.le_succ _)
  exact ⟨⟨Input.printMenu B.target (P.movedMenu B hK hF k) ha hb, rfl, hlarge, sc.chunks_le, hn, cap s, hz⟩, rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-!
# Uniform controlled concentration

One template and one finite dictionary suffice simultaneously for
all branches of the grouped layer. Their growth bounds are independent
of the number of hosts or blocks. The only use of the field size
in the address width is through its binary logarithm.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
open Assembly Sphere
open scoped Classical
local notation "g" => ((4 * 5) ^ 300 : ℕ)

private theorem depth_le (ℓ D n t : ℕ) : t ≤ room ℓ D n * (2 * t + 1) := by
  have hr : 0 < room ℓ D n := by unfold room slots; positivity
  exact (show t ≤ 2 * t + 1 by omega).trans (Nat.le_mul_of_pos_left _ hr)

private theorem card_capacity (n d : ℕ) : n + 3 ≤ 10001 + 4 * n + d := by omega

theorem controlled (K : Type) [Field K] (s : Plan)
    (hC : s.C = Input.terminalExponent g 10) (p l b : ℕ) :
    ∃ A J, Controlled K s p l b A J := by
  obtain ⟨A, hA⟩ := selector_bound g 10 s.D (p ^ l) b
  let M := upper s A
  obtain ⟨E, hE⟩ := Payload.price_bound M
  let J := max M (max (costExponent M) E + 1)
  have hJ : M ≤ J := le_max_left ..
  refine ⟨A, J, ?_⟩
  intro F _ _ _ _ T d f z sc hK hF₀ hT hF₁ hz hUnits hT' x y P a θ L B trials q hLive hd hw
  obtain ⟨hr, hi, hk, _⟩ := hA sc F
  let k := selectorBits A s.D (room 10 s.D g) T (Nat.card F)
  have hF := hr.trans_le hF₀
  have hDepth : depth 10 s.D g (p ^ l) (d * b) < 2 ^ f :=
    (depth_le _ _ _ _).trans_lt (hF.trans_le hF₁)
  have slopeBound : k ≤ slope A s.D (room 10 s.D g) * (1 + f) :=
    selector_width _ _ _ _ _ _ hT (Nat.card_eq_fintype_card.trans_le hF₁)
  obtain ⟨t, hb⟩ := sc.divides
  have ha : d * b = chunks 10 s.D * (t * b) := by rw [hb, mul_assoc]
  obtain ⟨U, hcap, hm⟩ := P.setupPrinter B sc hK hF (k := k) (f := f) ha hb hd hz
  have hc : s.C * s.D * T ≤ (s.b * z) * U.cap := by
    rw [hcap, cap, mul_left_comm (s.b * z)]
    exact Nat.mul_le_mul_left _ hT'
  have bounds := P.limits B U hd (le_refl M) hcap slopeBound
  let names := P.sphereCalls B sc hK hF U
  have priced := hE F B.target U.template U.childBits (P.motionWidth B p l k) f P.height (wd x + wd y)
    (U.family (S := B.target)) q bounds.parent bounds.degree bounds.contacts bounds.span bounds.labels
  have exec := P.executePriced B trials sc hK hF U q ha hb hm hC.symm hLive hUnits hc hDepth
    hi hk bounds priced (le_max_right ..) hJ hw
  refine ⟨U.template, names, rfl, Nat.le_add_right B.target.m U.childBits, ?_, rfl, ?_, bounds.span.trans hJ, ?_, ?_, exec⟩
  · exact Nat.add_le_add_left ((Nat.lt_two_pow_self.le.trans bounds.contacts).trans hJ) _
  · exact (Nat.lt_two_pow_self.le.trans bounds.degree).trans hJ
  · rw [add_comm B.target.ℓ 1]
    exact ((Nat.le_add_right ..).trans bounds.labels).trans (Nat.mul_le_mul_right _ hJ)
  · have ht := card_capacity (Input.design B.target g 10 s.D b d p l).waves (2 ^ B.target.d)
    exact ((P.card_sphereCalls B sc hK hF U).trans (ht.trans bounds.common)).trans hJ

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end
