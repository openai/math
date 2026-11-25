import OAI.Hierarchy.TraceDistributionScale
import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.RAM.ContractionGuess
import OAI.ThreeFlat.RAM.ContractionReturns

namespace OAI
/-! # Work of one selected history of compiled trace factors

The same ordered trees determine the scalar factors, their native replay costs and the
work tariffs. Each site charges its kernel, guessed bits and emitted pin maps. The
unique owner of every old tree prevents duplication in the total over terminal sites.
-/

noncomputable section
namespace Hierarchy.TraceDistribution.FactorWork

open ThreeFlat Diagonal.HistoryContraction
open scoped Classical BigOperators

variable {F Pins : Type*} [CommSemiring F] {S : Shape}

section Stage
variable {R : Rewrite S F} {t : Fin R.count} {V : Form S Pins} {W : Form (R.target t) Pins}
variable (a : Stage R t V W)

/-- Newly created kernel and address-map entries on this selected substep. -/
def added (v : (R.target t).Site) : ℕ :=
  a.freshResources v + ∑ i, V.width (a.child v i).val

theorem assemble_site (N : Forest F V) (v : (R.target t).Site) :
    (a.assemble N v).resources = added a v + ∑ i, (N (a.child v i).val).resources := by
  rw [Stage.resources_assemble, Finset.sum_add_distrib, added]
  omega

theorem assemble_total (N : Forest F V) :
    (∑ v, (a.assemble N v).resources) =
      (∑ v, a.freshResources v) + (∑ v, V.width v) + ∑ i, (N i).resources := by
  simp only [assemble_site, added, Finset.sum_add_distrib]
  rw [a.sum_children V.width, a.sum_children (fun i => (N i).resources)]

theorem assemble_peak (N : Forest F V) {B D M : ℕ} (fee : ∀ v, added a v ≤ B)
    (children : ∀ v, a.count v ≤ D) (old : ∀ i, (N i).resources ≤ M) (v : (R.target t).Site) :
    (a.assemble N v).resources ≤ B + D*M := by
  rw [assemble_site]
  apply Nat.add_le_add (fee _)
  calc
    (∑ i, (N (a.child v i).val).resources) ≤ ∑ _ : Fin (a.count v), M :=
      Finset.sum_le_sum fun i _ => old _
    _ = a.count v*M := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (children _)

end Stage

/-- Exact total increase in resources on a branch, stated entirely in terms
of intermediate forms and newly issued kernel descriptors. -/
def newResources : {S : Shape} → (P : Plan F S) → (h : P.History) → {V : Form S Pins} →
    P.Assembly V → ℕ
  | _, .done _, _, _, _ => 0
  | _, .step _ next, h, V, A =>
    (∑ v, (A h.1).2.1.freshResources v) + (∑ v, V.width v) +
      newResources (next h.1) h.2 (A h.1).2.2

def stages : {S : Shape} → (P : Plan F S) → P.History → ℕ
  | _, .done _, _ => 0
  | _, .step _ next, h => stages (next h.1) h.2 + 1

/-- Width and multiplicity bounds need only hold on the chosen branch. -/
def bounded (B D : ℕ) : {S : Shape} → (P : Plan F S) → (h : P.History) →
    {V : Form S Pins} → P.Assembly V → Prop
  | _, .done _, _, _, _ => True
  | _, .step _ next, h, _, A =>
    (∀ v, added (A h.1).2.1 v ≤ B) ∧ (∀ v, (A h.1).2.1.count v ≤ D) ∧
      bounded B D (next h.1) h.2 (A h.1).2.2

variable (P : Plan F S) (h : P.History) {V : Form S Pins} (A : P.Assembly V) (N : Forest F V)

/-- The integer charge for a terminal factor contains no external input or boundary bits. -/
def work (depth setup maps : ℕ) (v : (P.finish h).Site) : ℕ :=
  (10025+1016*depth+setup+maps)*((P.assemble h A N).2 v).resources

theorem resources_total :
    (∑ v, ((P.assemble h A N).2 v).resources) =
      newResources P h A + ∑ i, (N i).resources := by
  induction P with
  | done => exact (Nat.zero_add _).symm
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    change (∑ v, (((next t).assemble h (A t).2.2 ((A t).2.1.assemble N)).2 v).resources) = _
    rw [ih,assemble_total]
    dsimp only [newResources]
    omega

theorem resources_peak {B D M : ℕ} (fit : bounded B D P h A) (floor : B ≤ M)
    (seed : ∀ i, (N i).resources ≤ M) (v : (P.finish h).Site) :
    ((P.assemble h A N).2 v).resources ≤ (D+1)^(stages P h)*M := by
  induction P generalizing M with
  | done => simpa [Plan.assemble,stages] using seed v
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    have up : M ≤ (D+1)*M := Nat.le_mul_of_pos_left _ (by omega)
    have nextBound (x) : ((A t).2.1.assemble N x).resources ≤ (D+1)*M := by
      have q := assemble_peak (A t).2.1 N fit.1 fit.2.1 seed x
      rw [Nat.add_mul, Nat.one_mul]
      omega
    change (((next t).assemble h (A t).2.2 ((A t).2.1.assemble N)).2 v).resources ≤ _
    have q := ih t (M := (D+1)*M) h (A t).2.2 ((A t).2.1.assemble N) fit.2.2 (floor.trans up) nextBound v
    simpa only [stages,pow_succ,Nat.mul_assoc] using q

theorem work_total (depth setup maps : ℕ) :
    (∑ v, work P h A N depth setup maps v) =
      (10025+1016*depth+setup+maps)*(newResources P h A + ∑ i, (N i).resources) := by
  rw [← resources_total P h A N, Finset.mul_sum]; rfl

theorem work_peak (depth setup maps : ℕ) {B D M : ℕ} (fit : bounded B D P h A) (floor : B ≤ M)
    (seed : ∀ i, (N i).resources ≤ M) (v : (P.finish h).Site) :
    work P h A N depth setup maps v ≤
      (10025+1016*depth+setup+maps)*((D+1)^(stages P h)*M) :=
  Nat.mul_le_mul_left _ (resources_peak P h A N fit floor seed v)

/-- Convert the terminal-tree resource estimate of the archive scan into the
work allowance stored at that terminal site's two-word charge row. -/
theorem work_le_archive (depth setup maps n K credit unitWork : ℕ) (v : (P.finish h).Site)
    (resources : ((P.assemble h A N).2 v).resources ≤ (2*n+1)*K*credit)
    (tariff : (10025+1016*depth+setup+maps)*((2*n+1)*K) ≤ unitWork) :
    work P h A N depth setup maps v ≤ unitWork*credit := by
  calc
    _ ≤ (10025+1016*depth+setup+maps)*(((2*n+1)*K)*credit) := Nat.mul_le_mul_left _ resources
    _ = ((10025+1016*depth+setup+maps)*((2*n+1)*K))*credit := (Nat.mul_assoc ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ tariff

/-- A unit of archived work covers the selected stage forest, including
the cubic address-height price of the fixed physical shrink and refresh kernels. -/
def archiveTariff (w depth setup maps stages localCoefficient : ℕ) : ℕ :=
  (10025+1016*depth+setup+maps)*((2*stages+1)*(localCoefficient*(16*w^10+1)^3))

/-- The exponent of the whole elected work tariff is independent of the
compressor's finite tile constants and the number of repetitions. -/
theorem archiveTariff_le (w depth setup maps stages c a b : ℕ)
    (h : depth≤a*(w+1)^b) (s : setup≤a*(w+1)^b)
    (m : maps≤a*(w+1)^b) (n : stages≤a*(w+1)^b) :
    archiveTariff w depth setup maps stages c ≤
      ((10025+1018*a)*(2*a+1)*c*17^3)*(w+1)^(b+b+30) := by
  let x := (w+1)^b
  have one : 1≤x := Nat.pow_pos (Nat.succ_pos _)
  have price : 10025+1016*depth+setup+maps ≤ (10025+1018*a)*x := by
    change depth≤a*x at h
    change setup≤a*x at s
    change maps≤a*x at m
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  have count : 2*stages+1 ≤ (2*a+1)*x := by
    change stages≤a*x at n
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    omega
  have height : 16*w^10+1 ≤ 17*(w+1)^10 := by
    have hm : w^10≤(w+1)^10 := Nat.pow_le_pow_left (Nat.le_succ w) 10
    have ho : 1≤(w+1)^10 := Nat.pow_pos (Nat.succ_pos _)
    omega
  calc
    _ ≤ ((10025+1018*a)*x)*(((2*a+1)*x)*(c*((17*(w+1)^10)^3))) :=
      Nat.mul_le_mul price (Nat.mul_le_mul count (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left height _)))
    _ = _ := by
      let t:=w+1
      change ((10025+1018*a)*t^b)*(((2*a+1)*t^b)*(c*(17*t^10)^3)) =
        ((10025+1018*a)*(2*a+1)*c*17^3)*t^(b+b+30)
      rw [pow_add t (b+b) 30, pow_add t b b, mul_pow 17 (t^10) 3, ←pow_mul t 10 3]
      change ((10025+1018*a)*t^b)*(((2*a+1)*t^b)*(c*(17^3*t^30))) =
        ((10025+1018*a)*(2*a+1)*c*17^3)*(t^b*t^b*t^30)
      generalize t^b = p
      generalize t^30 = q
      ring

/-- Covers the selected tree's postorder replay, field scan and pin-map generation. -/
theorem work_covers (depth setup maps : ℕ) (v : (P.finish h).Site)
    (height : Tree.Within depth ((P.assemble h A N).2 v)) :
    let T := (P.assemble h A N).2 v
    T.replayWork setup + 10000*(T.rows+T.bits) + maps*T.footprint.pins ≤
      work P h A N depth setup maps v :=
  (Nat.add_le_add_right (Tree.scheduledWork_covers height setup) _).trans (Tree.native_cost ..)

private theorem scanCost {G : Type*} {p : ℕ} (T : Tree G p) :
    9+5*T.compile.internal+22*T.compile.cells ≤ 22*T.resources := by
  have nodes := T.nodes_pos
  rw [Tree.compiled_bits,Tree.compiled_rows]
  unfold Tree.resources Stage.treeWork
  omega

/-- The tariff covers both the preparation of the compiled network and the
actual field evaluator's instruction count on the same factor. -/
theorem replay_and_scan (depth setup maps : ℕ) (v : (P.finish h).Site)
    (height : Tree.Within depth ((P.assemble h A N).2 v)) :
    let T := (P.assemble h A N).2 v
    T.replayWork setup + (9+5*T.compile.internal+22*T.compile.cells) + maps*T.footprint.pins ≤
      work P h A N depth setup maps v := by
  intro T
  have volume : T.nodes+T.rows+T.bits ≤ T.resources := by
    unfold Tree.resources Stage.treeWork
    omega
  have pins : T.footprint.pins ≤ T.resources := Nat.le_add_left _ _
  have replay := (Tree.replay_le height setup).trans (Nat.mul_le_mul_left _ volume)
  calc
    _ ≤ (25+1016*depth+setup)*T.resources + 22*T.resources + maps*T.resources :=
      Nat.add_le_add (Nat.add_le_add replay (scanCost T)) (Nat.mul_le_mul_left _ pins)
    _ ≤ _ := by
      rw [←Nat.add_mul,←Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by omega : 25+1016*depth+setup+22+maps≤10025+1016*depth+setup+maps)

section Native
open RAM.Contraction
variable {G X : Type*} [Fintype G] [Field G] {H : Shape} {w : ℕ}
variable (Q : Plan G H) (g : Q.History) {U : Form H X} (A₀ : Q.Assembly U) (N₀ : Forest G U)

/-- The fixed 35-instruction evaluator for each compiled factor returns on every
path. Its path sum is the selected cell of the original contraction. The initial
memory here contains the compiled topology, local pins and fixed field table. -/
theorem native_factor (v : (Q.finish g).Site) (input : X) (z : (Q.finish g).Half v)
    (fit : Fits ((Q.assemble g A₀ N₀).2 v).compile w) (depth setup maps : ℕ) :
    let T := (Q.assemble g A₀ N₀).2 v
    let code := codec T.compile fit
    let mach := machine (parameters T.compile fit)
    let mem := RAM.BitLayout.memoryWithTail (fun _ => 0) T.compile code
      ((Q.assemble g A₀ N₀).1.read v input z) (fun _ => false)
    ∃ fuel ≤ work Q g A₀ N₀ depth setup maps v,
      RAM.value code mach fuel 0 mem = Q.cells g (U.values N₀ input) v z ∧
      RAM.Subroutine.returnsBy mach.program (fun f _ _ out => f=0 ∧ out.isSome)
        fuel (mach.program.start 0) mem := by
  intro T code mach mem
  let fuel := 9+5*T.compile.internal+22*T.compile.cells
  refine ⟨fuel,?_,?_,?_⟩
  · exact (scanCost T).trans (Nat.mul_le_mul_right _ (by omega : 22≤10025+1016*depth+setup+maps))
  · have value := value_eq_network T.compile fit ((Q.assemble g A₀ N₀).1.read v input z)
      (fun _ => false) 0
    have run : RAM.value code mach fuel 0 mem =
        T.compile.eval ((Q.assemble g A₀ N₀).1.read v input z) := by
      simpa only [Nat.zero_add] using value
    exact run.trans (congrFun (congrFun (Q.assemble_values g U A₀ N₀ input) v) z)
  · simpa only [Nat.zero_add] using returnsBy_network T.compile fit 0 mem

/-- The dense network, field multiplication table and supplied local pins are
addressable on a 64w-bit RAM at the stated work and input caps. -/
theorem factor_fits (v : (Q.finish g).Site) (depth setup maps : ℕ) (hw : 1≤w)
    (field : Fintype.card G * Fintype.card G ≤ 2^w)
    (pins : (Q.assemble g A₀ N₀).1.width v ≤ 2^w)
    (cost : work Q g A₀ N₀ depth setup maps v ≤ 2^w) :
    Fits ((Q.assemble g A₀ N₀).2 v).compile (64*w) := by
  let T := (Q.assemble g A₀ N₀).2 v
  have scan := (scanCost T).trans ((Nat.mul_le_mul_right T.resources
    (by omega : 22≤10025+1016*depth+setup+maps)).trans cost)
  change 2+(Q.assemble g A₀ N₀).1.width v + T.compile.internal + 11*T.compile.cells +
    Fintype.card G*Fintype.card G ≤ _
  have two : 2≤2^w := Nat.pow_le_pow_right (by decide : 0<2) hw
  calc
    _ ≤ 4*2^w := by omega
    _ = 2^(w+2) := by rw [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
end Native

/-- The stage and leaf estimates are uniform in the selector. The total exponent
does not involve the fixed multiplicities or the number of compression blocks. -/
theorem paper_scale {u s : ℕ → ℕ} (scale : Scale u s) (a b c K D passes : ℕ) :
    ∀ᶠ w : ℕ in Filter.atTop,
      ∀ (Q : Plan F S) (h : Q.History) (V : Form S Pins) (A : Q.Assembly V)
        (N : Forest F V) (depth setup maps B M : ℕ),
      10025+1016*depth+setup+maps ≤ w^c →
      newResources Q h A + ∑ i, (N i).resources ≤ 2^(u w)*w^b →
      bounded B D Q h A → B ≤ M → (∀ i, (N i).resources ≤ M) →
      stages Q h ≤ passes*s w → M ≤ a*(w+1)^b*K^(s w)*2^(w/2) →
      (∑ v, work Q h A N depth setup maps v) ≤ 2^(u w)*w^(b+c) ∧
      ∀ v, work Q h A N depth setup maps v ≤ 2^(3*w/5) := by
  filter_upwards [factor_room scale a (b+c) ((D+1)^passes*K)] with w room
  intro Q h V A N depth setup maps B M price total geom floor seed count size
  constructor
  · rw [work_total]
    calc
      _ ≤ w^c*(2^(u w)*w^b) := Nat.mul_le_mul price total
      _ = _ := by rw [pow_add]; ac_rfl
  · intro v
    have d : (D+1)^(stages Q h) ≤ ((D+1)^passes)^(s w) := by
      rw [←pow_mul]
      exact Nat.pow_le_pow_right (by omega) count
    have rate := price.trans (Nat.pow_le_pow_left (Nat.le_succ w) c)
    have low : 2^(w/2) ≤ 2^(max (w/2) (u w-w/2)) :=
      Nat.pow_le_pow_right (by decide) (le_max_left ..)
    calc
      _ ≤ (10025+1016*depth+setup+maps)*((D+1)^(stages Q h)*M) :=
        work_peak Q h A N _ _ _ geom floor seed v
      _ ≤ (w+1)^c*(((D+1)^passes)^(s w)*(a*(w+1)^b*K^(s w)*2^(w/2))) :=
        Nat.mul_le_mul rate (Nat.mul_le_mul d size)
      _ = a*(w+1)^(b+c)*((D+1)^passes*K)^(s w)*2^(w/2) := by
        generalize (D+1)^passes = e
        rw [pow_add (w+1) b c,mul_pow e K (s w)]
        generalize (w+1)^c = x
        generalize (w+1)^b = y
        generalize K^(s w) = z
        generalize e^(s w) = v
        generalize 2^(w/2) = q
        ring
      _ ≤ _ := (Nat.mul_le_mul_left _ low).trans room

end Hierarchy.TraceDistribution.FactorWork

end
end OAI
