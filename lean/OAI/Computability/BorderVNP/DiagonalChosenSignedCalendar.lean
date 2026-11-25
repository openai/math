import OAI.Computability.BorderVNP.DiagonalSignedSeedSchedule
import OAI.Computability.BorderVNP.DiagonalChargedFrozenOutput
import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.DiagonalSignedBlankLayout
import OAI.Computability.BorderVNP.PackedTableBoundSites
import OAI.Computability.BorderVNP.RoutingISAScheduleClockCube
import OAI.Computability.BorderVNP.CubeTeamCheckedRowClock

/-! # Common choice of the physical signed verifier, packet, and native time budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Filter Branch Crossing Cover Epoch Packing DeckGrid PackedHistoryCircuit RoutingISA VPVNP
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter TeamScales
open Packing.Inherited FrozenTape ExternalSew TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open RoutingISA.SignedTaskArena _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical
open scoped Classical BorderVNP.Epoch.Cube

set_option maxRecDepth 6500
set_option maxHeartbeats 1800000

variable {D m : ℕ} [NeZero D] {F K : Type} [Field F] [Field K] {G : PaidIdentity F D m}
    {S : SiteSchedule G} (cube : FixedCube K) {extra E deg Q a₀ b₀ j : ℕ}
    {scales : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} scales (E+1) deg Q a₀ b₀ j)
    (φ : K →+* F) (q : ℕ) (adv : ℕ → ℕ)

/-- The selected physical geometry ceiling, signed packet installation and per-directory emissions at one length. -/
def CalendarOutputAt (c k factor A n : ℕ) : Prop :=
  let g := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
  let r := stretch b.ρ n
  let d := CoverScale.initialDepth (Cube D) r n-1
  let tiles := GridHosts.tileCount (Fintype.card (Epoch.Cube D)) d
  let T := epochs scales.τ n
  let cells := CoverScale.sites (Cube D) (EnrichedOuter.depth S (d+1) T)
  let copies := TeamScales.width n scales.α
  let R := b.physical.teamsPred n
  NativeGeometryWindow (8*(11920000+1500000+16008100*A+37)) (4*(E+2)) n r
    (b.physical.word n) (R+1) tiles ((fan S)^T*tiles)
    (routingRows (boundaryShape S (d+1) T) cells ((fan S)^T*tiles) ((R+1)*tiles)) ∧
  SignedReaderInstallAt (aux:=φ ∘ cube.table) (q:=q) cube b (cube.signedSiteProgram G) adv c k factor
    (4*(E+2)) (8*(11920000+1500000+16008100*A+37)) n ∧
  ∀ {teams time pins link inner : ℕ} {Edge : Type} (wiring : Wiring teams r time pins link inner n Edge)
    (order : Fin tiles ≃ (Fin (Fintype.card (Epoch.Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Epoch.Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (desc : ℕ) (number : G.Entry → ℕ),
    let dir := b.signedStartupDirectory n desc
    let physical : Directory.Layout := {dir with sites := tiles, entries := (fan S)^T*tiles}
    physical = dir ∧ SignedPacketInputBounds S (d+1) T cells ((R+1)*tiles) (60*logWidth r n) (b.physical.word n)
      (logWidth r n) E A g (Boundary.seedFormat wiring order position copies) physical rfl number

/-- A positive common header has a canonical zero-traffic layout on exactly the same physical links. -/
def CalendarBlankAt (c k n : ℕ) : Prop :=
  let r := stretch b.ρ n
  let R := b.physical.teamsPred n
  let T := adv (adviceScale b.σ b.ρ n)
  let symbols := alphabet scales.α n
  let X := (R+1)*exterior ((scales.τ:ℝ)/5) r n
  let blocks := blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1))
  let cap := declarationCap cube.pred symbols blocks cube.b cube.h cube.width
  let reserve := SeedPlan.profileReserve r n
  let tally := b.physical.tally n
  ∀ {l size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {C : CommonField G (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch C)
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    (reader : ChosenReader chart (R+1) r (b.physical.multBits n) tally (b.physical.word n) (T+6)),
    reader.charge ≤ c*(T+1)^k →
    let dim := pairedTableParameters (l+1) size+Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    let len := PositiveFields.width reserve cube.pred symbols cap (R+1) dim tally
    ∃ blank : Routing.WireLayout (R+1) r (b.physical.link n),
      blank.header = len ∧ 0<blank.header ∧ blank.width=(fun _ _ => 0) ∧
      ∀ (later : Routing.WireLayout (R+1) r (b.physical.link n)) (same : later.header=blank.header)
        (bits : List Bool) (old : bits.length=blank.header),
        exterior blank bits old (fun _ _ _ => false) =
          exterior later bits (old.trans same.symm) (fun _ _ _ => false)

/-- The complete addressed signed task for every charged chart on this length. -/
def CalendarTaskAt (c k headerFactor C power n : ℕ) : Prop :=
  ∀ l, n=l+1 →
  let r := stretch b.ρ n
  let R := b.physical.teamsPred n
  let W := b.physical.word n
  let link := b.physical.link n
  let lit := literal scales.α n
  let start := CoverScale.initialDepth (Epoch.Cube D) r n
  let V := CoverScale.sites (Epoch.Cube D) start
  let T := epochs scales.τ n
  let entries := (epochCopies S)^T*V
  let reserve := SeedPlan.profileReserve r n
  let symbols := alphabet scales.α n
  let X := (R+1)*exterior ((scales.τ:ℝ)/5) r n
  let cap := declarationCap cube.pred symbols (blocksFor X (cube.h*cube.b) (symbols^(cube.pred+1)))
    cube.b cube.h cube.width
  let lim := adv (adviceScale b.σ b.ρ n)
  ∀ {size : ℕ} {ord : Fin (l+1) × Bool ≃ Fin (2*(l+1))}
    {common : CommonField G (φ ∘ cube.table) q l size ord} (chart : AdvisedBranch common)
    [Fact common.p.Prime] [Algebra (ZMod common.p) chart.E]
    (reader : ChosenReader chart (R+1) r W W W (lim+6)), reader.charge≤c*(lim+1)^k →
    let par := pairedTableParameters (l+1) size
    let scalars := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    let len := PositiveFields.width reserve cube.pred symbols cap (R+1) (par+scalars) W
    let initial : StartupArena := ⟨R+1,r,lit,link,len,reader.packetBitCount⟩
    let query := Fintype.card (Board.Physical par (lim+6) W (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width))
    let guesses := Fintype.card (Guess (Fin par) reader.gridRank (Nat.clog 2 common.p+1) (Nat.clog 2 common.p))
    ∀ (desc ceiling outputs field : ℕ) (dirs : GeometryDirectories), 1≤field →
      GeometryAdviceRate.packetWords ceiling reserve outputs field*W ≤ r*width n (95/100:ℝ) →
      let dir := freeDirectory R r lit link V (blockWidth (r*n) V) entries desc
      let task := b.frozenSignedTask cube n l size headerFactor initial dir reserve ceiling outputs field dirs
      let raw := rawAddress initial reserve cube.pred symbols cap
      task.ScalarRoom W query guesses reader.gates (C*(r*n+1)^power) ∧
        task.endAddress W query guesses reader.gates < 2^W ∧
        initial.next ≤ task.cube.header.header ∧ raw+(R+1)*(par+scalars)*W = initial.ibase ∧
        initial.frame+30 < 2^W ∧ initial.ibase+(par+2)*(lim+6) ≤ task.tallyBits ∧
        initial.hbase+(par+2)*(lim+6) ≤ task.tallyBits ∧
        initial.dense+(6+3*reader.gates+query)*W ≤ task.tallyBits

/-- All five phase budgets with coefficients from the actual fixed signed program. -/
noncomputable def EpochScales.chosenSignedWindows (scales : EpochScales S (cube.pred+1) extra)
    (E n r : ℕ) :=
  let selector := Cube.Tally.selectorWidth cube.pred cube.copies cube.h
  let routeK := 512*(cube.pred+1+selector+1)
  let fixed := (CubeConstants.install (cube.cubeID G)).slots
  let args := Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
  let finish := Evaluator.ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width args
  let read := Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width
  scales.signedWindows (E+2) routeK fixed finish read n r

/-- At an admitted length all the phase, field-reader, packet, sparse-burst,
and frozen-site estimates refer to this same scheduled batch. -/
structure SignedCalendarAt (cube : FixedCube K) {extra E p Q breadth sourcePower : ℕ}
    {scales : EpochScales S (cube.pred+1) extra}
    (b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourcePower+1))
    (φ : K →+* F) (q : ℕ) (hm : 0 < m) (header C A₀ a B₀ b₁ J j outputCoeff addr pow cut : ℕ)
    (adv : ℕ → ℕ) (c k factor n : ℕ) : Prop where
  /-- Cut, initial capacity, and primitive table bounds at this length. -/
  length : LengthBudget b cut n
  /-- Checked sparse geometry frames and their measured total work. -/
  receipt : selectedReceiptAt.{0,1} S scales C p n (stretch b.ρ n)
  /-- One true augmented seed machine with its measured phase sizes and public tape bound. -/
  seed : SignedSeedAt G scales hm header Q A₀ a B₀ b₁ J j n (stretch b.ρ n)
  /-- Private cell validator on original received inputs. -/
  privateCell : PrivateCellBudgetAt 3076 (tableLimit G) (breadth+10) (sourcePower+1) (16*(G.count+1)) 1 (E+2) n (stretch b.ρ n)
  /-- The greatest genuine paid-or-cube scalar index fits the checked
  digit bound of the private validator. -/
  sourceDigits : let g := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    (g-1).size+1 ≤ breadth*(logWidth (stretch b.ρ n) n+1)^sourcePower
  /-- Every cell's reported multiplicity consumes one full hardware word. -/
  reportDigits : b.physical.word n ≤ (logWidth (stretch b.ρ n) n+1)^(E+2)
  /-- Measured copy lengths and sparse private interpreter steps. -/
  sparse : SparseExterior.PrivateCallsAt 3076 (tableLimit G) (breadth+10) (sourcePower+1) (16*(G.count+1)) 1 (E+2) n (stretch b.ρ n)
  /-- Curve and integer multiplicities fit the real tape fields. -/
  tally : ReaderTallyInputsAt cube b n
  /-- Real signed program and its timed reference packet on the fixed geometry. -/
  sites : SignedSitesAt G cube b φ q adv c k n
  /-- The five numerical charges together lie inside the timed simulator. -/
  time : let r := stretch b.ρ n
    let win := scales.chosenSignedWindows cube E n r
    win.core+win.before+win.argumentsCalls+win.finish+win.reader ≤ ticks ((scales.τ:ℝ)/5) r n
  /-- Charged frozen output, installed reader, and true word bounds on every original roster. -/
  output : CalendarOutputAt cube b φ q adv c k factor outputCoeff n
  /-- An initial zero-traffic layout for the true positive header and every later routed word. -/
  blank : CalendarBlankAt cube b φ q adv c k n
  /-- Signed address space and common raw header on the physical task. -/
  task : CalendarTaskAt cube b φ q adv c k header addr pow n

/-- Select the cube, shortening, fixed-source bounds and stretched batch before
any polynomial advice bound, field reader, candidate or pin assignment. Afterwards
one length threshold obtains every physical estimate for that characteristic. -/
theorem exists_chosen_signed_calendar (G : PaidIdentity F D m) (φ : K →+* F) (q : ℕ) [CharP F q]
    (hm : 0 < m) (minimum : ℕ) :
    ringChar F = q ∧
    ∃ cube : FixedCube K, minimum ≤ cube.h*cube.b ∧
    ∃ S : SiteSchedule G, (∀ z ≥ S.floor, S.FitsLevels z ∧ S.HasLeaves z ∧ S.RunsEnriched.{1} z) ∧
    ∀ extra : ℕ, ∃ scales : EpochScales S (cube.pred+1) extra, ∃ C p : ℕ,
    ∀ E : ℕ, ∃ outputCoeff : ℕ, ∀ headerExtra Qextra sourceDigitCoeff sourceDigitPower : ℕ,
    let header := 8+headerExtra
    let Q := Qextra+1
    let g := Fintype.card (G.Entry ⊕ TableEntry cube.pred cube.b cube.h cube.copies cube.width)
    let breadth := max ((g-1).size+1) sourceDigitCoeff
    ∃ A₀ a B₀ b₁ J j : ℕ, ∀ limit : ℝ, 0 < limit →
    ∃ b : JointSchedule.{0} scales (E+1) (max (5*(E+2)) p) Q 3076 (breadth+10) (sourceDigitPower+1),
      b.ω ≤ limit ∧ ∀ cut : ℕ, ∀ adv : ℕ → ℕ, PolynomiallyBounded adv → ∀ c k factor : ℕ,
      ∃ addr pow : ℕ, ∀ᶠ n : ℕ in atTop,
        SignedCalendarAt cube b φ q hm header C A₀ a B₀ b₁ J j outputCoeff addr pow cut adv c k factor n := by
  refine ⟨ringChar.eq F q,?_⟩
  obtain ⟨cube,width,S,physical,select⟩ := exists_signed_seed_schedule G φ q hm minimum
  refine ⟨cube,width,S,physical,?_⟩
  intro extra
  obtain ⟨scales,C,p,choose⟩ := select extra
  refine ⟨scales,C,p,?_⟩
  intro E
  obtain ⟨outputCoeff,outputs⟩ := scales.exists_charged_signed_output cube φ q E
  refine ⟨outputCoeff,?_⟩
  intro headerExtra Qextra sourceDigitCoeff sourceDigitPower header Q g breadth
  let sel := Cube.Tally.selectorWidth cube.pred cube.copies cube.h
  let routeK := 512*(cube.pred+1+sel+1)
  let fixed := (CubeConstants.install (cube.cubeID G)).slots
  let packet := Cube.Tally.argumentWidth cube.pred cube.b cube.h cube.copies cube.width
  let finish := Evaluator.ScheduleClock.cubeCoefficient cube.pred cube.b cube.h cube.copies cube.width packet
  let read := Cube.TeamRowClock.physicalCoefficient cube.pred cube.b cube.h cube.copies cube.width
  obtain ⟨A₀,a,B₀,b₁,J,j,batch⟩ := choose header E (5*(E+2)) Q 3076 (tableLimit G) (breadth+10)
    (sourceDigitPower+1) (16*(G.count+1)) 1 (E+2) (E+2) routeK fixed finish read
  refine ⟨A₀,a,B₀,b₁,J,j,?_⟩
  intro limit positive
  obtain ⟨b,cap,all⟩ := batch limit positive
  refine ⟨b,cap,?_⟩
  intro cut adv poly c k factor
  obtain ⟨addr,pow,tasks⟩ := b.eventually_frozen_signed_task cube φ q adv poly c k header
  refine ⟨addr,pow,?_⟩
  have output := outputs b (le_max_left ..) adv poly c k factor
  have blank := b.eventually_blank_signed_layout (aux := φ ∘ cube.table) (q := q) cube adv poly c k
  filter_upwards [all cut adv poly c k,output,blank,tasks] with n bounds emit free fits
  let r := stretch b.ρ n
  have digits : (g-1).size+1 ≤ breadth*(logWidth r n+1)^sourceDigitPower :=
    (le_max_left _ _).trans (Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _))
  have report : b.physical.word n ≤ (logWidth r n+1)^(E+2) :=
    Nat.pow_le_pow_left (Nat.le_succ (logWidth r n)) _
  refine ⟨bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2.1,digits,report,bounds.2.2.2.2.1,
    bounds.2.2.2.2.2.1,bounds.2.2.2.2.2.2.1,bounds.2.2.2.2.2.2.2,emit,free,?_⟩
  exact fun l hn => fits l hn ⟨bounds.2.2.1.choose⟩

end Diagonal

end BorderVNP
end Computability
end OAI
