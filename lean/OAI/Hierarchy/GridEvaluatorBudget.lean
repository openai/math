import OAI.Hierarchy.GridCompilerAdmission
import OAI.Hierarchy.GridControllerSimGeometry
import OAI.Hierarchy.GridSimulationPublish
import OAI.Hierarchy.GridPhysicalRootCount
import OAI.Hierarchy.GridSimulationPadding
import OAI.Hierarchy.FactorCompilerBudget
import OAI.Hierarchy.GridTraceCap
import OAI.Hierarchy.TraceIterationTerminalRoom

namespace OAI
/-! # Native evaluator clock on the original grid

The selector guard, compressor, terminal padding, node registration, classifier,
endpoint scatter and both ordered rail writers use the same original grid volume.
The evaluator exponent is independent of the polynomial size of its input header. -/
namespace Hierarchy.GridEvaluatorBudget
open GridScale Filter ThreeFlat Diagonal PhysicalStage NavigationPass NavigationDirectory
open RAM Computability.VPVNP.BurstRAM UniversalGrid GridThrough
open scoped Classical
noncomputable section

/-- Literal sequential prices of admission, registration, assignment and publication. -/
def sim (w m n q B pinWidth e cap hdr text bits N stages full span logRadix pc : ℕ)
    (a : Archive) (ss : List Stage) (edges : ℕ) (ar : GridOrderedSources.Arena) : ℕ :=
  let P := GridPinPublisher.canonical w (m+1) n q pinWidth hdr (cap+1) text B e bits N stages full span
  let K := 2^(3*w/5)
  let b := GridControllerIdle.shape m n B logRadix q pinWidth pc
  K+(K+Archive.terminalTime (a.terminal ss edges (64*w))) + 2*K +
    (GridSimulation.assignTime w N ((m+1)+2) +
      (3+e*(1+GridPinNativeLoops.seedOps.length)+P.budget (64*w))) +
    (GridControllerSimGeometry.cost (64*w) ar b + (9+5*b.data+11*(b.rails*2)))

private def rawCoeff (C : ℕ) := 6+64*(C+21)

private theorem raw_le {w e B n C d M : ℕ} (header : n ≤ C*(w+1)^d)
    (rails : e ≤ M) (compact : B ≤ M) (pos : 1 ≤ M) :
    GridSelfHeader.rawSize w e B n ≤ rawCoeff C*(w+1)^(d+2)*M := by
  let U := (w+1)^(d+2)
  have one : 1 ≤ U := Nat.pow_pos (Nat.succ_pos w)
  have square : w^2 ≤ U := (Nat.pow_le_pow_left (Nat.le_succ w) 2).trans
    (Nat.pow_le_pow_right (Nat.succ_pos w) (by omega))
  have low : (w+1)^d ≤ (w+1)^(d+1) := Nat.pow_le_pow_right (Nat.succ_pos w) (by omega)
  have lin : w+1 ≤ (w+1)^(d+1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos w) (show 1 ≤ d+1 by omega)
  have count : GridReceiverHeader.count w ≤ 21*(w+1)^(d+1) :=
    (by unfold GridReceiverHeader.count; omega : GridReceiverHeader.count w ≤ 21*(w+1)).trans
      (Nat.mul_le_mul_left _ lin)
  have operands : n+GridReceiverHeader.count w ≤ (C+21)*(w+1)^(d+1) := by
    rw [Nat.add_mul]; exact Nat.add_le_add (header.trans (Nat.mul_le_mul_left C low)) count
  have storage : (n+GridReceiverHeader.count w)*(64*w) ≤ 64*(C+21)*U*M := calc
    _ ≤ ((C+21)*(w+1)^(d+1))*(64*(w+1)) := Nat.mul_le_mul operands (by omega)
    _ = 64*(C+21)*U := by dsimp [U]; rw [show d+2=(d+1)+1 by omega,pow_succ]; ring
    _ ≤ _ := Nat.le_mul_of_pos_right _ pos
  have rails' := Nat.mul_le_mul rails one
  have compact' := Nat.mul_le_mul compact square
  have bit := Nat.mul_le_mul pos square
  unfold GridSelfHeader.rawSize rawCoeff
  change _ ≤ (6+64*(C+21))*U*M
  rw [Nat.add_mul,Nat.add_mul]
  nlinarith only [rails',compact',bit,storage]

private theorem lanes_le (bits span : ℕ) : (bits+span-1)/span ≤ bits := by
  by_cases hz : span=0
  · simp [hz]
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hz)).mpr
  have := Nat.le_mul_of_pos_right bits (Nat.pos_of_ne_zero hz)
  rw [Nat.succ_mul]; omega

/-- The pin publisher reads all receiver pins, including padding, and both endpoints of every rail. -/
private theorem pin_clock {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D) (k A C d : ℕ)
    (hk : 0 < k) : ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w →
    let a := overhead Q D w
    let B := pairs A w q
    let e := external k a B
    let g := side a
    let pin := pins w a
    let ell := selector k w a
    ∀ n hdr text bits N stages full span, n+1=g → hdr ≤ C*(w+1)^d →
      bits ≤ GridSelfHeader.rawSize w e B hdr+ell → N ≤ B →
      let P := GridPinPublisher.canonical w k n q pin hdr ell text B e bits N stages full span
      3+e*(1+GridPinNativeLoops.seedOps.length)+P.budget (64*w) ≤ g^k*B := by
  let c := 900*22^(k+2)*10*rawCoeff C
  filter_upwards [controller_room env k A c ((k+2)+(d+2)) hk, budgets env k A 1 0]
    with w available wb
  intro q hq htop a B e g pin ell n hdr text bits N stages full span hn hs hb hN P
  let M := ticks k a q * pin + e + B
  let Z := rawCoeff C*(w+1)^(d+2)*M
  have bpos : 0 < B := (Nat.two_pow_pos _).trans_le (wb q hq htop).bankLo
  have pos : 1 ≤ M := by dsimp [M]; omega
  have tpos : 0 < ticks k a q := by dsimp [ticks,side]; positivity
  have ppos : 0 < pin := Nat.two_pow_pos _
  have teq : P.ticks=ticks k a q := by change (n+1)^k*q=g^k*q; rw [hn]
  have dims : P.header.pins=pin := rfl
  have prices := (wb q hq htop).density
  have sel : ell ≤ pin := by simpa using prices.2.2.1
  have MZ : M ≤ Z := Nat.le_mul_of_pos_left _ (by dsimp [rawCoeff]; positivity)
  have raw : GridSelfHeader.rawSize w e B hdr ≤ Z := raw_le hs (by dsimp [M];omega) (by dsimp [M];omega) pos
  have pinM : pin ≤ M := (Nat.le_mul_of_pos_left _ tpos).trans (by dsimp [M];omega)
  have tm : ticks k a q ≤ M := (Nat.le_mul_of_pos_right _ ppos).trans (by dsimp [M];omega)
  have lane : P.lanes ≤ 2*Z := by
    change (bits+span-1)/span ≤ _
    exact (lanes_le ..).trans (by omega)
  have lit : P.literals ≤ Z := (Nat.sub_le _ _).trans raw
  have rs : e ≤ Z := (show e ≤ M by dsimp [M];omega).trans MZ
  have nm : N ≤ M := hN.trans (by dsimp [M]; omega)
  have all : 1+P.ticks+N+P.lanes+P.ticks*P.header.pins+P.literals+P.endpoints ≤ 10*Z := by
    change _+e*2 ≤ 10*Z
    rw [teq,dims]
    have total : ticks k a q*pin ≤ M := by dsimp [M];omega
    omega
  have classBound : (20*(w+1)+2)^(k+2) ≤ 22^(k+2)*(w+1)^(k+2) := by
    rw [←Nat.mul_pow]
    exact Nat.pow_le_pow_left (by omega : 20*(w+1)+2 ≤ 22*(w+1)) _
  apply (GridPinPublisher.canonical_cost w k n q pin hdr ell text B e bits N stages full span).trans
  calc
    _ ≤ 900*(22^(k+2)*(w+1)^(k+2))*(10*Z) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ classBound) all
    _ = c*(w+1)^((k+2)+(d+2))*M := by dsimp only [c,Z]; rw [pow_add]; ring
    _ ≤ _ := (available q hq htop).1

/-- The public edge count at the final grade of this particular repeated block. -/
theorem terminal_edges {F : Type} [Field F] (B : Block F) {u s : ℕ → ℕ}
    (scale : TraceDistribution.Scale u s) : ∀ᶠ w : ℕ in atTop,
    ∀ axes, axes = u w+1-w/2 → B.blockCharge*s w ≤ axes →
      (B.repeat (s w)).finalEdges (axes-(B.repeat (s w)).charge) axes ≤ 2^(3*w/5) := by
  exact TraceAdmission.terminal_edges B scale

/-- Full native execution on the original grid. Each public root and edge count
is bounded by `GridPhysicalAdmission.eventual_root_count` and `terminal_edges`,
respectively. The fixed number 2 is chosen before the receiver header is compiled. -/
theorem eventual_clock {F : Type} [Field F] [Fintype F] {Q : ℕ → ℕ} {D : ℕ → ℝ}
    (env : Envelopes Q D) (m A C d : ℕ) : ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w →
    let k := m+1
    let a := overhead Q D w
    let B := pairs A w q
    let e := external k a B
    let ell := selector k w a
    let pin := pins w a
    let K := 2^(3*w/5)
    ∀ n hdr text bits N stages full span logRadix pc (arch : Archive) (ss : List Stage) edges
      (ar : GridOrderedSources.Arena) (X : Catalyst.Approximation F k (q*pin)),
      n+1=side a → hdr ≤ C*(w+1)^d → bits ≤ GridSelfHeader.rawSize w e B hdr+ell →
      N ≤ K → edges ≤ K → arch.pairCapacity ≤ ell → X.size ≤ B →
      let b := GridControllerIdle.shape m n B logRadix q pin pc
      let ta := GridControllerIdle.guardedCost (64*w) ar b (ell-1)
      let tb := sim w m n q B pin e (ell-1) hdr text bits N stages full span logRadix pc arch ss edges ar
      let limit := GridPaddedCellImage.limit e ((n+1)^k) B (Ordered.hiddenCount e n) (Ordered.edgeCount e n) (Fintype.card F)
      (GridNativeEvaluator.tailTime (n:=n) (e:=e) X +
        GridCompilerAdmission.clock w k n e B limit (4+max ta tb))+4+5*ell ≤ evalWork w k A 2 a q := by
  let k := m+1
  let dim := k+2
  let fixed := 13000000*(m+2)+45000*((Fintype.card F)^2+11)
  filter_upwards [pin_clock env k A C d (Nat.succ_pos m),
    controller_room env k A (2*FactorBucketRAM.budgetConstant dim) (dim+1) (Nat.succ_pos m),
    controller_room env k A 7000 2 (Nat.succ_pos m), budgets env k A 1 0,
    sublinear env 20, eventually_ge_atTop (fixed+5000)]
    with w pubRoom classRoom headerRoom budget age large
  intro q hq htop kl a B e ell pin K n hdr text bits N stages full span logRadix pc arch ss edges ar X
    hn header bitSize roots wires capacity size b ta tb limit
  let L := (n+1)^k*B
  let M := ticks k a q*pin+e+B
  have wb := budget q hq htop
  have dens := wb.density
  change 20*a ≤ w at age
  have sel : ell ≤ pin := by simpa [kl,k] using dens.2.2.1
  have kp : K ≤ pin := Nat.pow_le_pow_right (by decide : 0 < 2) (by
    omega)
  have qpin : q*pin ≤ B := by simpa [kl,k] using dens.1
  have pb : pin ≤ B := (Nat.le_mul_of_pos_left _ hq).trans qpin
  have bpos : 0 < B := (Nat.two_pow_pos _).trans_le wb.bankLo
  have bL : B ≤ L := Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos n))
  have bM : B ≤ M := by dsimp [M];omega
  have unit : 1 ≤ L := bpos.trans_le bL
  have um : 1 ≤ M := bpos.trans_le bM
  have klow : K ≤ L := kp.trans (pb.trans bL)
  have elow : ell ≤ L := sel.trans (pb.trans bL)
  have ellpos : 0 < ell := Nat.two_pow_pos _
  have diff : ell-1+1=ell := by omega
  have clkN : N ≤ B := roots.trans (kp.trans pb)
  have pinFee := pubRoom q hq htop n hdr text bits N stages full span hn header bitSize clkN
  have classifier : FactorBucketRAM.ticks w N dim ≤ L := calc
    _ ≤ FactorBucketRAM.budgetConstant dim*(w+1)^(dim+1)*(N+1) := FactorBucketRAM.clock_bound ..
    _ ≤ FactorBucketRAM.budgetConstant dim*(w+1)^(dim+1)*(2*M) := Nat.mul_le_mul_left _ (by omega)
    _ = 2*FactorBucketRAM.budgetConstant dim*(w+1)^(dim+1)*M := by ring
    _ ≤ _ := by simpa only [L,hn] using (classRoom q hq htop).1
  have unpack : GridReceiverHeader.count w*(5*(64*w)+6)+6 ≤ L := calc
    _ ≤ 7000*(w+1)^2 := by unfold GridReceiverHeader.count; nlinarith
    _ ≤ 7000*(w+1)^2*M := Nat.le_mul_of_pos_right _ um
    _ ≤ _ := by simpa only [L,hn] using (headerRoom q hq htop).1
  have classification : GridSimulation.assignTime w N dim ≤ 2*L := by
    unfold GridSimulation.assignTime; omega
  have term := GridSelector.terminal_price arch ss edges (64*w)
  have term' : Archive.terminalTime (arch.terminal ss edges (64*w)) ≤ 2000*L := by omega
  have idle := GridControllerIdle.work_in_cells (64*w) ar m n B logRadix q pin pc qpin bpos
  have guard := GridControllerIdle.guard_price ar (ell-1)
  have simRows := GridControllerSimGeometry.receiver_work_in_cells (64*w) ar m n B logRadix q pin pc qpin bpos
  have tA : ta ≤ (3520*(m+2))*L := by
    change GridIdleGuard.cost _ _ (ell-1)+GridControllerIdle.cost _ _ _ ≤ _
    change GridControllerIdle.cost _ _ b ≤ 20+3000*(m+1)*L at idle
    rw [diff] at guard
    nlinarith only [idle,guard,elow,unit,Nat.zero_le (m*L)]
  have tB : tb ≤ (4000*(m+2))*L := by
    dsimp only [tb,sim]
    rw [diff]
    change 3+e*(1+GridPinNativeLoops.seedOps.length)+_ ≤ (side a)^k*B at pinFee
    rw [← hn] at pinFee
    change GridControllerSimGeometry.cost _ _ b+_ ≤ 25+1250*(m+1)*L at simRows
    change K+(K+Archive.terminalTime _)+2*K+(GridSimulation.assignTime w N dim+_)+_ ≤ _
    calc
      _ ≤ L+(L+2000*L)+2*L+(2*L+L)+(25+1250*(m+1)*L) :=
        Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add klow (Nat.add_le_add klow term'))
            (Nat.mul_le_mul_left 2 klow)) (Nat.add_le_add classification pinFee)) simRows
      _ ≤ _ := by nlinarith only [unit,Nat.zero_le (m*L)]
  have lr : e*(n+1) ≤ 2*kl*((n+1)^kl*B) := by
    change ((m+1)*(2*(side a)^((m+1)-1)*B))*(n+1) ≤ _
    rw [← hn]; simp only [Nat.add_sub_cancel,kl,pow_succ]; apply le_of_eq; ring
  have outer := GridCompilerAdmission.charged_path (w:=w) (ell:=ell) X (4+max ta tb) bpos size lr elow
  have maxPrice : max ta tb ≤ (4000*(m+2))*L := max_le
    (tA.trans (Nat.mul_le_mul_right L (Nat.mul_le_mul_right (m+2) (by decide : 3520 ≤ 4000)))) tB
  have fpos : 45000*((Fintype.card F)^2+11) ≤ 45000*((Fintype.card F)^2+11)*L := Nat.le_mul_of_pos_right _ unit
  have fullPrice : (4+max ta tb)+(12000000*(kl+1)+4000*w)*L+45000*((Fintype.card F)^2+11) ≤
      (fixed+4000*w)*L := by dsimp only [kl,fixed]; nlinarith only [maxPrice,unit,fpos,Nat.zero_le (m*L)]
  apply outer.trans (fullPrice.trans ?_)
  change (fixed+4000*w)*L ≤ (side a)^kl*B*(w+1)^2
  rw [← hn]
  have factor : fixed+4000*w ≤ (w+1)^2 := by nlinarith only [large,Nat.mul_le_mul_right w large]
  simpa only [L,k,kl,Nat.mul_comm] using Nat.mul_le_mul_right L factor

/-- Machine clock for the actual public directory, including its final physical
row count. Every selected history and both values of the simulation flag use this clock. -/
theorem eventual_execution {F : Type} [Field F] [Fintype F] {Q : ℕ → ℕ} {D : ℕ → ℝ}
    (env : Envelopes Q D) (block : Block F) {u s : ℕ → ℕ} (scale : TraceDistribution.Scale u s)
    (m A C d : ℕ) : ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w →
    let k := m+1
    let a := overhead Q D w
    let B := pairs A w q
    let e := external k a B
    let ell := selector k w a
    let pin := pins w a
    let axes := u w+1-w/2
    block.blockCharge*s w ≤ axes →
    ∀ n hdr text off slots static logRadix pc (ar : GridOrderedSources.Arena)
      (X : Catalyst.Approximation F k (q*pin)), n+1=side a → hdr ≤ C*(w+1)^d → X.size ≤ B →
      let arch := TraceSeedWriter.archive block w axes off slots (ell-1) static
      let P := block.repeat (s w)
      let rem := axes-P.charge
      let ss := P.directory rem axes
      let N := (TraceRecovery.lastLayer arch.K ss arch.cursor arch.seedLayer).count
      let bits := GridSelfHeader.rawSize w e B hdr
      let b := GridControllerIdle.shape m n B logRadix q pin pc
      let time := 4+max (GridControllerIdle.guardedCost (64*w) ar b (ell-1))
        (sim w m n q B pin e (ell-1) hdr text bits N ss.length (2^axes) (2*2^(w/2)) logRadix pc arch ss
          (P.finalEdges rem axes) ar)
      let limit := GridPaddedCellImage.limit e ((n+1)^k) B (Ordered.hiddenCount e n) (Ordered.edgeCount e n) (Fintype.card F)
      (GridNativeEvaluator.tailTime (n:=n) (e:=e) X +
        GridCompilerAdmission.clock w k n e B limit time)+4+5*ell ≤ evalWork w k A 2 a q := by
  filter_upwards [eventual_clock (F:=F) env m A C d, GridPhysicalAdmission.eventual_root_count block scale,
    terminal_edges block scale] with w charged rootsCount edgeCount
  intro q hq top k a B e ell pin axes fits n hdr text off slots static logRadix pc ar X rows words size
    arch P rem ss N bits b time limit
  exact charged q hq top n hdr text bits N ss.length (2^axes) (2*2^(w/2)) logRadix pc arch ss
    (P.finalEdges rem axes) ar X rows words (Nat.le_add_right _ _) (rootsCount rfl fits off slots (ell-1) static)
    (edgeCount axes rfl fits) (Nat.sub_le _ _) size

end
end Hierarchy.GridEvaluatorBudget

end OAI
