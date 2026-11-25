import OAI.ThreeFlat.Diagonal.TraceNodeBankBounds
import OAI.ThreeFlat.Diagonal.TraceNodeCompactCode
import OAI.Hierarchy.TraceRetainedBounds
import OAI.Hierarchy.TraceRecordScale
import OAI.ThreeFlat.Diagonal.PhysicalNodeDirectoryCap
import OAI.ThreeFlat.Diagonal.PhysicalNodeChargeWork

namespace OAI
/-! # Actual stage count, charge and time at the trace width -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication

open RAM RAM.NavigationNodeRows NavigationDirectory PhysicalStage TraceNodeHeaders

variable {F : Type} [Field F]

/-- The physical stage never has more sites than the initial cursor layer. -/
theorem program_site_count {degree : ℕ} (P : PhysicalStage.Program F degree) (K rem v : ℕ) (c : Cursor) (l : Layer)
    (start : l.count≤v*2^(P.charge+rem)) (q : Layers) (hit : q∈nodeLayers K (P.directory rem v) c l) :
    q.actual.count≤v*2^(P.charge+rem) := by
  induction P generalizing c l v with
  | done => obtain rfl := List.mem_singleton.mp hit; exact start
  | shrink s t T small tail ih =>
    let tag := 2^CompressorPacking.tagBits (2^s)
    let x : CompressorPacking.Native.ShrinkStage.Dimensions :=
      ⟨v,2^s,2*2^s+1,tag,2^(tail.charge+rem),2^t⟩
    let op := Stage.shrink x
    rcases List.mem_cons.mp hit with rfl|later
    · exact start
    · have sub := ih (v:=v*tag) (c:=(allocate K c op).next) (l:=nodeLayer K c op) le_rfl later
      have both := Program.shrink_positions s t (tail.charge+rem) v
      have newCount : (v*tag)*2^(tail.charge+rem)=x.outputSites := rfl
      rw [newCount] at sub
      change x.originalSites=_ ∧ x.outputSites*4≤x.originalSites at both
      exact sub.trans ((by omega : x.outputSites≤x.originalSites).trans_eq
        (by simpa only [Program.charge,Nat.add_assoc] using both.1))
  | refresh s t h pad coeff γ C T two pos sym grade zero conn deg tail ih =>
    let op := Stage.refresh v (2^s) (2^(tail.charge+rem)) h pad
    rcases List.mem_cons.mp hit with rfl|later
    · exact start
    · have both := Program.refresh_positions s (tail.charge+rem) v h pad
      have count : (nodeLayer K c op).count=(v*2^s)*2^(tail.charge+rem) := both.1.trans both.2.symm
      have sub := ih (v:=v*2^s) (c:=(allocate K c op).next) (l:=nodeLayer K c op) count.le later
      exact sub.trans_eq (by simpa only [Program.charge,Nat.add_assoc] using both.2)

def widthBanks : Banks := ⟨0,0,0,0,0,0,0,0⟩
def fieldCost (cap : ℕ) :=
  2*(2*(charge widthBanks cap cap cap).work+4)+8*(2*(node widthBanks).work+4)
def publicationRate (cap : ℕ) := 64+16*(2*(compactRow 0).work+4)+39+fieldCost cap

/-- The publisher visits the same instructions and fields when its physical banks move. -/
theorem compact_cost_relocate {W : ℕ} (a b : NodeArchive) (ca cb n sz : ℕ)
    (cc : a.childCap=b.childCap) (hc : a.halfCap=b.halfCap) (mc : a.motifCap=b.motifCap) :
    compactTicks ca n (rowBudget W a sz)=compactTicks cb n (rowBudget W b sz) := by
  have mask : (compactRow ca).work=(compactRow cb).work := rfl
  have nodeWords : (node a.banks).work=(node b.banks).work := rfl
  simp only [compactTicks,rowBudget,ticks,HeaderScan.binds_closed,cc,hc,mc,mask,nodeWords,
    charge_work a.banks b.banks]

/-- The 43 setup instructions are included in the bound. Only the fixed cap
affects the coefficient of the number of chronological visits and sites. -/
theorem compact_cost {w lanes per pairs trace tariff cap : ℕ} (n sz : ℕ) :
    let a := traceArchive w lanes per pairs trace tariff cap cap cap
    43+compactTicks (compactControl w) n (rowBudget (64*w) a sz)≤publicationRate cap*(n+1)*(sz+1) := by
  intro a
  have ident : (compactRow (compactControl w)).work=(compactRow 0).work := rfl
  have nodeEq : (node a.banks).work=(node widthBanks).work := rfl
  change 43+compactTicks (compactControl w) n (ticks (64*w) a.banks cap cap cap sz)≤_
  simp only [compactTicks,ticks,HeaderScan.binds_closed,charge_work a.banks widthBanks,nodeEq,ident,publicationRate,fieldCost]
  ring_nf
  omega

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage
open NavigationPass NavigationDirectory NodePublication TraceDistribution Filter
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- Header count, initial-site count, real heap size, and native publisher cost
are all bounded on the same word-width chart that admits the compressor. -/
theorem eventual_node_limits {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (_fit : B.blockCharge*s w≤u w+1-w/2),
      let k := u w+1-w/2
      let P := B.repeat (s w)
      let rem := k-P.charge
      let ops := P.directory rem k
      16*(ops.length+1)≤traceUnit w ∧
        traceBase w+64+64*ops.length+44≤compactControl w ∧
        8*(k*2^k+(ops.map Stage.heapWords).sum)≤traceUnit w ∧
        directoryCap B<2^(64*w) ∧
        ∀ lanes per pairs trace tariff,
          let a := traceArchive w lanes per pairs trace tariff (directoryCap B) (directoryCap B) (directoryCap B)
          43+compactTicks (compactControl w) (ops.length+1) (rowBudget (64*w) a (k*2^k))≤2^(3*w/5) := by
  let rate := publicationRate (directoryCap B)
  filter_upwards [eventual_stage_headers B scale,eventual_stage_heap B scale,
    record_room scale (rate*(B.levels+3)),record_room scale 1,eventually_ge_atTop 7,
    eventually_ge_atTop (directoryCap B)] with w headers heap budget base hw cap
  intro fit k P rem ops
  have head := headers rem k
  have cells := heap fit
  have seed : k*2^k≤2^(3*w/5) := by
    change 1*(s w+1)*(1+k*2^k)*(64*w+1)≤_ at base
    have grow : 1+k*2^k≤1*(s w+1)*(1+k*2^k) := Nat.le_mul_of_pos_left _ (by positivity)
    have keep : 1*(s w+1)*(1+k*2^k)≤1*(s w+1)*(1+k*2^k)*(64*w+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    exact (by omega : k*2^k≤1+k*2^k).trans (grow.trans (keep.trans base))
  have slack : 16*2^(3*w/5)≤traceUnit w := by
    change 2^4*2^(3*w/5)≤(2^w)^4
    rw [←pow_add,←pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change 64*(ops.length+2)≤2^(3*w/5) at head
  change (ops.map Stage.heapWords).sum≤2^(3*w/5) at cells
  have nonzero := Nat.two_pow_pos (3*w/5)
  refine ⟨by omega,?_,by omega,?_,?_⟩
  · unfold compactControl;omega
  · exact cap.trans_lt ((show w≤64*w by omega).trans_lt Nat.lt_two_pow_self)
  · intro lanes per pairs trace tariff a
    have lim := compact_cost (w:=w) (lanes:=lanes) (per:=per) (pairs:=pairs) (trace:=trace) (tariff:=tariff)
      (cap:=directoryCap B) (ops.length+1) (k*2^k)
    apply lim.trans
    change rate*((ops.length+1)+1)*(k*2^k+1)≤_
    have count : (ops.length+1)+1≤(B.levels+3)*(s w+1) := by
      dsimp only [ops,P]
      rw [Program.directory_length,repeated_length]
      ring_nf;omega
    have scaled := Nat.mul_le_mul_right (k*2^k+1) (Nat.mul_le_mul_left rate count)
    have before : rate*((B.levels+3)*(s w+1))*(k*2^k+1)=rate*(B.levels+3)*(s w+1)*(1+k*2^k) := by ring
    exact (scaled.trans_eq before).trans ((Nat.le_mul_of_pos_right _ (by omega : 0<64*w+1)).trans budget)

end
end Hierarchy.TraceAdmission

end OAI
