import OAI.Computability.VPVNP.CompressorSlotPhaseCosts
import OAI.Computability.VPVNP.CompressorRecordGreedyPass
import OAI.Computability.VPVNP.CompressorRecordRefreshPrepare
import OAI.Computability.VPVNP.CompressorRecordRefreshSupplyScan
import OAI.Computability.VPVNP.CompressorRecordsBundleScan
import OAI.Computability.VPVNP.CompressorRecordsShrinkScan
import OAI.Computability.VPVNP.CompressorBundleFixedGather
import OAI.Computability.VPVNP.CompressorBundleKeyTable
import OAI.Computability.VPVNP.CompressorShrinkMotifAbsolute
import OAI.Computability.VPVNP.CompressorRecordsPortRankRAM
import OAI.Computability.VPVNP.CompressorRecordsBundlePrefixRAM
import OAI.Computability.VPVNP.CompressorRecordsABWidths
import OAI.Computability.VPVNP.CompressorShrinkDemandGatherCall

/-!
# Native worker traffic at an actual compressor state

The greedy color and tag readers are charged per original base. Dense bundle
arrays are charged by the actual old-port count, and the refresh tie and supply
arrays by the counts of blocks, ports and expander arcs. The per-call caps
depend on the fixed degrees and tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CatalogRates

open BurstRAM Compression PhaseCosts
variable {w : ℕ}

/-- Coefficient of the base count for one greedy preparer followed by its reader. -/
def greedyRate (rows width arity candidates : ℕ) :=
  16 + rows + width + 2*arity*candidates*candidates

/-- Maximum instructions of either worker of a prepared greedy pass. -/
def greedyCap (rows width arity candidates : ℕ) :=
  max (33+8*rows+6*width) (13+((4*arity+4)*candidates+4)*candidates)

open Greedy Greedy.WalkLayout in
theorem preparedPassCounts {A V : Type*} {n d width arity k : ℕ}
    {L : WalkLayout w n width} {rows : OperandRows d} {m : Memory w} {enc : A → Word w}
    {order : V ≃ Fin n} {f : V → A} (h : L.PreparedPass rows m arity k enc order f) :
    ∃ prep reads,
      runSegment (prepareMachine w rows).program (1+(prepareCode rows).length) (some 0) m
        (List.replicate n []) = some prep ∧
      runSegment (visitMachine w arity k).program (1+(visitCode arity k).length) (some (L.base 0))
        (after m (eventLog prep)) (List.replicate n []) = some reads ∧
      (prep++reads).length = 2*n ∧
      RAMBuckets.cost Report.probes (prep++reads) = n*greedyRate rows.length width arity k ∧
      ∀ r ∈ prep++reads, r.events.length+1 ≤ greedyCap rows.length width arity k := by
  obtain ⟨prep,hp,_,np,cp,wp,hread⟩ := h
  obtain ⟨rs,hr',cr⟩ := hread.cost
  obtain ⟨reads,hr,_,_,nr,wr⟩ := hread
  have he : rs = reads := Option.some.inj (hr'.symm.trans hr)
  subst rs
  refine ⟨prep,reads,hp,hr,by rw [List.length_append,np,nr]; omega,?_,?_⟩
  · rw [RAMBuckets.cost_append]
    change RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) prep +
      RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) reads = _
    rw [cp,cr]; unfold greedyRate; ring
  · intro r hr
    rcases List.mem_append.mp hr with h | h
    · apply le_trans _ (le_max_left ..)
      have := (wp r h).1
      omega
    · apply le_trans _ (le_max_right ..)
      rw [(wr r h).1]; omega

open Greedy.WalkLayout in
/-- Combined per-base-vertex charge for preparing and reading the greedy colors and
displacement tags at degree `d`. -/
def greedyShrinkRate (d : ℕ) :=
  greedyRate (2*d) (2*d) 1 (2*d) + greedyRate (tagCount d) (4*tagCount d) 4 (tagCount d)

open Greedy.WalkLayout in
/-- Maximum per-call instruction bound over the color and tag passes at degree `d`. -/
def greedyShrinkCap (d : ℕ) :=
  max (greedyCap (2*d) (2*d) 1 (2*d)) (greedyCap (tagCount d) (4*tagCount d) 4 (tagCount d))

open Greedy Greedy.WalkLayout in
/-- Both greedy scans on the original base graph. The rate uses the exact base count,
which is at most the number of physical positions. -/
theorem greedyStateCounts {a g j : ℕ} (X : State a g) (hw : j ≤ w)
    (colorLayout : WalkLayout w (Fintype.card X.Base) (2 * 2 ^ a))
    (tagLayout : WalkLayout w (Fintype.card X.Base) (4 * tagCount (2 ^ a)))
    (colorMem tagMem : Memory w) (tags : X.Base → BitWord j)
    (hcolor : colorLayout.PreparedPass (colorOperandRows (2 ^ a)) colorMem 1 (2 * 2 ^ a)
      (fun v : Fin (2*2^a+1) ↦ Fin.ofNat _ v.val) X.baseIndex
        (X.slots.base.orderedColor X.baseIndex))
    (htag : tagLayout.PreparedPass (tagOperandRows (2^a)) tagMem 4 (tagCount (2^a))
      (tagWord hw) X.baseIndex tags) :
    ∃ pc rc pt rt : List (Report w),
      runSegment (prepareMachine w (colorOperandRows (2^a))).program
        (1+(prepareCode (colorOperandRows (2^a))).length) (some 0) colorMem
        (List.replicate (Fintype.card X.Base) []) = some pc ∧
      runSegment (visitMachine w 1 (2*2^a)).program (1+(visitCode 1 (2*2^a)).length)
        (some (colorLayout.base 0)) (after colorMem (eventLog pc))
        (List.replicate (Fintype.card X.Base) []) = some rc ∧
      runSegment (prepareMachine w (tagOperandRows (2^a))).program
        (1+(prepareCode (tagOperandRows (2^a))).length) (some 0) tagMem
        (List.replicate (Fintype.card X.Base) []) = some pt ∧
      runSegment (visitMachine w 4 (tagCount (2^a))).program
        (1+(visitCode 4 (tagCount (2^a))).length)
        (some (tagLayout.base 0)) (after tagMem (eventLog pt))
        (List.replicate (Fintype.card X.Base) []) = some rt ∧
      let all := (pc++rc)++(pt++rt)
      all.length = 4*Fintype.card X.Base ∧
        RAMBuckets.cost Report.probes all = Fintype.card X.Base*greedyShrinkRate (2^a) ∧
        RAMBuckets.cost Report.probes all ≤ X.positions*greedyShrinkRate (2^a) ∧
        ∀ rep ∈ all, rep.events.length+1 ≤ greedyShrinkCap (2^a) := by
  obtain ⟨pc,rc,runC,readC,nC,cC,capC⟩ := preparedPassCounts hcolor
  obtain ⟨pt,rt,runT,readT,nT,cT,capT⟩ := preparedPassCounts htag
  have csz : (colorOperandRows (2^a)).length = 2*2^a := by simp [colorOperandRows]
  have tsz : (tagOperandRows (2^a)).length = tagCount (2^a) := by simp [tagOperandRows,tagCount]
  rw [csz] at cC capC
  rw [tsz] at cT capT
  have hc : RAMBuckets.cost Report.probes ((pc++rc)++(pt++rt)) =
      Fintype.card X.Base * greedyShrinkRate (2^a) := by
    rw [RAMBuckets.cost_append,cC,cT]
    unfold greedyShrinkRate
    ring
  have hn : Fintype.card X.Base ≤ X.positions := by
    rw [State.positions,Fintype.card_prod]; exact Nat.le_mul_of_pos_right _ Fintype.card_pos
  refine ⟨pc,rc,pt,rt,runC,readC,runT,readT,?_,hc,hc.trans_le (Nat.mul_le_mul_right _ hn),?_⟩
  · rw [List.length_append,nC,nT]; omega
  · intro rep hrep
    rcases List.mem_append.mp hrep with h|h
    · exact (capC rep h).trans (le_max_left ..)
    · exact (capT rep h).trans (le_max_right ..)

open PortRefresh in
private theorem demandScanCounts {n t : ℕ} {p : Fin t → DemandScan.Params w}
    {ks : List (Fin t)} {m : Memory w} {rs : List (Report w)} (r : DemandScan.Runs p n ks m rs) :
    rs.length = n*ks.length ∧ RAMBuckets.cost Report.probes rs = 3*n*ks.length ∧
      ∀ rep ∈ rs, rep.events.length+1 ≤ 26 := by
  induction r with
  | nil => simp
  | cons k head tail ih =>
    obtain ⟨nh,ch,_,wh⟩ := fixedScanCounts _ (DemandScan.native (p k)) (DemandScan.work (p k)) head
    refine ⟨?_,?_,?_⟩
    · rw [List.length_append,nh,ih.1,List.length_cons]; ring
    · rw [RAMBuckets.cost_append,ch,ih.2.1,List.length_cons]; ring
    · intro rep hr
      rcases List.mem_append.mp hr with h|h
      · rw [wh _ h]
      · exact ih.2.2 _ h

/-- Catalog coefficient per refreshed position, using the number of tie coordinates as a
uniform upper bound on the dense demand scans per position. -/
def refreshRate (degree dH outDegree ties : ℕ) :=
  12 + 12*degree + 11*dH + 4*(outDegree-(dH+1)) + 3*ties

open PortRefresh PortRefresh.NewSlots Compression.DegreeRefresh PrimedStackRAM in
/-- External descriptors, every dense demand tie, every selected expander supply, and
all three output incidence columns. Motif term selection can intervene between the
prepared demand and supply scans. -/
theorem refreshStateCounts {a g outDegree dH t : ℕ} (X : State a (a + g)) (T : IncidenceDirectory w)
    (q : Fin 8 → Word w) (out lanes : Word w) (ties : Fin t ≃ Tie (2 ^ a))
    {fit : Fintype.card X.Base * 2 ^ a * 2 ^ g * 2 ^ a ≤ 2 ^ w}
    (m m' : Memory w) (prep : List (Report w)) (ready : PrepareRun X T q out ties lanes fit m
      m' prep)
    (supply : Fin 7 → Word w) (selected : Memory w) (sr : List (Report w))
    (hs : runSegment ((template SupplyScan.visit 0).instantiate w supply).program 34 (some 0)
      selected (List.replicate ((Fintype.card X.Base * 2 ^ a * 2 ^ g) * dH) []) = some sr)
    (hd : dH + 1 ≤ outDegree) (pub : Fin outDegree → Public w) (os : List (Report w))
    (ho : AllSlots.Runs (fun k ↦ kindOf ((refreshSlots hd).symm k)) pub
      (Fintype.card X.Base * 2 ^ a * 2 ^ g) (List.finRange outDegree) (after selected
        (eventLog sr)) os) :
    let B := Fintype.card X.Base*2^g
    let all := prep++sr++os
    all.length = X.positions*(2*2^a+1+dH+outDegree) + B*t ∧
      RAMBuckets.cost Report.probes all =
        X.positions*(12+12*2^a+11*dH+4*(outDegree-(dH+1))) + 3*B*t ∧
      RAMBuckets.cost Report.probes all ≤ X.positions*refreshRate (2^a) dH outDegree t ∧
      ∀ rep ∈ all, rep.events.length+1 ≤ 46 := by
  intro B all
  obtain ⟨rg,rd,re,ds,ext,demand,_,eqPrep⟩ := ready
  obtain ⟨hg,hb,he,extCost,_⟩ := ext
  obtain ⟨nd,cd,wd⟩ := demandScanCounts demand
  rw [List.length_finRange] at nd cd
  obtain ⟨ns,cs,_,ws⟩ := fixedScanCounts _ (SupplyScan.visit_native supply)
    (SupplyScan.events_work supply) hs
  obtain ⟨no,co,_,wo⟩ := refreshWrites _ _ ho
  rw [List.length_finRange] at no
  rw [← List.ofFn_id,List.map_ofFn,List.sum_ofFn] at co
  have co' := co.trans (slot_cost hd _)
  have pos : Fintype.card X.Base*2^a*2^g = X.positions := AllSlots.site_count X
  have B_le : B ≤ X.positions := by
    rw [← pos]; dsimp [B]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
  have ng := (run_length hg).trans (List.length_replicate ..)
  have nb := (run_length hb).trans (List.length_replicate ..)
  have ne := (run_length he).trans (List.length_replicate ..)
  have count : RAMBuckets.cost Report.probes all =
      X.positions*(12+12*2^a+11*dH+4*(outDegree-(dH+1))) + 3*B*t := by
    rw [show all = (((rg++rd++re)++ds)++sr)++os from by dsimp only [all]; rw [eqPrep],
      RAMBuckets.cost_append,RAMBuckets.cost_append,RAMBuckets.cost_append,extCost,cd,cs,co']
    dsimp [B]
    rw [← pos]; ring
  refine ⟨?_,count,?_,?_⟩
  · rw [show all = (((rg++rd++re)++ds)++sr)++os from by dsimp only [all]; rw [eqPrep]]
    simp only [List.length_append,ng,nb,ne,nd,ns,no]
    rw [← pos]; dsimp [B]; ring
  · rw [count,refreshRate,Nat.mul_add]
    linarith only [Nat.mul_le_mul_right t (Nat.mul_le_mul_left 3 B_le)]
  · intro rep hr
    rw [show all = (((rg++rd++re)++ds)++sr)++os from by dsimp only [all]; rw [eqPrep]] at hr
    simp only [List.mem_append] at hr
    rcases hr with ((((hh|hh)|hh)|hh)|hh)|hh
    · exact (run_cap hg _ hh).trans (by decide)
    · exact (run_cap hb _ hh).trans (by decide)
    · exact (run_cap he _ hh).trans (by decide)
    · exact (wd _ hh).trans (by decide)
    · rw [ws _ hh]; decide
    · exact wo _ hh

/-- The dimensions used by the selected shrinking workers, on the input state's actual
base enumeration and residual lanes. -/
def shrinkShape {a g : ℕ} (X : State a (packingLaneBits a g)) (subdiv : Fin 4 → ℕ)
    (newDegree : ℕ) : SlotLevel.Shape :=
  ⟨Fintype.card X.Base, 2^(Shrink.J a), 2^g, 2^a, Shrink.colors a, subdiv, newDegree⟩

theorem shrinkShape_positions {a g : ℕ} (X : State a (packingLaneBits a g))
    (subdiv : Fin 4 → ℕ) (degree : ℕ) :
    let s := shrinkShape X subdiv degree
    SlotLevel.sites s*(2^s.colors*s.oldDegree) = X.positions := by
  simp only [shrinkShape, SlotLevel.sites, State.positions, Fintype.card_prod,
    Fintype.card_congr (bitWordFinEquiv (packingLaneBits a g)), Fintype.card_fin,
      packingLaneBits, pow_add,
    Shrink.colors, Shrink.J]
  ring

/-- Number of workers in a dense rank scan depends only on the motif row capacity. -/
def denseRankCap (s : SlotLevel.Shape) :=
  20 + 9*PackingData.pieceCount s.oldDegree s.colors

open PrimedStackRAM in
/-- Physical dense key/rank scans. The two prefix rows partition the old arcs and the
motif-absolute writeback visits all old arcs. AB widths and dense demand pairs visit only
the compact motif rectangle. -/
structure DenseShrinkScans (w : ℕ) (s : SlotLevel.Shape) where
  /-- Seven public operands used by the dense bundle key-gather scan. -/
  keyBank : Fin 7 → Word w
  /-- Six public operands used to rank bundle entries by their gathered keys. -/
  rankBank : Fin 6 → Word w
  /-- Five public operands used to scatter widths into rank order. -/
  widthBank : Fin 5 → Word w
  /-- Seven public operands used to compute absolute motif identifiers. -/
  absBank : Fin 7 → Word w
  /-- Five public operands used to scan prefix widths of the thick-wire entries. -/
  thickBank : Fin 5 → Word w
  /-- Five public operands used to scan prefix widths of the motif entries. -/
  motifBank : Fin 5 → Word w
  /-- Five public operands used to compute the new AB widths. -/
  abBank : Fin 5 → Word w
  /-- Six public operands used to gather the shrinking motif demands. -/
  demandBank : Fin 6 → Word w
  /-- Native key-gather run on every dense bundle entry. -/
  key : NativeScan ((template BundleGather.Fixed.visit 0).instantiate w keyBank).program
    29 (SlotLevel.sites s*s.oldDegree*(2^s.colors*s.oldDegree))
  /-- Native run assigning each dense bundle entry its rank. -/
  rank : NativeScan ((template (PortRankRAM.visit (PackingData.pieceCount s.oldDegree
    s.colors)) 0).instantiate w rankBank).program
    (1+(PortRankRAM.visit (PackingData.pieceCount s.oldDegree s.colors)).length)
    (SlotLevel.sites s*s.oldDegree*(2^s.colors*s.oldDegree))
  /-- Native run scattering each entry's width to its ranked position. -/
  width : NativeScan ((template BundleWidthScatter.visit 0).instantiate w widthBank).program
    19 (SlotLevel.sites s*s.oldDegree*(2^s.colors*s.oldDegree))
  /-- Native run materializing the absolute motif identifiers. -/
  absolute : NativeScan ((template MotifAbsolute.visit 0).instantiate w absBank).program
    25 (SlotLevel.sites s*s.oldDegree*(2^s.colors*s.oldDegree))
  /-- Native prefix scan of the sorted thick-wire widths in each bundle. -/
  thick : NativeScan ((template BundlePrefixRAM.visit 0).instantiate w thickBank).program
    25 (SlotLevel.sites s*s.oldDegree*(2^s.colors*s.oldDegree/4))
  /-- Native prefix scan of the motif widths in each bundle. -/
  motif : NativeScan ((template BundlePrefixRAM.visit 0).instantiate w motifBank).program
    25 (SlotLevel.sites s*s.oldDegree*PackingData.pieceCount s.oldDegree s.colors)
  /-- Native scan computing AB widths for the motif entries. -/
  ab : NativeScan ((template ABWidths.visit 0).instantiate w abBank).program
    30 (SlotLevel.sites s*s.oldDegree*PackingData.pieceCount s.oldDegree s.colors)
  /-- Native scan gathering demand rows for the shrinking motifs. -/
  demand : NativeScan (ShrinkDemandGather.program demandBank) 25
    (SlotLevel.sites s*s.oldDegree*PackingData.pieceCount s.oldDegree s.colors)

/-- The eight dense shrinking scans' reports concatenated in execution order. -/
def DenseShrinkScans.all {s : SlotLevel.Shape} (b : DenseShrinkScans w s) :=
  b.key.reports ++ b.rank.reports ++ b.width.reports ++ b.absolute.reports ++ b.thick.reports ++
    b.motif.reports ++ b.ab.reports ++ b.demand.reports

open private checked_scan from OAI.Computability.VPVNP.CompressorSlotPhaseCosts

/-- Exact physical traffic and call count for the eight dense shrinking passes. -/
theorem denseShrinkCounts (s : SlotLevel.Shape) (hc : 2 ≤ s.colors) (b : DenseShrinkScans w s) :
    let K := 2^s.colors*s.oldDegree
    let Q := PackingData.pieceCount s.oldDegree s.colors
    let B := SlotLevel.sites s*s.oldDegree
    let A := B*K
    b.all.length = 5*A+2*(B*Q) ∧
      RAMBuckets.cost Report.probes b.all = (Q+24)*A + 9*(B*Q) ∧
      ∀ r ∈ b.all, r.events.length+1 ≤ max 30 (denseRankCap s) := by
  intro K Q B A
  have k := fixedScanCounts _ (BundleGather.Fixed.native b.keyBank)
    (BundleGather.Fixed.work b.keyBank) b.key.executed
  have r := checked_scan (ticks := (PortRankRAM.visit Q).length) (probes := Q+4)
    (P := ((PrimedStackRAM.template (PortRankRAM.visit Q) 0).instantiate w b.rankBank).program)
    (fuel := 1+(PortRankRAM.visit Q).length) (fun m i r h ↦ by
      obtain ⟨es,he,_,hp,ht⟩ := PortRankRAM.run_one b.rankBank m i Q
      rw [he] at h; cases h; exact ⟨ht,hp⟩) b.rank.executed
  have v := fixedScanCounts (ticks := 18) (probes := 4) _ (BundleWidthScatter.native b.widthBank)
    (fun _ _ ↦ ⟨rfl,rfl⟩) b.width.executed
  have z := fixedScanCounts (ticks := 24) (probes := 4) _ (MotifAbsolute.native b.absBank)
    (fun _ _ ↦ ⟨rfl,rfl⟩) b.absolute.executed
  have t := fixedScanCounts _ (BundlePrefixRAM.native b.thickBank)
    (fun m i ↦ (BundlePrefixRAM.events_work b.thickBank m i).symm) b.thick.executed
  have u := fixedScanCounts _ (BundlePrefixRAM.native b.motifBank)
    (fun m i ↦ (BundlePrefixRAM.events_work b.motifBank m i).symm) b.motif.executed
  have ab := fixedScanCounts _ (ABWidths.native b.abBank) (ABWidths.work b.abBank) b.ab.executed
  have dm := fixedScanCounts (ticks := 24) (probes := 4)
    (fun m i ↦ (ShrinkDemandGather.visits b.demandBank i m).events)
    (fun m i ↦ ShrinkDemandGather.visit_run b.demandBank i m
      (by decide : ShrinkDemandGather.cost < 25))
    (fun _ _ ↦ ⟨rfl,rfl⟩) b.demand.executed
  have split : B*(K/4)+B*Q = A := by
    rw [← Nat.mul_add, BundleKeys.bundle_row_lengths_add hc]
  refine ⟨?_,?_,?_⟩
  · simp only [DenseShrinkScans.all,List.length_append,k.1,r.1,v.1,z.1,t.1,u.1,ab.1,dm.1]
    change A+A+A+A+B*(K/4)+B*Q+B*Q+B*Q = _
    omega
  · simp only [DenseShrinkScans.all,RAMBuckets.cost_append,k.2.1,r.2.1,v.2.1,z.2.1,
      t.2.1,u.2.1,ab.2.1,dm.2.1]
    change 4*A+(1+(Q+4))*A+5*A+5*A+5*(B*(K/4))+5*(B*Q)+4*(B*Q)+5*(B*Q) = _
    linarith only [congrArg (5*·) split]
  · intro rep hr
    simp only [DenseShrinkScans.all,List.mem_append] at hr
    rcases hr with ((((((hh|hh)|hh)|hh)|hh)|hh)|hh)|hh
    · exact (run_cap b.key.executed _ hh).trans ((by decide : 29 ≤ 30).trans (le_max_left ..))
    · apply le_trans (run_cap b.rank.executed _ hh)
      rw [PortRankRAM.visit_length]; apply le_trans _ (le_max_right ..); dsimp [denseRankCap]; omega
    · exact (run_cap b.width.executed _ hh).trans ((by decide : 19 ≤ 30).trans (le_max_left ..))
    · exact (run_cap b.absolute.executed _ hh).trans ((by decide : 25 ≤ 30).trans (le_max_left ..))
    · exact (run_cap b.thick.executed _ hh).trans ((by decide : 25 ≤ 30).trans (le_max_left ..))
    · exact (run_cap b.motif.executed _ hh).trans ((by decide : 25 ≤ 30).trans (le_max_left ..))
    · exact (run_cap b.ab.executed _ hh).trans (le_max_left ..)
    · exact (run_cap b.demand.executed _ hh).trans ((by decide : 25 ≤ 30).trans (le_max_left ..))

open Greedy Greedy.WalkLayout in
/-- The actual two prepared greedy passes, before the shrinking layout is populated. -/
structure GreedyPrepared (w : ℕ) {a l : ℕ} (X : State a l) where
  /-- Bit length of a displacement tag assigned to a base vertex. -/
  j : ℕ
  tagFits : j ≤ w
  /-- The selected displacement-tag word for each base vertex. -/
  tags : X.Base → BitWord j
  /-- Layout of the greedy color descriptor rows in the base-vertex order. -/
  colorLayout : WalkLayout w (Fintype.card X.Base) (2*2^a)
  /-- Layout of the descriptor rows for the greedy displacement-tag pass. -/
  tagLayout : WalkLayout w (Fintype.card X.Base) (4*tagCount (2^a))
  /-- External memory supplying the operands and descriptors of the prepared color pass. -/
  colorMem : Memory w
  /-- External memory supplying the operands and descriptors of the prepared tag pass. -/
  tagMem : Memory w
  color : colorLayout.PreparedPass (colorOperandRows (2^a)) colorMem 1 (2*2^a)
    (fun v : Fin (2*2^a+1) ↦ Fin.ofNat _ v.val) X.baseIndex (X.slots.base.orderedColor X.baseIndex)
  offset : tagLayout.PreparedPass (tagOperandRows (2^a)) tagMem 4 (tagCount (2^a))
    (tagWord tagFits) X.baseIndex tags

open Greedy Greedy.WalkLayout in
/-- Reports of all four native greedy workers, with the two preparer-to-reader handoffs. -/
def GreedyPrepared.realizes {a l : ℕ} {X : State a l} (G : GreedyPrepared w X)
    (log : List (Report w)) :=
  ∃ pc rc pt rt : List (Report w), log = (pc++rc)++(pt++rt) ∧
    runSegment (Greedy.prepareMachine w (Greedy.colorOperandRows (2^a))).program
      (1+(Greedy.prepareCode (Greedy.colorOperandRows (2^a))).length) (some 0) G.colorMem
      (List.replicate (Fintype.card X.Base) []) = some pc ∧
    runSegment (Greedy.visitMachine w 1 (2*2^a)).program (1+(Greedy.visitCode 1 (2*2^a)).length)
      (some (G.colorLayout.base 0)) (after G.colorMem (eventLog pc))
        (List.replicate (Fintype.card X.Base) []) = some rc ∧
    runSegment (Greedy.prepareMachine w (Greedy.tagOperandRows (2^a))).program
      (1+(Greedy.prepareCode (Greedy.tagOperandRows (2^a))).length) (some 0) G.tagMem
      (List.replicate (Fintype.card X.Base) []) = some pt ∧
    runSegment (Greedy.visitMachine w 4 (tagCount (2^a))).program
      (1+(Greedy.visitCode 4 (tagCount (2^a))).length)
      (some (G.tagLayout.base 0)) (after G.tagMem (eventLog pt))
        (List.replicate (Fintype.card X.Base) []) = some rt

theorem GreedyPrepared.reports {a l : ℕ} {X : State a l} (G : GreedyPrepared w X) :
    ∃ rs, G.realizes rs ∧ rs.length = 4*Fintype.card X.Base ∧
      RAMBuckets.cost Report.probes rs ≤ X.positions*greedyShrinkRate (2^a) ∧
      ∀ r ∈ rs, r.events.length+1 ≤ greedyShrinkCap (2^a) := by
  obtain ⟨pc,rc,pt,rt,hc,hr,ht,hu,n,_,cost,cap⟩ :=
    greedyStateCounts X G.tagFits G.colorLayout G.tagLayout G.colorMem G.tagMem G.tags G.color
      G.offset
  exact ⟨_,⟨pc,rc,pt,rt,rfl,hc,hr,ht,hu⟩,n,cost,cap⟩

/-- Bound for bulk descriptor scans including the fixed global key gather, full-stride
rank worker, scatter, both prefixes, absolute indices, AB widths, and dense demand
pairs. The coefficient is independent of the number of lanes and the base size. -/
def bulkShrinkRate (s : SlotLevel.Shape) :=
  let d := s.oldDegree
  let K := 2^s.colors*d
  let Q := PackingData.pieceCount d s.colors
  let U := 4*d*K*(∑ t, s.subdivisions t)
  14*K + 25*K*d + 18 + 22*U + 16*SlotLevel.pad s + 11*s.newDegree + ((Q+24)*d*K + 9*d*Q)

/-- The largest opcode budget among the bulk and greedy workers. -/
def bulkShrinkCap (s : SlotLevel.Shape) := max (greedyShrinkCap s.oldDegree)
    (max 66 (denseRankCap s))

/-- All bulk shrink descriptors and both greedy scans on the actual incoming state.
The cost equality for the five endpoint passes is returned by `SlotLevel.run_selected`.
The rate counts the global rank scan once, alongside the fixed global key gather. -/
theorem shrinkStateBulkTraffic {a g : ℕ} (X : State a (packingLaneBits a g)) (subdiv : Fin 4 → ℕ)
    (degree : ℕ) (G : GreedyPrepared w X) (heads : SlotLevel.Heads) (m : Memory w)
    (r : SlotLevel.Reports w) :
    let s := shrinkShape X subdiv degree
    ∀ (prep : ShrinkScans w s) (dense : DenseShrinkScans w s), r.Native s heads m →
      ∃ greedy, G.realizes greedy ∧
        let all := greedy ++ (prep.reports ++ r.all) ++ dense.all
        RAMBuckets.cost Report.probes all ≤ X.positions*(greedyShrinkRate (2^a)+bulkShrinkRate s) ∧
        ∀ rep ∈ all, rep.events.length+1 ≤ bulkShrinkCap s := by
  intro s prep dense hn
  have work := slotLevelExactCost hn
  have hc : 2 ≤ s.colors := by
    change 2 ≤ 2*2^a+1
    have := Nat.two_pow_pos a; omega
  have hl : 1 ≤ s.lanes := Nat.two_pow_pos g
  have hpos : 0 < SlotLevel.sites s := by
    change 0 < Fintype.card X.Base*(2^(Shrink.J a)*2^g)
    exact Nat.mul_pos Fintype.card_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  have small : SlotLevel.sites s ≤ X.positions := by
    rw [← shrinkShape_positions X subdiv degree]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  let K := 2^s.colors*s.oldDegree
  let Q := PackingData.pieceCount s.oldDegree s.colors
  obtain ⟨_,cd,capD⟩ := denseShrinkCounts s hc dense
  have boundD : RAMBuckets.cost Report.probes dense.all ≤
    SlotLevel.sites s*((Q+24)*s.oldDegree*K+9*s.oldDegree*Q) := by
    rw [cd]; dsimp [Q,K]; apply le_of_eq; ring
  obtain ⟨cb,capB⟩ := shrinkDescriptorTraffic s heads m r hn hl hpos prep work boundD
  obtain ⟨greedy,hgr,_,cg,capG⟩ := G.reports
  refine ⟨greedy,hgr,?_,?_⟩
  · simp only [RAMBuckets.cost_append]
    have base : RAMBuckets.cost Report.probes (prep.reports++r.all) +
        RAMBuckets.cost Report.probes dense.all ≤ X.positions*bulkShrinkRate s :=
      cb.trans (Nat.mul_le_mul_right _ small)
    rw [RAMBuckets.cost_append] at base
    rw [Nat.mul_add]; omega
  · intro rep hr
    simp only [List.mem_append] at hr
    rcases hr with (hg | (hp | ho)) | hd
    · exact (capG _ hg).trans (le_max_left ..)
    · exact (capB _ (List.mem_append_left _ hp)).trans ((le_max_left ..).trans (le_max_right ..))
    · exact (capB _ (List.mem_append_right _ ho)).trans ((le_max_left ..).trans (le_max_right ..))
    · exact (capD _ hd).trans ((max_le_max_right _ (by decide : 30 ≤ 66)).trans (le_max_right ..))

open private preimage_scan_cost from OAI.Computability.VPVNP.CompressorSlotPhaseCosts

/-- The placement and bundle classifier feed the two bounded append scans. The two
append runs are the ones supplied by `placementPreimages` and `BundleLists.fill_run`. -/
theorem stateInputScanCounts {a l : ℕ} (X : State a l) (p : Fin 14 → Word w)
    (c : Fin 11 → Word w) (p' c' : Fin 6 → Word w) (m n : Memory w)
    (placed classified : List (Report w)) (preimages : NativeScan
      ((PrimedStackRAM.template collectPreimage 3).instantiate w p').program 23 X.positions)
    (bundles : NativeScan ((PrimedStackRAM.template collectPreimage 3).instantiate w c').program
      23 (X.positions * 2 ^ a))
    (hp : ShrinkRAM.ScanResult p X.positions 0 X.positions m placed)
    (hc : BundleRAM.ScanResult c (X.positions * 2 ^ a) 0 (X.positions * 2 ^ a) n classified) :
    let all := placed++preimages.reports++classified++bundles.reports
    all.length = X.positions * (2+2*2^a) ∧
      RAMBuckets.cost Report.probes all = X.positions*(14+14*2^a) ∧
      ∀ r ∈ all, r.events.length+1 ≤ 66 := by
  intro all
  have np := (run_length preimages.executed).trans (List.length_replicate ..)
  have nc := (run_length bundles.executed).trans (List.length_replicate ..)
  have wp := preimage_scan_cost preimages.executed
  have wc := preimage_scan_cost bundles.executed
  have h₁ : RAMBuckets.cost Report.probes placed = 9*X.positions := hp.cost
  have h₂ : RAMBuckets.cost Report.probes classified = 9*(X.positions * 2 ^ a) := hc.cost
  refine ⟨?_,?_,?_⟩
  · simp only [all,List.length_append,hp.calls,np,hc.calls,nc]; ring
  · simp only [all,RAMBuckets.cost_append,h₁,wp,h₂,wc]; ring
  · intro r hr
    simp only [all,List.mem_append] at hr
    rcases hr with ((h|h)|h)|h
    · rw [(hp.work r h).1]; decide
    · exact (run_cap preimages.executed _ h).trans (by decide)
    · rw [(hc.work r h).1]; decide
    · exact (run_cap bundles.executed _ h).trans (by decide)

open scoped Classical in
/-- Indexed input banks for the demand slice of each bundle and the subdivided output of
each role-edge. The widths in the old arrays come from the selected state. -/
structure StateSliceInputs (w : ℕ) {a g : ℕ} (X : State a (packingLaneBits a g))
    (subdiv : Fin 4 → ℕ) where
  /-- The enumeration used to lay out the motif entries of each bundle. -/
  number : X.packingData.BundleNumbering
  /-- The enumeration used to lay out the thick-wire entries of each bundle. -/
  order : X.packingData.ThickNumbering
  /-- Width of each of the four selected roles at each packing motif. -/
  roleWidth : Fin 4 × X.packingData.Motif → ℕ
  /-- The slice-scan operands for intersecting ordered old thick-wire widths with ordered new
  AB widths in each bundle. -/
  demand : ∀ b, SliceInput w (orderedWidths (order b) (fun x ↦ X.packingWidth x.1.1))
    (orderedWidths (number b) (fun x ↦ X.packingData.abWidth number X.packingWidth x.1))
  /-- The slice-scan operands for splitting each selected role width into its prescribed
  subdivisions. -/
  divide : ∀ i, SliceInput w [roleWidth i] (List.ofFn (splitWidth (roleWidth i) (subdiv i.1)))

/-- Per-position charge allowance for AB interval intersections and subdivision of the four
motif role widths. -/
def sliceRate (d c : ℕ) (subdiv : Fin 4 → ℕ) :=
  let Q := PackingData.pieceCount d c
  let H := 2^c*d/4
  let S := ∑ t, subdiv t
  d*(4+7*(H+Q)+16*(H*Q)+4*Q*(4+7*(1+S)+16*S))

/-- The number of physical slice worker rows. Each native slice pass has five phases. -/
def sliceRowsPerSite (d c : ℕ) := 5*d*(1+4*PackingData.pieceCount d c)

/-- Total traffic and row count of all local slice inputs of one actual state. -/
theorem stateSliceTraffic {a g : ℕ} (X : State a (packingLaneBits a g)) (subdiv : Fin 4 → ℕ)
    (input : StateSliceInputs w X subdiv) :
    ∃ (ds : Site X.Base (BitWord (Shrink.J a)) (BitWord g) × Fin (2^a) → SliceSchedule.Passes w)
      (rs : Fin 4 × X.packingData.Motif → SliceSchedule.Passes w),
      (∀ b, (input.demand b).produces (ds b) ∧ ∀ r ∈ (ds b).all, r.events.length+1 ≤ 38) ∧
      (∀ i, (input.divide i).produces (rs i) ∧ ∀ r ∈ (rs i).all, r.events.length+1 ≤ 38) ∧
      ((∑ b, RAMBuckets.cost Report.probes (ds b).all) + (∑ i, RAMBuckets.cost Report.probes
        (rs i).all) ≤
        X.positions * sliceRate (2^a) (Shrink.colors a) subdiv) ∧
      5*Fintype.card (Site X.Base (BitWord (Shrink.J a)) (BitWord g) × Fin (2^a)) +
        5*Fintype.card (Fin 4 × X.packingData.Motif) ≤ X.positions * sliceRowsPerSite (2^a)
          (Shrink.colors a) := by
  classical
  let s := shrinkShape X subdiv 0
  let P := SlotLevel.sites s
  let d := 2^a
  let c := Shrink.colors a
  let Q := PackingData.pieceCount d c
  let S := ∑ t, subdiv t
  let site := SlotSchedule.siteIndex X.baseIndex (bitWordFinEquiv (Shrink.J a)) (bitWordFinEquiv g)
  have hport : Fintype.card (Site X.Base (BitWord (Shrink.J a)) (BitWord g) × Fin d) = P*d := by
    rw [Fintype.card_prod,Fintype.card_congr site,Fintype.card_fin,Fintype.card_fin]; rfl
  have hrole : Fintype.card (Fin 4 × X.packingData.Motif) = 4*(P*d*Q) := by
    rw [Fintype.card_prod,Fintype.card_fin,
      Fintype.card_congr (MotifAbsolute.denseIndex X.packingData site input.number),
        Fintype.card_fin]
    rfl
  have hp : P ≤ X.positions := by
    rw [← shrinkShape_positions X subdiv 0]
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  obtain ⟨ds,hs,capD,_,cd,_⟩ :=
    demandSliceCosts X.packingData input.number input.order X.packingWidth input.demand
  obtain ⟨rs,hr,capR,_,cr,_⟩ := subdivisionSliceCosts input.roleWidth subdiv Prod.fst input.divide
  rw [hport] at cd
  rw [hrole] at cr
  refine ⟨ds,rs,fun b ↦ ⟨hs b,capD b⟩,fun i ↦ ⟨hr i,capR i⟩,?_,?_⟩
  · apply le_trans _ (Nat.mul_le_mul_right (sliceRate d c subdiv) hp)
    change (∑ i, RAMBuckets.cost Report.probes (ds i).all) ≤
      P*d*(4+7*(2^c*d/4+Q)+16*((2^c*d/4)*Q)) at cd
    change (∑ i, RAMBuckets.cost Report.probes (rs i).all) ≤ 4*(P*d*Q)*(4+7*(1+S)+16*(1*S)) at cr
    change _ ≤ P*(d*(4+7*(2^c*d/4+Q)+16*((2^c*d/4)*Q)+4*Q*(4+7*(1+S)+16*S)))
    linarith only [cd,cr]
  · rw [hport,hrole]
    apply le_trans _ (Nat.mul_le_mul_right (sliceRowsPerSite d c) hp)
    change _ ≤ P*(5*d*(1+4*Q)); apply le_of_eq; ring

/-- The coefficient for the shrinking descriptor catalog. The scheduler charges motif
coefficient evaluation and row framing separately. -/
def shrinkRate (s : SlotLevel.Shape) :=
  greedyShrinkRate s.oldDegree + bulkShrinkRate s + sliceRate s.oldDegree s.colors s.subdivisions

/-- End-to-end count of the physical preparation, greedy, slot, dense and slice workers
for one selected shrinking state. The report witnesses are retained for the scheduler. -/
theorem shrinkStateTraffic {a g : ℕ} (X : State a (packingLaneBits a g)) (subdiv : Fin 4 → ℕ)
    (degree : ℕ) (G : GreedyPrepared w X) (heads : SlotLevel.Heads) (m : Memory w)
    (r : SlotLevel.Reports w) (slices : StateSliceInputs w X subdiv) :
    let s := shrinkShape X subdiv degree
    ∀ (prep : ShrinkScans w s) (dense : DenseShrinkScans w s), r.Native s heads m →
      ∃ (greedy : List (Report w))
        (ds : Site X.Base (BitWord (Shrink.J a)) (BitWord g) × Fin (2^a) → SliceSchedule.Passes w)
        (rs : Fin 4 × X.packingData.Motif → SliceSchedule.Passes w),
        G.realizes greedy ∧ (∀ b, (slices.demand b).produces (ds b)) ∧
        (∀ i, (slices.divide i).produces (rs i)) ∧
        let bulk := greedy ++ (prep.reports ++ r.all) ++ dense.all
        RAMBuckets.cost Report.probes bulk + ((∑ b, RAMBuckets.cost Report.probes (ds b).all) +
          (∑ i, RAMBuckets.cost Report.probes (rs i).all)) ≤ X.positions*shrinkRate s ∧
        (∀ rep ∈ bulk, rep.events.length+1 ≤ bulkShrinkCap s) ∧
        (∀ b, ∀ rep ∈ (ds b).all, rep.events.length+1 ≤ 38) ∧
        (∀ i, ∀ rep ∈ (rs i).all, rep.events.length+1 ≤ 38) := by
  intro s prep dense native
  obtain ⟨greedy,run,cb,cap⟩ := shrinkStateBulkTraffic X subdiv degree G heads m r prep dense native
  obtain ⟨ds,rs,hd,hr,cs,_⟩ := stateSliceTraffic X subdiv slices
  refine ⟨greedy,ds,rs,run,fun b ↦ (hd b).1,fun i ↦ (hr i).1,?_,cap,fun b ↦ (hd b).2,fun i ↦
    (hr i).2⟩
  exact (Nat.add_le_add cb cs).trans_eq (Nat.mul_add ..).symm

end CompressorRecords.CatalogRates

end VPVNP
end Computability
end OAI
