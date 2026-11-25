import OAI.Computability.BorderVNP.CubeTeamOwnedGroupImage
import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalCapacity
import OAI.Computability.BorderVNP.CubeISALocalRowGroupPrefix

/-! # The honest public group prefix at the rounded physical epoch parameters -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open VPVNP.BurstRAM Crossing Physical MeanChoice LabelIndex TeamScales Filter
open RoutingISA RoutingISA.LocalRow RoutingISA.CubeHeaderInstall TeamContraction.JointHeader Tally

universe u v t

/-- The actual canonical seven-stage preparation returns at every sufficiently
large epoch. Its selected memory is reached by real label and cable-interval
code. Its final memory contains the physical chosen coordinate, all true
subtotals, and the actual greedy owners computed from the populated deliveries. -/
theorem PacketFormat.eventually_canonical_groupPrefix {F : Type u} [Field F] {n : ℕ} {η α ξ : ℝ}
    (p : PacketFormat F n η) (hη : 0 < η) (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (hα : 0 < α) (hξ : ξ < α/3) (hgap : 8*α*(n+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ {netDim : ℕ} {P : Type v} {bits : P → ℕ} {Cell : Type}
      [Fintype Cell] [DecidableEq Cell] {A : Type t} [Fintype A] (r R w d blocks : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
      (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs slotWidth off ell : ℕ)
      (G : List Bool) (claims : List (List Bool)) (pad cells cables maxRows cellStride : ℕ)
      (select : Packet n d blocks → Selector n p.K p.h) (reg : Bank w)
      (producer : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (before : Memory w) (dest : ℕ)
      (N : Network netDim P bits) (cell : N.Site → Cell) (recv : A → Cell) (size : A → ℕ) (M : ℕ),
      let X := exterior ξ r k
      let frame := (pub 0).val
      let stat := geometryInputs fresh G.length gates outputs slotWidth w d n blocks p.b p.h p.s
      let a : CubeArena.Layout := ⟨stat,n,p.b,p.h,p.K,p.s,cells,cables,maxRows,R+1,cellStride⟩
      let m := Packing.Directory.ISA.publish before frame dest (producer.directory pp lp)
      let dir := LabelIndex.layout frame (readings m)
      let decl := broadcast p.b p.s select
      let raw := TeamContraction.JointHeader.padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
      let ext := jointFields (a.extension old) fresh G.length gates outputs slotWidth off ell d n blocks p.b p.h p.s
      let i := chosen p.b p.s select
      let wl := weightLayout a frame i.val
      let tl := teamLayout a R
      let clock := (labelPrefixCost frame (readings m)+publicBootCost a f.dst) +
        (minimumCost n+(ticks wl+TeamNative.assignmentTicks tl+(TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1)))
      ∀ (fit : LabelPrefixFits frame w (readings m)) (cellNum : Cell ≃ Fin dir.cells)
        (edgeOrd : N.CrossingEdge cell ↪ Fin dir.cableCount) (dataOrd : A ↪ Fin dir.deliveryCount),
        RowPlacement (networkRows N cell recv size) (fromTables dir (readings m) fit.endpoints) cellNum
          (edgeOrd.sumMap dataOrd) → PackedLabelBudget N cell recv size ((X*(R+1) : ℕ) : ℝ) M (d^(n+1)) →
        producer.teams = R+1 → producer.processors = r → producer.literal = literal α k →
        0 < producer.fields → 0 < producer.block → producer.fields ≤ 2 →
        producer.entries*producer.description ≤ producer.teams*producer.processors*(producer.literal/2) →
        dir.deliveries = dest → dir.deliveryCount = (producer.directory pp lp).length → frame+9 < dest →
        (∀ j : Fin (producer.directory pp lp).length, ∀ t ∈ (producer.directory pp lp)[j.val].words, t < 2^w) →
        1 ≤ r → (R+1 : ℝ) ≤ (k : ℝ)^(2*α) → d = alphabet α k →
        blocks = blocksFor (X*(R+1) : ℕ) (p.h*p.b) (d^(n+1)) →
        BootPins pub f ext raw m → frame+112 ≤ stat.header → f.dst+raw.length ≤ stat.header →
        0 < d → 0 < blocks → 0 < bankWidth n p.b p.h p.K p.s → a.stop < 2^w →
        readings m (frame+11) = cells → f.teams = R+1 → (old 0).val = X →
        1000000 < 2^w → 1000000*X*(R+1) < 2^w →
        ∃ es mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg m es mid selected ∧
          traceCost es ≤ labelPrefixCost frame (readings m) ∧
          let input := powerHeaderImage a f.dst (readings selected)
          let groupNo := fun g : Fin d => (TeamNative.owner R (wl.weight input) g.val).val
          (∑ j ∈ Finset.range d, wl.weight input j) < 2^w ∧ capacities wl tl X input ∧
          BoundedRun pub mac (groupPrefix n (selectorWidth n p.K p.h)) reg m clock (fun z =>
            ScheduleResult wl tl input z.mem ∧ a.ScannerWords frame f.team i.val groupNo (readings pub) z.mem
              (subtotals itemRow (crossCount p.b p.s select) i) ∧ ∀ x < stat.header, z.mem x = readings m x) := by
  filter_upwards [p.eventually_directory_capacity hη fixed hα hξ hgap] with k caps
  intro netDim P bits Cell _ _ A _ r R w d blocks pub mac f old fresh gates outputs slotWidth off ell G claims pad cells cables maxRows
    cellStride select reg producer pp lp before dest N cell recv size M X frame stat a m dir decl raw ext i wl tl
    clock fit cellNum edgeOrd dataOrd place labelBudget teams proc lit fields block f2 tails pd count floor fitted
    hr hR groups bCount pins primary extent positive bpos stride high cellCount processors budget million scaled
  have valid := broadcast_passes_minimum p.b p.s select
  have ix : readCode (n+1) decl.1 = i.val := by simp [decl,i,broadcast,readCode,writeCode]
  let D : LengthDeclaration n d := (i,fun u j => readCode _ (decl.2 u j))
  have passes : passesLengths p.b p.s select D := by
    apply (passesLengths_iff ..).mpr
    simp [D,decl,i,broadcast,readCode,writeCode]
  obtain ⟨es,mid,selected,ran,ticks,here,low,next⟩ := groupPrefix_of_arena pub f a old fresh gates outputs
    slotWidth off ell mac reg m G claims pad decl R X pins rfl primary extent positive bpos stride high fit
    cellCount processors rfl budget million scaled
  refine ⟨es,mid,selected,ran,ticks,?_⟩
  intro input groupNo
  have check := publicBoot_pinned a old fresh gates outputs slotWidth off ell mac mid G claims pad decl here
    rfl primary extent positive bpos stride high
  obtain ⟨_,bootReg,bootMem,_,_,decoded⟩ := check.complete valid.1
  have mem : readings bootMem = input := decoded.1
  have labelFit : a.alphabet < 2^w := by
    have hd : d ≤ d*d := Nat.le_mul_of_pos_right _ positive
    have growth := Nat.pow_le_pow_left hd (n+1)
    have enough : (d*d)^(n+1) ≤ (d*d)^(n+1)*2*blocks*bankWidth n p.b p.h p.K p.s := by
      calc _ ≤ _*2 := by omega
           _ ≤ _*blocks := Nat.le_mul_of_pos_right _ bpos
           _ ≤ _*bankWidth n p.b p.h p.K p.s := Nat.le_mul_of_pos_right _ stride
    have pk : d^(n+1) ≤ a.packetEnd := growth.trans (enough.trans (Nat.le_add_left ..))
    have b := arenaExtents a
    have si : a.packetEnd+8+a.h ≤ a.powerBase := b.2.1
    change d^(n+1) < 2^w
    omega
  have data := groupImage_pinned pub mac f a old fresh G.length gates outputs slotWidth off ell reg m pins ran fit high
    labelFit cellCount positive i decl (.ofWords bootReg bootMem) decoded
  have preEq : readings (Packing.Directory.ISA.publish before frame dir.deliveries (producer.directory pp lp)) = readings m := by
    rw [pd]
  have selectedCount : readings selected (frame+11) = cells := by
    have base : stat.header ≤ a.publicBase := header_le_publicBase a
    exact (low _ (by omega)).trans cellCount
  have mkFrame (mass : (∑ j ∈ Finset.range wl.groups, wl.weight (readings bootMem) j) < 2^w) :
      CheckedFrame wl tl (readings bootMem) w X := by
    have h := checkedFrame_of_pins pub f a old fresh gates outputs slotWidth off ell mac mid selected G claims pad decl
      R X here rfl primary extent selectedCount processors rfl budget positive bpos stride high million scaled valid.1
    rw [mem] at mass ⊢
    rw [ix] at h
    exact h mass
  have general := @caps netDim P bits Cell _ _ A _ r w wl tl blocks dir producer pp lp frame before N cell recv size cellNum edgeOrd dataOrd M D select
    pub mac bootReg bootMem
  dsimp only at general
  rw [preEq] at general
  have budgetRoom := budgetFits_of_arena a w frame R X rfl primary high million scaled
  have calcCap := general fit.endpoints cellCount.symm positive place labelBudget teams proc lit fields block f2 tails count
    (pd ▸ floor) fitted hr hR groups bCount passes (mem ▸ data) rfl budgetRoom mkFrame
  rw [mem] at calcCap
  refine ⟨calcCap.1,calcCap.2,?_⟩
  have execute := next (fun _ => by rw [ix]; exact calcCap.1)
  rw [ix] at execute
  apply (execute.complete ⟨valid.1,valid.2,calcCap.2⟩).mono le_rfl
  rintro z ⟨scheduled,words,rest⟩
  refine ⟨scheduled,?_,rest⟩
  have wraw : a.ScannerWords frame f.team (readCode (n+1) decl.1) groupNo (readings pub) z.mem
      (fun u j => readCode (a.header.cap+1) (decl.2 u j)) := ix ▸ words
  exact CubeArena.Layout.ScannerWords.of_canonicalBroadcast a select decl rfl rfl wraw

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
