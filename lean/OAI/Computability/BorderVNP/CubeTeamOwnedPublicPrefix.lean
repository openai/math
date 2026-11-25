import OAI.Computability.BorderVNP.CubeTeamOwnedCheckedWords
import OAI.Computability.BorderVNP.CubeISALocalRowLabelBoot
import OAI.Computability.BorderVNP.CubeISALocalRowBootMinimum

/-! # Public preparation through the actual checked greedy group schedule

The seven consecutive native stages compute the physical label table, its
intervals, powers, declaration, minimum, and team owners. A passing path
produces the actual scalar and declaration words consumed by the subsequent
writers and by the owned-row machine.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Tally
open CubeHeaderInstall TeamContraction.JointHeader

private theorem sequenceWithRun {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {a b : Code} {r : Bank w} {m : Memory w} {ca cb : ℕ} {oa ob : Prop} {P Q : NatState → Prop}
    (first : TestRun pub mac a r m ca oa P)
    (next : ∀ es u mu, Runs pub mac a r m es u mu → P (.ofWords u mu) → TestRun pub mac b u mu cb ob Q) :
    TestRun pub mac (.seq a b) r m (ca+cb) (oa ∧ ob) Q := by
  constructor
  · rintro ⟨p,q⟩
    obtain ⟨es,u,mu,ra,wa,pa⟩ := first.complete p
    obtain ⟨fs,v,mv,rb,wb,pb⟩ := (next es u mu ra pa).complete q
    exact ⟨_,v,mv,ra.seq rb,(by rw [traceCost,VPVNP.RAMBuckets.cost_append]; exact Nat.add_le_add wa wb),pb⟩
  · intro es u mu run
    obtain ⟨v,mv,fs,gs,_,ra,rb⟩ := Runs.seq_iff.mp run
    have ha := first.sound ra
    have hb := (next fs v mv ra ha.2).sound rb
    exact ⟨⟨ha.1,hb.1⟩,hb.2⟩

private theorem joinBlocks {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (a b : List Code) (ha : a ≠ []) (hb : b ≠ []) {r : Bank w} {m : Memory w}
    {ticks : ℕ} {ok : Prop} {P : NatState → Prop}
    (ret : TestRun pub mac (.seq (.block a) (.block b)) r m ticks ok P) :
    TestRun pub mac (.block (a++b)) r m ticks ok P := by
  constructor
  · intro passed
    obtain ⟨es,t,mt,run,cost,p⟩ := ret.complete passed
    exact ⟨es,t,mt,(Runs.block_append_iff ha hb).mpr run,cost,p⟩
  · intro es t mt run
    exact ret.sound ((Runs.block_append_iff ha hb).mp run)

/-- Actual seven-stage prefix of the evaluator's public group scheduler. -/
def groupPrefix (n width : ℕ) : Code := .block [LabelIndex.directoryProgram,NativeIntervals.prepare,
  CubePowers.install,install n width,HeaderDecode.program,CubeLengths.minimum,GroupWeights.checkedSchedule]

/-- The two numerical acceptance conditions of the native checked group assignment. -/
def capacities (wl : GroupWeights.Layout) (tl : TeamNative.Layout) (X : ℕ) (input : ℕ → ℕ) : Prop :=
  let budget : TeamBudget.Layout := ⟨tl.r+1,X,tl.totals⟩
  (∀ j, TeamNative.loads tl.r (wl.weight input) wl.groups j ≤ budget.teamLimit) ∧
    (∑ j ∈ Finset.range wl.groups, wl.weight input j) ≤ budget.totalLimit

/-- Reached RAM after the real label and interval phase determines the entire
scheduler input. All further successful returns have the true checked owner
and declaration arrays. The three success predicates use the actual parsed
fields, least-minimizer convention and load budget. -/
theorem groupPrefix_pinned {w : ℕ} (pub : Arg → Word w) (f : BroadcastFrame)
    (a : CubeArena.Layout) (old : Fin 81 → Word w) (fresh gates outputs width off ell : ℕ)
    (mac : TeamOpcode.Macros w 8) (r : Bank w) (m : Memory w)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (decl : Broadcast a.n a.header.d a.header.cap) :
    let raw := padded (TeamContraction.JointHeader.spelling (G++DeclarationBits.spelling decl) claims) pad
    let physical := geometryInputs fresh G.length gates outputs width w a.header.d a.n a.header.blocks a.b a.h a.s
    let ext := jointFields (a.extension old) fresh G.length gates outputs width off ell
      a.header.d a.n a.header.blocks a.b a.h a.s
    let labelTicks := labelPrefixCost (pub 0).val (readings m)
    BootPins pub f ext raw m → a.header = physical → (pub 0).val+112 ≤ a.header.header →
      f.dst+raw.length ≤ a.header.header → 0 < a.header.d → 0 < a.header.blocks →
      0 < bankWidth a.n a.b a.h a.K a.s → a.stop < 2^w →
      LabelPrefixFits (pub 0).val w (readings m) →
      ∃ tr mid selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) r m tr mid selected ∧
        traceCost tr ≤ labelTicks ∧ BootPins pub f ext raw selected ∧
        ∀ (wl : GroupWeights.Layout) (tl : TeamNative.Layout) (X : ℕ),
        let input := powerHeaderImage a f.dst (readings selected)
        let groupNo := fun g : Fin a.header.d => (TeamNative.owner tl.r (wl.weight input) g.val).val
        let rows := fun p j => readCode (a.header.cap+1) (decl.2 p j)
        readings pub 0 = wl.frame → GroupWeights.CheckedFrame wl tl input w X →
          (∑ k ∈ Finset.range wl.groups, wl.weight input k) < 2^w → wl.groups = a.header.d →
          wl.weights = a.groupWeights → tl.totals = a.teamTotals → tl.owners = a.ownerBase →
          TestRun pub mac (groupPrefix a.n (selectorWidth a.n a.K a.h)) r m
            ((labelTicks+publicBootCost a f.dst)+(minimumCost a.n+
              (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+
                (TeamBudget.setup.slots+(tl.r+1)*(TeamBudget.row.slots+1)+1))))
            (declarationInRange decl ∧ declaredMinimum decl ∧ capacities wl tl X input)
            (fun z => GroupWeights.ScheduleResult wl tl input z.mem ∧
              a.ScannerWords (readings pub 0) f.team (readCode (a.n+1) decl.1) groupNo (readings pub) z.mem rows ∧
              ∀ x < a.header.header, z.mem x = readings m x) := by
  intro raw physical ext labelTicks pins phys primary copied alphabet blocks stride high fitted
  obtain ⟨es,t,mt,label,cost,belowLabel,atLabel,first⟩ := labelBoot_pinned pub f a old fresh gates outputs width off ell
    mac r m G claims pad decl pins phys primary copied alphabet blocks stride high fitted
  refine ⟨es,t,mt,label,cost,atLabel,?_⟩
  intro wl tl X input groupNo rows base frame sumFit groups weights totals owners
  let firstFive := [LabelIndex.directoryProgram,NativeIntervals.prepare,CubePowers.install,
    install a.n (selectorWidth a.n a.K a.h),HeaderDecode.program]
  let finalTwo := [CubeLengths.minimum,GroupWeights.checkedSchedule]
  have axes : a.header.a = a.n+1 := by rw [phys]; rfl
  have labelsFit : a.alphabet < 2^w := by
    have ch := LocalRow.arenaExtents a
    have above : a.alphabet ≤ a.packetEnd := by
      have low : a.header.d ≤ a.header.d*a.header.d := Nat.le_mul_of_pos_right _ alphabet
      have cells := Nat.pow_le_pow_left low (a.n+1)
      have raw : (a.header.d*a.header.d)^(a.n+1) ≤ (a.header.d*a.header.d)^(a.n+1)*2*a.header.blocks*
          bankWidth a.n a.b a.h a.K a.s := by
        calc _ ≤ _*2 := by omega
             _ ≤ _*a.header.blocks := Nat.le_mul_of_pos_right _ blocks
             _ ≤ _*bankWidth a.n a.b a.h a.K a.s := Nat.le_mul_of_pos_right _ stride
      exact cells.trans (raw.trans (Nat.le_add_left _ _))
    have en : a.packetEnd+8+a.h ≤ a.powerBase := ch.2.1
    omega
  change TestRun pub mac (.block (firstFive++finalTwo)) r m _ _ _
  apply joinBlocks firstFive finalTwo (by simp [firstFive]) (by simp [finalTwo])
  apply first.seq
  intro bootRegs bootMem decoded
  have guard := DecodedRows.minimum_run pub mac a f.dst decl (readings mt) bootRegs bootMem decoded axes primary high
  apply sequenceWithRun guard
  intro fs minRegs minMem minimum kept
  have image : readings minMem = input := kept.1.trans decoded.1
  have actual := a.checkedScanner_test pub f old fresh G.length gates outputs width off ell atLabel decl
    decoded minimum wl tl X base (image ▸ frame) (image ▸ sumFit) groups weights totals owners axes
    primary alphabet high labelsFit
  have classified := actual
  rw [image] at classified
  apply classified.mono le_rfl Iff.rfl
  rintro z ⟨schedule,words⟩
  refine ⟨schedule,words,?_⟩
  intro x hx
  have hb := header_le_publicBase a
  have hp := a.source_order.1
  have wg : a.powerBase ≤ a.groupWeights := Nat.le_add_right _ _
  have tt : a.groupWeights ≤ a.teamTotals := Nat.le_add_right _ _
  have ow : a.teamTotals ≤ a.ownerBase := Nat.le_add_right _ _
  have final := schedule.other x (fun j _ => by rw [weights]; omega)
    (fun j => by rw [totals]; omega) (fun j _ => by rw [owners]; omega)
  rw [final]
  change headerImage a.header a.n _ _ (CubePowers.image a.header.d a.powerBase (a.n+1) (readings mt)) x = _
  rw [headerImage_outside _ _ _ _ _ _ (.inl hx)]
  have skip : ¬ a.powerBase ≤ x := by omega
  simp only [CubePowers.image,skip,false_and,ite_false]
  exact belowLabel x (hx.trans_le hb)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
