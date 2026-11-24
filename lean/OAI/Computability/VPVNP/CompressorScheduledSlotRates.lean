import OAI.Computability.VPVNP.CompressorCatalogRates
import OAI.Computability.VPVNP.CompressorSlotBuild
import OAI.Computability.VPVNP.CompressorRecordsCopyIncidence

/-!
# Charged work of the complete shrinking slot program

The seven preparation segments, nine slot and incidence segments, and six
canonical copy segments form the 22 visits of the fixed slot plan.
The copy also applies to the output of a port refresh.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledRates

open Compression BurstRAM PhaseCosts SlotLevel ShrinkSlots

variable {w : ℕ}

open private full_count from OAI.Computability.VPVNP.CompressorRecordsCopyIncidence

/-- Six canonical transfer passes for any selected output state. The first three
columns have one cell per base port and the remaining three one per actual port. -/
theorem copyColumns {a l : ℕ} (X : State a l) (T U : IncidenceDirectory w) (m : Memory w) :
    let rs := CopyIncidence.reports X T U CopyIncidence.allColumns m
    CopyIncidence.Runs X T U CopyIncidence.allColumns m rs ∧
      rs.length = 3*(Fintype.card X.Base*2^a)+3*(X.positions*2^a) ∧
      RAMBuckets.cost Report.probes rs = 9*(Fintype.card X.Base*2^a)+9*(X.positions*2^a) ∧
      RAMBuckets.cost Report.probes rs ≤ X.positions*(18*2^a) ∧
      ∀ r ∈ rs, r.events.length+1 = 12 := by
  intro rs
  obtain ⟨n,c,h⟩ := CopyIncidence.reports_work X T U CopyIncidence.allColumns m
  have eqn : (CopyIncidence.allColumns.map (CopyIncidence.rows X)).sum =
      3*(Fintype.card X.Base*2^a)+3*(X.positions*2^a) := full_count X
  have b : Fintype.card X.Base*2^a ≤ X.positions*2^a := CopyIncidence.rows_le_slots X 0
  rw [eqn] at n c
  refine ⟨CopyIncidence.reports_run ..,n,c.trans (by ring),?_,fun r hr ↦ congrArg (·+1) (h r hr).1⟩
  exact c.le.trans (by linarith only [b])

private theorem outputResources {s : Shape} {h : Heads} {m : Memory w} {split : ℕ}
    {r : Build.Passes w}
    (native : r.Native s h split m) :
    RAMBuckets.cost Report.probes (r.mates.all++r.widths) = 3*baseArcs s+12*actualCount s ∧
    ∀ rep ∈ r.mates.all++r.widths, rep.events.length+1 ≤ 43 := by
  obtain ⟨_,⟨inv,out,inc⟩,widths⟩ := native
  let ip := inverseBank s h w
  have ib := fixedScanCounts (probes := 2) (ticks := 9)
    (fun mem x ↦ SlotScatter.events ip x (mem (ip 0+x).val)) (SlotScatter.visit_native ip)
    (fun _ _ ↦ ⟨rfl,rfl⟩) inv
  have ob := fixedScanCounts _ (SlotIncidencePass.native _ false)
    (fun mem x ↦ SlotIncidencePass.events_work _ false mem x) out
  have rb := fixedScanCounts _ (SlotIncidencePass.native _ true)
    (fun mem x ↦ SlotIncidencePass.events_work _ true mem x) inc
  have wb := fixedScanCounts _ (SlotWidthScan.native _)
    (fun mem x ↦ SlotWidthScan.events_work _ mem x) widths
  refine ⟨?_,?_⟩
  · simp only [MateReports.all,RAMBuckets.cost_append,ib.2.1,ob.2.1,rb.2.1,wb.2.1]; ring
  · intro rep hr
    simp only [MateReports.all,List.mem_append] at hr
    rcases hr with ((hx|hx)|hx)|hx
    · exact (run_cap inv _ hx).trans (by decide)
    · exact (run_cap out _ hx).trans (by decide)
    · exact (run_cap inc _ hx).trans (by decide)
    · exact run_cap widths _ hx

/-- Coefficient per packed site, including the temporary owner holes, zeroed
counters, lane-lifted incidence columns and the six transfers. -/
def slotRate (s : Shape) :=
  let U := 4*s.oldDegree*(2^s.colors*s.oldDegree)*(∑ t, s.subdivisions t)
  30+26*U+20*pad s+44*s.newDegree

/-- The 22 physical passes with their native reports. The two count equalities
are supplied by `ShrinkSlots.next_counts` for the actual selected output. -/
theorem slotProgram {a l : ℕ} (Y : State a l) (s : Shape) (h : Heads) (split : ℕ)
    (U : IncidenceDirectory w) (layout : Bool) (m : Memory w) (r : Build.Construction w)
    (native : r.Native s h split layout m) (lanes : 1 ≤ s.lanes) (positive : 0 < sites s)
    (base : Fintype.card Y.Base * 2 ^ a = baseArcs s)
      (actual : Y.positions * 2 ^ a = actualCount s) :
    let cp := CopyIncidence.reports Y (directory s h w) U CopyIncidence.allColumns (r.final m)
    let all := r.all++cp
    CopyIncidence.Runs Y (directory s h w) U CopyIncidence.allColumns (r.final m) cp ∧
      RAMBuckets.cost Report.probes all =
        24+2*sites s+2*(owners s+fields s)+6*genuineCount s+3*dummyCount s+5*fields s+
          3*(owners s*s.newDegree)+17*baseArcs s+21*actualCount s ∧
      RAMBuckets.cost Report.probes all ≤ sites s*slotRate s ∧
      ∀ rep ∈ all, rep.events.length+1 ≤ 49 := by
  intro cp all
  obtain ⟨prep,pass⟩ := native
  obtain ⟨_,wp,_,capP⟩ := ShrinkSlots.Preparation.Reports.Native.resources prep
  have ws := slotLevelExactCost pass.1
  obtain ⟨_,bs,capS,_⟩ := slotLevelBounds s h _ r.passes.slots pass.1 lanes ws
  obtain ⟨wo,capO⟩ := outputResources pass
  obtain ⟨copy,_,wc,_,capC⟩ := copyColumns Y (directory s h w) U (r.final m)
  rw [base,actual] at wc
  have wt : RAMBuckets.cost Report.probes all =
      RAMBuckets.cost Report.probes r.prepare.all + RAMBuckets.cost Report.probes
        r.passes.slots.all +
      RAMBuckets.cost Report.probes (r.passes.mates.all++r.passes.widths) +
        RAMBuckets.cost Report.probes cp := by
    simp only [all,Build.Construction.all,Build.Passes.all,RAMBuckets.cost_append]; ring
  have base_le : baseArcs s ≤ actualCount s := by
    change s.bases*s.tags*s.newDegree ≤ s.bases*(s.tags*s.lanes)*s.newDegree
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ lanes)
  let K := 4*s.oldDegree*(2^s.colors*s.oldDegree)*(∑ t,s.subdivisions t)
  have hg : genuineCount s = sites s*(2*K) := by dsimp [genuineCount,sites,Slots.keyCount,K]; ring
  have hd : dummyCount s = sites s*(2*pad s) := by dsimp [dummyCount,sites]; ring
  have hf : fields s = sites s*(2*(K+pad s)) := by rw [← counts_add,hg,hd]; ring
  have ho : owners s = 2*sites s := Nat.mul_comm ..
  refine ⟨copy,?_,?_,?_⟩
  · rw [wt,wp,ws,wo,wc]; ring
  · rw [wt,wp,wo,wc,ho,hf]
    change _ ≤ sites s*(30+26*K+20*pad s+44*s.newDegree)
    change _ ≤ sites s*s.newDegree at base_le
    change _ ≤ sites s*(22*K+16*pad s+11*s.newDegree) at bs
    change _ + (3*baseArcs s+12*(sites s*s.newDegree)) + (9*baseArcs s+9*(sites s*s.newDegree)) ≤ _
    linarith only [bs,base_le,positive]
  · intro rep hr
    simp only [all,Build.Construction.all,Build.Passes.all,List.mem_append] at hr
    rcases hr with (hp|((hs|hm)|hw))|hc
    · exact (capP _ hp).trans (by decide)
    · exact capS _ hs
    · exact (capO _ (List.mem_append_left _ hm)).trans (by decide)
    · exact (capO _ (List.mem_append_right _ hw)).trans (by decide)
    · rw [capC _ hc]; decide

open Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion

/-- The 22 visits on the selected dyadic branch, including the transfer of its actual
width column into the next level. The incoming position count pays for the whole run. -/
theorem selectedSlotProgram {a b g : ℕ} {δ factor : ℝ} {k : Type*} [_root_.Field k]
    (X : State a (packingLaneBits a g))
    (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass)
      (realWidths supplyMass) (31 / 16) factor)
    (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (sel : X.ShrinkSelection B)
    (h : Heads) (split : ℕ) (U : IncidenceDirectory w) (m : Memory w) (r : Build.Construction w) :
    let s := levelShape (b := b) X
    let Y := X.shrinkNext B ready sel
    let cp := CopyIncidence.reports Y (directory s h w) U CopyIncidence.allColumns (r.final m)
    let all := r.all++cp
    r.Native s h split (selectedLayout X B sel) m →
      CopyIncidence.Runs Y (directory s h w) U CopyIncidence.allColumns (r.final m) cp ∧
        RAMBuckets.cost Report.probes all ≤ X.positions*slotRate s ∧
        ∀ rep ∈ all, rep.events.length+1 ≤ 49 := by
  intro s Y cp all native
  obtain ⟨hb,ha⟩ := ShrinkSlots.next_counts X B ready sel
  have ha' : Y.positions*2^b = actualCount s := by
    simpa only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv g),
      Fintype.card_fin]
      using ha
  have hl : 1 ≤ s.lanes := Nat.two_pow_pos g
  have hp : 0 < sites s := Nat.mul_pos Fintype.card_pos (Nat.mul_pos (Nat.two_pow_pos _)
    (Nat.two_pow_pos _))
  have eqn := CatalogRates.shrinkShape_positions X s.subdivisions (2^b)
  change sites s*(2^s.colors*s.oldDegree) = X.positions at eqn
  have le : sites s ≤ X.positions := (Nat.le_mul_of_pos_right _
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))).trans_eq eqn
  obtain ⟨rc,_,c,hc⟩ := slotProgram Y s h split U _ m r native hl hp hb ha'
  exact ⟨rc,c.trans (Nat.mul_le_mul_right _ le),hc⟩

end CompressorRecords.ScheduledRates

end VPVNP
end Computability
end OAI
