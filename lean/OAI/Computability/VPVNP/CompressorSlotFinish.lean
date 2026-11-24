import OAI.Computability.VPVNP.CompressorSlotMateColumns
import OAI.Computability.VPVNP.CompressorSlotWidthState

/-!
# Building the selected shrinking state's incidence directory

One native run produces the sorted endpoint and base tables. The following
three scans invert and lift the base matching, and a final scan gathers the
selected split widths. All six output columns use the exact canonical port
numbers of the next compressor state.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Build

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel SlotOwners SlotSchedule
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Reports for the nine passes that build the endpoint tables, lift the base matching, and
gather the next state's widths. -/
structure Passes (w : ℕ) where
  /-- Reports for the five passes that order endpoint fields and recover the base matching and
  displacements. -/
  slots : Reports w
  /-- Reports for inverting the base matching and writing the two directions of actual port
  incidence. -/
  mates : MateReports w
  /-- Reports that gather the selected split widths for actual outgoing slots, including zero
  widths for dummy slots. -/
  widths : List (Report w)

/-- All slot, mate, and width reports in the order their workers execute. -/
def Passes.all {w : ℕ} (r : Passes w) := r.slots.all++r.mates.all++r.widths

/-- Memory after applying the slot passes, the mate passes, and the final width scan. -/
def Passes.final {w : ℕ} (r : Passes w) (m : Memory w) := after (r.mates.final (r.slots.final m)) (eventLog r.widths)

/-- The three groups of reports arise from native slot, mate, and width executions on
successive memory states. -/
def Passes.Native {w : ℕ} (r : Passes w) (s : Shape) (h : Heads) (splitHead : ℕ) (m : Memory w) :=
  let m₁ := r.slots.final m
  let m₂ := r.mates.final m₁
  r.slots.Native s h m ∧ r.mates.Native s h m₁ ∧
    runSegment ((template SlotWidthScan.visit 0).instantiate w (widthBank s h splitHead w)).program 43 (some 0)
      m₂ (List.replicate (actualCount s) []) = some r.widths

/-- The slot and mate scans reach their prescribed stops and the width scan returns the actual
port count. -/
def Passes.Cursors {w : ℕ} (r : Passes w) (s : Shape) := r.slots.Cursors s ∧ r.mates.Cursors s ∧
  endState (some 0) r.widths = some (Fin.ofNat _ (actualCount s))

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- All nine passes on a prepared shrinking level. The final representation
feeds the ordinary incidence API and retains the source arrays. -/
theorem from_prepared (h : Heads) (splitHead : ℕ) (mem : Memory w) (hdw : 2^b < 2^w) :
    let s := levelShape (b := b) X
    let l := selectedLayout X B sel
    let P := X.packingData
    let tags := bitWordFinEquiv (packingTagBits (2^a))
    let lanes := bitWordFinEquiv g
    let g₀ := bank s h w .genuineOwners
    let d₀ := bank s h w .dummyOwners
    let Y := X.shrinkNext B ready sel
    GenuineTables P s.subdivisions X.baseIndex tags lanes l g₀ mem →
    DummyTables X.baseIndex tags lanes (pad s) d₀ mem →
    SlotWidthScan.SplitRows P s.subdivisions X.baseIndex tags lanes (branchWidth X B sel) splitHead mem →
    h.oldArc+4*(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes) ≤ h.scratch →
    h.role+8 ≤ h.scratch → h.subdivisions+4 ≤ h.scratch → h.nextSite+sites s ≤ h.scratch →
    splitHead+(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes)*4*(∑t,s.subdivisions t) ≤ h.scratch →
    finish s h < 2^w → (∀ u : Word w, u.val < owners s+fields s → mem (h.scratch+fields s+u.val)=0) →
    ∃ r : Passes w, r.Native s h splitHead mem ∧ r.Cursors s ∧ (directory s h w).Represents Y (r.final mem) ∧
      (∀ addr, addr < h.scratch ∨ finish s h ≤ addr → r.final mem addr=mem addr) ∧
      RAMBuckets.cost Report.probes r.all = 6*genuineCount s+3*dummyCount s+5*fields s+
        3*(owners s*2^b)+8*baseArcs s+12*actualCount s := by
  intro s l P tags lanes g₀ d₀ Y hg hp split ho hr hs hn hsplit fit zero
  have h₀ : targetsHead s h+baseArcs s=shiftsHead s h := rfl
  have h₁ : shiftsHead s h+baseArcs s=inverseBaseHead s h := rfl
  have h₂ : inverseBaseHead s h+baseArcs s=outHead s h := rfl
  have h₃ : outHead s h+actualCount s=inHead s h := rfl
  have h₄ : inHead s h+actualCount s=widthHead s h := rfl
  have h₅ : widthHead s h+actualCount s=finish s h := rfl
  have hpre : h.scratch ≤ rowsHead s h := by unfold rowsHead; omega
  have hrect : rowsHead s h+owners s*s.newDegree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have htargets : inverseHead s h+fields s=targetsHead s h := rfl
  have hstop : stopAddress s h=inverseBaseHead s h := rfl
  obtain ⟨slot, sn, sc, tab, forward, sf, costS⟩ := next_run X B ready sel h mem hdw hg hp ho hr hs hn (by change stopAddress s h < 2^w; omega) zero
  let m₁ := slot.final mem
  obtain ⟨nb,na⟩ := next_counts X B ready sel
  change Fintype.card Y.Base*2^b=baseArcs s at nb
  change Fintype.card Y.Base*2^g*2^b=actualCount s at na
  have hlw : 2^g < 2^w := hg.laneCount ▸ (g₀ 0).isLt
  obtain ⟨mate,mn,mc,mates,mf,costM⟩ := writeMates Y s h m₁ forward nb na rfl rfl hdw hlw fit
  let m₂ := mate.final m₁
  have split' := SlotWidthScan.SplitRows.congr_below P s.subdivisions X.baseIndex tags lanes (m' := m₂)
    split hsplit (fun addr haddr ↦ (mf addr (Or.inl (by omega))).trans (sf addr (Or.inl haddr)))
  have oldRows (e) := tab.bySlot e
  obtain ⟨ws,wn,wc,widths,wf,costW⟩ := width_run X B ready sel h splitHead m₂ hp.twoFits hdw hlw
    (hg.subdivCount ▸ (g₀ 1).isLt) (hg.baseCount ▸ (g₀ 2).isLt) hsplit fit split' (fun e ↦ by
      let D := slotDirectory P s.subdivisions X.baseIndex tags lanes l (pad := pad s)
      have hD (v) : Fintype.card {x // D.owner x=v} = s.newDegree :=
        (slotDirectory_degree P s.subdivisions X.baseIndex tags lanes (two_le_packingColors a) l v).trans (Nat.add_sub_of_le ready.degree_budget)
      have he : (sortedFields D s.newDegree hD e).val < owners s*s.newDegree := (sortedFields D s.newDegree hD e).isLt
      exact (mf (rowsHead s h+(sortedFields D s.newDegree hD e).val) (Or.inl (by omega))).trans (oldRows e))
  let r : Passes w := ⟨slot,mate,ws⟩
  change ∀ addr, addr < widthHead s h ∨ finish s h ≤ addr → r.final mem addr=m₂ addr at wf
  have done : Stored s h Y (r.final mem) := by
    constructor
    · intro e; have he := (IncidenceDirectory.baseOrder Y e).isLt
      exact (wf _ (Or.inl (by omega))).trans (mates.forward.mate e)
    · intro e; have he := (IncidenceDirectory.baseOrder Y e).isLt
      exact (wf _ (Or.inl (by omega))).trans (mates.baseIn e)
    · intro e; have he := (IncidenceDirectory.baseOrder Y e).isLt
      exact (wf _ (Or.inl (by omega))).trans (mates.forward.displacement e)
    · intro e; have he := (IncidenceDirectory.actualOrder Y e).isLt
      exact (wf _ (Or.inl (by omega))).trans (mates.actualOut e)
    · intro e; have he := (IncidenceDirectory.actualOrder Y e).isLt
      exact (wf _ (Or.inl (by omega))).trans (mates.actualIn e)
    · exact widths
  refine ⟨r,⟨sn,mn,wn⟩,⟨sc,mc,wc⟩,done.represents nb na fit,?_,?_⟩
  · intro addr ha
    have hsf : addr < h.scratch ∨ stopAddress s h ≤ addr := by omega
    exact (wf addr (by omega)).trans ((mf addr (by omega)).trans (sf addr hsf))
  · change RAMBuckets.cost Report.probes ((slot.all++mate.all)++ws) = _
    change RAMBuckets.cost Report.probes slot.all = 6*genuineCount s+3*dummyCount s+5*fields s+3*(owners s*2^b)+5*baseArcs s at costS
    change RAMBuckets.cost Report.probes ws = 4*actualCount s at costW
    rw [RAMBuckets.cost_append,RAMBuckets.cost_append,costS,costM,costW]; ring

end CompressorRecords.ShrinkSlots.Build

end VPVNP
end Computability
end OAI
