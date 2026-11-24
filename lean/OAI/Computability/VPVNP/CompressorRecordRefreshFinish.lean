import OAI.Computability.VPVNP.CompressorRecordRefreshPrepare
import OAI.Computability.VPVNP.CompressorRecordRefreshExpanderROM
import OAI.Computability.VPVNP.CompressorRecordRefreshSupplyScan
import OAI.Computability.VPVNP.CompressorRecordRefreshIncidence

/-!
# Completing a degree refresh from its selected term records

The selected payloads and repetition headers determine all expander widths. The fixed
expander table then gives their endpoint slots. The actual incidence scans consume those
fields and the retained external bundle directory, and the lane-zero scan recovers the base
slots of the chosen next state. Each stage receives the preceding stage's physical memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Finish

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry NewSlots

variable {bits a a₀ g dH : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (choice : DyadicRefreshChoice X E hdH conn F)
  (q : Fin 8 → W bits) (termBase : W bits) (stride : ℕ) (I : AllSlots.Tables bits)
  (T : IncidenceDirectory bits)

local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd choice
local notation "N" => Fintype.card X.Base * 2^a * 2^g
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "Iₛ" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E hdH conn F choice
local notation "kind" => (fun k : Fin (2^a₀) => kindOf (Equiv.symm (refreshSlots hd) k))
local notation "pub" => (fun k : Fin (2^a₀) => AllSlots.words (2^a) (2^g) I T (Equiv.symm (refreshSlots hd) k))
local notation "supplyPub" => SupplyScan.params (2^a) (2^g) dH termBase stride F.selectorBits I.supply

/-- The two fixed expander output intervals, in the representation used by its ROM pass. -/
def ROMOutside (n addr : ℕ) : Prop :=
  (addr < I.targetPort.val ∨ I.targetPort.val+n ≤ addr) ∧
  (addr < I.reverseSlot.val ∨ I.reverseSlot.val+n ≤ addr)

/-- An address outside the supply, expander, actual incidence and base incidence writes. -/
structure Outside (addr : ℕ) : Prop where
  supply : SupplyScan.Outside supplyPub (N*dH) addr
  rom : ROMOutside I (2^a*dH) addr
  actual : AllSlots.Outside T (N*2^a₀) addr
  base : BaseOutput.Outside T Y addr

/-- The segment and supply input columns survive until consumed, and the seven
segment columns remain accessible for the refresh kernel after all writes. -/
structure Layout : Prop where
  targetBase : I.target = q 2
  totalBase : I.total = q 4
  dims : AllSlots.Fits (a₀ := a₀) X bits
  supplyApart : SupplyScan.Apart supplyPub (N*dH)
  romRegions : ExpanderROM.Regions I (2^a*dH)
  romSupply : ∀ j : W bits, j.val < N*dH → ROMOutside I (2^a*dH) (I.supply+j).val
  incidence : T.Layout Y
  slotReads : AllSlots.InputsApart T kind pub N
  segments : ∀ c : Fin 8, c ≠ 0 → ∀ j : W bits, j.val < N*2^a →
    Outside X E hdH conn F hD hd choice termBase stride I T (q c+j).val

/-- The four stages' individual executions, together with their order in the common
report list. The ROM report is indexed by the fixed outgoing expander edge. -/
def Run (initial : Memory bits) (reports : List (Report bits)) : Prop :=
  ∃ ss es os bs,
    let m₁ := after initial (eventLog ss)
    let m₂ := after m₁ (eventLog es)
    let m₃ := after m₂ (eventLog os)
    reports = ss ++ es ++ (os ++ bs) ∧
    runSegment ((template SupplyScan.visit 0).instantiate bits supplyPub).program 34
      (some 0) initial (List.replicate (N*dH) []) = some ss ∧
    ExpanderROM.runRows E I (some 0) m₁ (List.finRange (2^a*dH)) = some es ∧
    AllSlots.Runs kind pub N (List.finRange (2^a₀)) m₂ os ∧
    runSegment ((template BaseOutput.visit 0).instantiate bits (BaseOutput.params T a₀ g)).program
      29 (some 0) m₃ (List.replicate (BaseOutput.baseCount Y) []) = some bs

private theorem append_memory (m : Memory bits) (x y : List (Report bits)) :
    after m (eventLog (x++y)) = after (after m (eventLog x)) (eventLog y) := by
  change List.foldl BurstRAM.update m ((x++y).flatMap Report.events) = _
  rw [List.flatMap_append,List.foldl_append]; rfl

/-- The supply pass and fixed expander ROM produce exactly the inputs read
by the subsequent slot workers, in their actual shared memory. -/
theorem supply_and_rom (m : Memory bits) (fit : N*2^a ≤ 2^bits) (segments : SegmentFields X q fit m)
    (terms : SupplyScan.TermFields X E hdH conn F choice termBase stride m)
    (layout : Layout X E hdH conn F hD hd choice q termBase stride I T)
    (widthFit : ∀ (s : (X.Base × BitWord g) × Fin (2^a)) (k : Fin dH), Iₛ s.1 (s.2,k) < 2^bits) :
    ∃ ss es,
      let m₁ := after m (eventLog ss)
      let m₂ := after m₁ (eventLog es)
      runSegment ((template SupplyScan.visit 0).instantiate bits supplyPub).program 34
        (some 0) m (List.replicate (N*dH) []) = some ss ∧
      ExpanderROM.runRows E I (some 0) m₁ (List.finRange (2^a*dH)) = some es ∧
      AllSlots.SourceTables X E hdH conn F choice I m₂ ∧
      (∀ addr, Outside X E hdH conn F hD hd choice termBase stride I T addr → m₂ addr = m addr) ∧
      RAMBuckets.cost Report.probes ss = 4*(N*dH) ∧ RAMBuckets.cost Report.probes es = 3*(2^a*dH) := by
  have dims : SupplyScan.Fits (dH := dH) X bits :=
    ⟨layout.dims.ports,layout.dims.lanes,lt_of_lt_of_le (by omega : dH < 2^a₀) layout.dims.degree.le,
      (Nat.mul_le_mul_left _ (by omega : dH ≤ 2^a₀)).trans layout.dims.ids⟩
  obtain ⟨ss,srun,swidth,sframe,scost,_,_⟩ := SupplyScan.supply_pass X E hdH conn F choice
    termBase stride I.supply m terms dims layout.supplyApart widthFit
  let m₁ := after m (eventLog ss)
  let es := (List.finRange (2^a*dH)).map (ExpanderROM.report E I)
  let m₂ := after m₁ (eventLog es)
  obtain ⟨erun,rom,rframe,rcost⟩ := ExpanderROM.initialize_expander E I layout.romRegions m₁
  have preFrame (addr : ℕ) (ho : Outside X E hdH conn F hD hd choice termBase stride I T addr) :
      m₂ addr = m addr := (rframe addr ho.rom.1 ho.rom.2).trans (sframe addr ho.supply)
  have seg₂ : SegmentFields X q fit m₂ :=
    segments.transfer X q (fun c hc j hj => preFrame _ (layout.segments c hc j hj))
  have index (s : (X.Base × BitWord g) × Fin (2^a)) : word (bits := bits) (O s).val = bundleWord O fit s :=
    Fin.ext (Nat.mod_eq_of_lt (bundleWord O fit s).isLt)
  have src : AllSlots.SourceTables X E hdH conn F choice I m₂ := by
    constructor
    · intro b; rw [layout.targetBase,index]; exact seg₂.target b
    · intro b; rw [layout.totalBase,index]; exact seg₂.total b
    · exact rom.targetPort
    · exact rom.reverseSlot
    · intro s k
      let i : W bits := word ((O s).val*dH+k.val)
      have num : (finProdFinEquiv (O s,k)).val = (O s).val*dH+k.val := by change k.val+dH*(O s).val = _; ring
      have hi : i.val < N*dH := (Nat.mod_le ..).trans_lt (num ▸ (finProdFinEquiv (O s,k)).isLt)
      have ho := layout.romSupply i hi
      change (m₂ (I.supply+i).val).val = _
      rw [show m₂ (I.supply+i).val = m₁ (I.supply+i).val from rframe _ ho.1 ho.2]
      exact swidth s k
  exact ⟨ss,es,srun,erun,src,preFrame,scost,rcost⟩

/-- From selected term records and the old segment fields, the post-term phase produces
the six-column incidence directory of the chosen dyadic state. The final memory retains
the segment offsets and preserves every address outside the reserved output columns. -/
theorem finish (m : Memory bits) (fit : N*2^a ≤ 2^bits) (segments : SegmentFields X q fit m)
    (terms : SupplyScan.TermFields X E hdH conn F choice termBase stride m)
    (layout : Layout X E hdH conn F hD hd choice q termBase stride I T)
    (widthFit : ∀ (s : (X.Base × BitWord g) × Fin (2^a)) (k : Fin dH), Iₛ s.1 (s.2,k) < 2^bits) :
    ∃ rs, Run X E hdH conn F hD hd choice termBase stride I T m rs ∧
      T.Represents Y (after m (eventLog rs)) ∧ SegmentFields X q fit (after m (eventLog rs)) ∧
      (∀ addr, Outside X E hdH conn F hD hd choice termBase stride I T addr → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost Report.probes rs =
        4*(N*dH) + 3*(2^a*dH) + ((6+7*dH+4*(2^a₀-(dH+1)))*X.positions + 5*BaseOutput.baseCount Y) := by
  obtain ⟨ss,es,srun,erun,src,preFrame,scost,rcost⟩ :=
    supply_and_rom X E hdH conn F hD hd choice q termBase stride I T m fit segments terms layout widthFit
  let m₁ := after m (eventLog ss)
  let m₂ := after m₁ (eventLog es)
  obtain ⟨os,bs,orun,brun,rep,iframe,icost⟩ :=
    incidence_output X E hdH conn F hD hd choice I T m₂ src layout.dims layout.incidence layout.slotReads
  let rs := ss ++ es ++ (os ++ bs)
  have finalMem : after m (eventLog rs) = after (after m₂ (eventLog os)) (eventLog bs) := by
    simp only [rs,m₂,m₁,append_memory]
  have frame (addr) (ho : Outside X E hdH conn F hD hd choice termBase stride I T addr) :
      after m (eventLog rs) addr = m addr := by
    rw [finalMem]
    exact (iframe addr ho.actual ho.base).trans (preFrame addr ho)
  refine ⟨rs,⟨ss,es,os,bs,rfl,srun,erun,orun,brun⟩,finalMem ▸ rep,
    segments.transfer X q (fun c hc i hi => frame _ (layout.segments c hc i hi)),frame,?_⟩
  change RAMBuckets.cost Report.probes ((ss++es)++(os++bs)) = _
  rw [RAMBuckets.cost_append,RAMBuckets.cost_append,scost,rcost,icost]

end CompressorRecords.PortRefresh.Finish

end VPVNP
end Computability
end OAI
