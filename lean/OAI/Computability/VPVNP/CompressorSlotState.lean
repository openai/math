import OAI.Computability.VPVNP.CompressorSlotLevelRun
import OAI.Computability.VPVNP.ShrinkStatePass
import OAI.Computability.VPVNP.CompressorRecordIncidenceLayout
import OAI.Computability.VPVNP.BitSlotXor

/-!
# Passing the sorted shrinking graph to the next compressor state

The graph used by `State.shrinkNext` uses the same current base index, binary
tag index, subdivisions and common layout as the native slot builder. Its
base-arc numbers are exactly the ordinary port numbers in the shared
incidence directory. A scatter of the forward base table constructs the
inverse at the same numerical indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel SlotOwners SlotSchedule
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Slot directory dimensions for this shrink, using the current base vertices and residual
lanes and the subdivisions chosen for the outgoing degree. -/
noncomputable abbrev levelShape : Shape :=
  ⟨Fintype.card X.Base,2^(packingTagBits (2^a)),2^g,2^a,2*2^a+1,subdivisions (2^a) (2*2^a+1) (2^b),2^b⟩

/-- The layout with lower group energy for the selected term's widths, choosing the false
layout on a tie. -/
noncomputable abbrev selectedLayout :=
  chosenLayout (equalArcMass (Position X.Base (BitWord a) (BitWord (packingTagBits (2^a))) (BitWord g) (2*2^a+1)) (2^a))
    (fun e ↦ (relativeMass e : ℝ)) (X.packingData.termWidths B X.shrinkNumber X.packingWidth sel)

/-- Base columns shared by the following level in the canonical port order. -/
structure BaseForward {a l : ℕ} (Y : State a l) (target shift : ℕ) (mem : Memory w) : Prop where
  mate : ∀ e, mem (target+(IncidenceDirectory.baseOrder Y e).val) = Fin.ofNat _ (IncidenceDirectory.baseOrder Y (Y.slots.base.target e)).val
  displacement : ∀ e, mem (shift+(IncidenceDirectory.baseOrder Y e).val) = Fin.ofNat _ (bitWordFinEquiv l (Y.slots.displacement e)).val

/-- The kernel's actual branch and the native builder have identical topology. -/
theorem next_baseMatching (targets shifts : ℕ) (m : Memory w) :
    let l := selectedLayout X B sel
    let tags := bitWordFinEquiv (packingTagBits (2^a))
    let I := X.shrinkStateIndex ready l
    BaseMatching X.baseIndex tags (bitWordFinEquiv g) I.graph targets shifts m →
      BaseForward (X.shrinkNext B ready sel) targets shifts m := by
  intro l tags I h
  let Y := X.shrinkNext B ready sel
  have idx (e : Y.Base × Fin (2^b)) : (IncidenceDirectory.baseOrder Y e).val =
      (SlotSchedule.baseIndex X.baseIndex tags e).val := rfl
  constructor
  · intro e
    rw [idx,idx]
    exact Fin.ext ((h.targetAt e).trans (Nat.mod_eq_of_lt ((h.targetAt e) ▸ (m _).isLt)).symm)
  · intro e
    rw [idx]
    exact Fin.ext ((h.shiftAt e).trans (Nat.mod_eq_of_lt ((h.shiftAt e) ▸ (m _).isLt)).symm)

/-- Native slot construction directly on the same selected state as the
compression kernel, using the canonical next-level port addresses. -/
theorem next_run (h : Heads) (mem : Memory w) (hdw : 2^b < 2^w) :
    let s := levelShape (b := b) X
    let l := selectedLayout X B sel
    let p := X.packingData
    let tags := bitWordFinEquiv (packingTagBits (2^a))
    let lanes := bitWordFinEquiv g
    let g₀ := bank s h w .genuineOwners
    let d₀ := bank s h w .dummyOwners
    let D := slotDirectory p s.subdivisions X.baseIndex tags lanes l (pad := pad s)
    let hD := fun owner ↦ (slotDirectory_degree p s.subdivisions X.baseIndex tags lanes (two_le_packingColors a) l owner).trans
      (Nat.add_sub_of_le ready.degree_budget)
    GenuineTables p s.subdivisions X.baseIndex tags lanes l g₀ mem →
    DummyTables X.baseIndex tags lanes (pad s) d₀ mem →
    h.oldArc+4*(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes) ≤ h.scratch →
    h.role+8 ≤ h.scratch → h.subdivisions+4 ≤ h.scratch → h.nextSite+sites s ≤ h.scratch → stopAddress s h < 2^w →
    (∀ u : Word w, u.val < owners s+fields s → mem (h.scratch+fields s+u.val)=0) →
    ∃ r : Reports w, r.Native s h mem ∧ r.Cursors s ∧
      Tables D (2^b) (rowsHead s h) (inverseHead s h) hD (r.final mem) ∧
      BaseForward (X.shrinkNext B ready sel) (targetsHead s h) (shiftsHead s h) (r.final mem) ∧
      (∀ addr, addr < h.scratch ∨ stopAddress s h ≤ addr → r.final mem addr = mem addr) ∧
      RAMBuckets.cost Report.probes r.all =
        6*genuineCount s+3*dummyCount s+5*fields s+3*(owners s*2^b)+5*baseArcs s := by
  intro s l p tags lanes g₀ d₀ D hD hg hp ho hr hs hn fit hz
  have hJ : 1 < 2^packingTagBits (2^a) := Nat.one_lt_two_pow (Nat.succ_pos _).ne'
  have hlane : (lanes 0).val = 0 := by simpa using bitWordFinEquiv_add_val (0 : BitWord g) 0
  obtain ⟨r,hNative,hCursors,tab,hBase,hFrame,hCost,_⟩ := SlotLevel.run_selected p s.subdivisions X.baseIndex tags lanes l h
    (two_le_packingColors a) (orderedDyadicPacking_validTags X.slots X.baseIndex) ready.degree_budget hJ hlane
    (Nat.two_pow_pos b) hdw mem hg hp ho hr hs hn fit hz
  exact ⟨r,hNative,hCursors,tab,next_baseMatching X B ready sel _ _ _ hBase,hFrame,hCost⟩

/-- Inverting the canonical base-mate permutation needs one two-probe
scatter per base port. Forward and shift columns survive in separate arrays. -/
theorem scatterBaseIn {a l : ℕ} (Y : State a l) (m : Memory w) (p : Fin 2 → Word w) (shift : ℕ)
    (regions : SlotScatter.Regions p (Fintype.card Y.Base * 2^a) (Fintype.card Y.Base * 2^a))
    (forward : BaseForward Y (p 0).val shift m)
    (hshift : shift+(Fintype.card Y.Base * 2^a) ≤ (p 1).val ∨ (p 1).val+(Fintype.card Y.Base * 2^a) ≤ shift) :
    let n := Fintype.card Y.Base * 2^a
    let worker := ((template SlotScatter.visit 0).instantiate w p).program
    ∃ rs, runSegment worker 10 (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ n) ∧
      BaseForward Y (p 0).val shift (after m (eventLog rs)) ∧
      (∀ e, after m (eventLog rs) ((p 1).val+(IncidenceDirectory.baseOrder Y e).val) =
        Fin.ofNat _ (IncidenceDirectory.baseOrder Y (Y.slots.base.target.symm e)).val) ∧
      (∀ addr, addr < (p 1).val ∨ (p 1).val+n ≤ addr → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost Report.probes rs = 3*n := by
  intro n worker
  let o := IncidenceDirectory.baseOrder Y
  let t := o.symm.trans (Y.slots.base.target.trans o)
  have stored (i : Fin n) : m ((p 0).val+i.val) = Fin.ofNat _ (t i).val := by
    have h := forward.mate (o.symm i)
    change m ((p 0).val+(o (o.symm i)).val) = _ at h
    rwa [o.apply_symm_apply] at h
  obtain ⟨rs,hr,hc,hvals,hframe,_,_,hcost⟩ := SlotScatter.run regions t.toEmbedding m stored
  refine ⟨rs,hr,hc,⟨?_,?_⟩,?_,?_,hcost⟩
  · intro e
    rw [hframe,forward.mate]
    intro i; have he := (o e).isLt; have ht := (t i).isLt; have := regions.disjoint; change _+ (o e).val ≠ _+(t i).val; omega
  · intro e
    rw [hframe,forward.displacement]
    intro i; have he := (o e).isLt; have ht := (t i).isLt; change _+(o e).val ≠ _+(t i).val; omega
  · intro e
    have hx : t (o (Y.slots.base.target.symm e)) = o e := by simp [t]
    simpa only [Equiv.coe_toEmbedding,hx] using hvals (o (Y.slots.base.target.symm e))
  · intro addr ha
    exact hframe addr (fun i ↦ by have hi := (t i).isLt; change addr ≠ _+(t i).val; omega)

end CompressorRecords.ShrinkSlots

end VPVNP
end Computability
end OAI
