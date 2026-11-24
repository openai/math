import OAI.Computability.VPVNP.CompressorShrinkTermInputs
import OAI.Computability.VPVNP.CompressorTermWorkerScan
import OAI.Computability.VPVNP.CompressorShrinkKernelSlices
import OAI.Computability.VPVNP.ShrinkFieldBounds
import OAI.Computability.VPVNP.StatePassHistory

/-!
# Shrinking choices from the physical balanced and original wire widths

The gather and the fused term verifier run on successive memory states.
Their successful streams biject with the actual six-party terms at the
packed CD motifs. Grid, repetition and payload words remain available at
the same dense ordinal for scoring and interval subdivision.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermSelection

open Compression Compression.PackingData MotifGrid MotifBlocks MotifConversion ShrinkMotif BurstRAM
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))

local notation "N" => ShrinkTermInputs.motifCount X
local notation "roles" => ShrinkSliceArrays.supplyRoles
local notation "demand" => ShrinkTermInputs.demand X

/-- The word-fit constant supplied by the native term-scan theorem for shrinking motifs with
two demand coordinates. -/
noncomputable def fitConstant :=
  (TermWorker.scan_native F finTwoEquiv roles demandMass_pos supplyMass_pos).choose

/-- Supply tapes and term rows both use the physical bundle/rank ordinal. -/
noncomputable def tapes (s : X.ShrinkSelection F) (w : ℕ) (j : Fin N) : List Bool :=
  TermRecordScan.tape F roles (demand j) w (s (ShrinkMotifOrder.entries X j)).val

/-- Identify a term choice at each shrinking motif with the same choices in the dense physical
scan order. -/
noncomputable def reindex : X.ShrinkSelection F ≃ TermRecordScan.Choices F demand :=
  Equiv.piCongrLeft' (fun m => ↥(outerIndices F (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m)))
    (ShrinkMotifOrder.entries X).symm

/-- The first header address of the actual CD occurrence's term. -/
noncomputable def rowBase (term : BurstRAM.Word w) (stride : ℕ) (m : X.packingData.Motif) : BurstRAM.Word w :=
  Fin.ofNat _ (term.val+(ShrinkMotifOrder.stateNumber X m).val*stride)

/-- The term worker's four public words, specifying the dense demand base, two demand fields
per motif, the term base and the term-record stride. -/
def addr (dense term : BurstRAM.Word w) (stride : ℕ) : Fin 4 → BurstRAM.Word w :=
  ![dense.val, 2, term.val, stride]

/-- The native shrinking term verifier instantiated with the two demand roles and the dense
demand and term addresses. -/
noncomputable abbrev termProgram (dense term : BurstRAM.Word w) (stride : ℕ) :=
  TermWorker.program F finTwoEquiv roles (addr dense term stride)

/-- The physical term scan runs on the tapes of the given selection, stores each motif's
selected fields, and has the stated cursor, frame, report count and resource bounds. -/
structure Written (dense term : BurstRAM.Word w) (stride cap : ℕ) (s : X.ShrinkSelection F)
    (before : Memory w) (rs : List (Report w)) : Prop where
  run : runSegment (termProgram F dense term stride) cap (some 0) before (List.ofFn (tapes F X s w)) = some rs
  fields : ∀ m, TermRecordScan.Fields F roles demandMass_pos
    (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m) (s m).val
    (rowBase X term stride m) (after before (eventLog rs))
  frame : ∀ x, x < term.val ∨ term.val + N*stride ≤ x → after before (eventLog rs) x = before x
  cursor : endState (some (0 : BurstRAM.Word w)) rs = some (N : BurstRAM.Word w)
  count : rs.length = N
  branches : branchPaths rs = List.ofFn (tapes F X s w)
  probes : countProbes (eventLog rs) ≤ N * TermRecordScan.probesPerRow F 2 8
  steps : (eventLog rs).length ≤ N * TermWorker.budget F 2 8 w X.maxWireWidth

set_option maxHeartbeats 1600000 in
theorem native (dense term : BurstRAM.Word w) (stride : ℕ) (wide : 10 ≤ stride)
    (sep : dense.val+N*2 ≤ term.val) (room : term.val+N*stride < 2^w)
    (mem : Memory w) (pairs : ShrinkTermInputs.statePairs X dense mem)
    (fit : fitConstant F+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (cap : ℕ) (hcap : TermWorker.budget F 2 8 w X.maxWireWidth ≤ cap) :
    (∀ bs : Fin N → List Bool, (runSegment (termProgram F dense term stride) cap (some 0) mem (List.ofFn bs)).isSome ↔
      ∃! s : X.ShrinkSelection F, bs = tapes F X s w) ∧
    ∀ s : X.ShrinkSelection F, ∃ rs, Written F X dense term stride cap s mem rs := by
  let L := ShrinkTermInputs.termRows X dense term stride wide sep room
  have hin := ShrinkTermInputs.inputs X dense term stride wide sep room mem pairs
  have hw (j : Fin N) (e : Bool) : demand j e ≤ X.maxWireWidth :=
    X.packingData.shrinkDemandWidths_le (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.packingWidth (fun _ => X.width_le_maxWireWidth _) _ e
  have haddr : TermWorker.Addresses L (addr dense term stride) :=
    TermWorker.addresses_strided (n := 8) _ _ _ _ le_rfl wide sep room
  obtain ⟨legal,chosen⟩ := (TermWorker.scan_native F finTwoEquiv roles demandMass_pos supplyMass_pos).choose_spec
    N X.maxWireWidth w fit L (addr dense term stride) haddr demand hw mem hin cap hcap
  constructor
  · intro bs
    rw [legal]
    let P := fun v : TermRecordScan.Choices F demand =>
      bs = fun j => TermRecordScan.tape F roles (demand j) w (v j).val
    let E := reindex F X
    change (∃! v, P v) ↔ ∃! s, P (E s)
    constructor
    · rintro ⟨v,hv,uniq⟩
      exact ⟨E.symm v,by simpa using hv,fun s hs => E.injective (by simpa using uniq _ hs)⟩
    · rintro ⟨s,hs,uniq⟩
      refine ⟨E s,hs,fun v hv => ?_⟩
      have h := uniq (E.symm v) (by simpa using hv)
      simpa using congrArg E h
  · intro s
    obtain ⟨rs,hr,fields,frame,cursor,count,bs,probes,steps⟩ := chosen (reindex F X s)
    refine ⟨rs,hr,fun m => ?_,fun x h => frame x (fun i => ?_),cursor,count,bs,probes,steps⟩
    · let j := (ShrinkMotifOrder.entries X).symm m
      have h := fields j
      have eqn : ShrinkMotifOrder.entries X j = m := (ShrinkMotifOrder.entries X).apply_symm_apply m
      have hb : L.base j = rowBase X term stride m := by
        change Fin.ofNat _ (term.val+j.val*stride) = Fin.ofNat _ (term.val+_*stride)
        rw [ShrinkMotifOrder.entries_ordinal]
      rw [hb] at h
      change TermRecordScan.Fields F roles demandMass_pos
        (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth (ShrinkMotifOrder.entries X j))
        (s (ShrinkMotifOrder.entries X j)).val _ _ at h
      rwa [eqn] at h
    · have endRow := Nat.mul_le_mul_right stride i.isLt
      rw [Nat.succ_mul] at endRow
      have hb : (L.base i).val = term.val+i.val*stride := Nat.mod_eq_of_lt (by omega)
      change x < (L.base i).val ∨ (L.base i).val + 2+8 ≤ x
      rw [hb]; omega

end CompressorRecords.ShrinkTermSelection

end VPVNP
end Computability
end OAI
