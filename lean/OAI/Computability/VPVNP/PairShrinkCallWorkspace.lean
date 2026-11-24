import OAI.Computability.VPVNP.PairShrinkCallFields
import OAI.Computability.VPVNP.PairSimulationMapWorkspaceLayout
import OAI.Computability.VPVNP.PairSimulationMapArgumentInput

/-!
# Workspace and argument separation of the six-party map

The private input addresses may lie on either side of the histogram. All
inputs end before the map's port directory, then come its argument record,
selector ordinals and decoded labels. The nine staging intervals comprise
AB and the source and target of each of the four surviving wire types.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallFields

open BurstRAM Compression Compression.ShrinkMotif MotifEntry
open MotifGrid MotifBlocks MotifConversion MapWorkspace
open scoped Fin.CommRing

variable {w : ℕ}

theorem Scratch.shared_end (s : Scratch) {n : ℕ} (hm : n < s.motifs) (t : Fin 4) :
    s.shared n t + s.stride ≤ s.staging := by
  have k : n * 4 + t.val + 1 ≤ 4 * s.motifs := by have := t.isLt; omega
  have hk := Nat.mul_le_mul_right s.stride k
  rw [Nat.succ_mul] at hk
  unfold Scratch.shared Scratch.staging
  omega

theorem Scratch.surviving_end (s : Scratch) (dir : Bool) (t : Fin 4) :
    s.surviving dir t + s.stride ≤ s.directory := by
  have k : 1 + dir.toNat * 4 + t.val + 1 ≤ 9 := by cases dir <;> have := t.isLt <;> simp <;> omega
  have hk := Nat.mul_le_mul_right s.stride k
  rw [Nat.succ_mul] at hk
  unfold Scratch.surviving Scratch.directory
  omega

theorem Scratch.rawEnd (s : Scratch) (n : ℕ) (hn : n < s.motifs) (j : Fin 6) (layout : Bool)
    (cd : Bool → ℕ) (demand : Bool → ℕ) (payload : Bool × Fin 4 → ℕ) (tags copies : ℕ)
    (ab : demand false ≤ s.stride) (old : ∀ dir, cd dir + demand true ≤ s.hidden)
    (wire : ∀ e, payload e + copies * tags ≤ s.stride) (f : Endpoint) :
    s.fieldBase n j layout cd f + rawWidth demand payload tags copies f ≤ s.directory := by
  have before : s.hidden ≤ s.staging := Nat.le_add_right ..
  have after : s.staging + s.stride ≤ s.directory := by unfold Scratch.directory; omega
  rcases f with ⟨dir, e⟩ | ⟨dir, e⟩
  · cases e
    · change (if j = demandParty dir false then s.staging else 0) + demand false ≤ _
      split <;> omega
    · change (if j = demandParty dir true then cd dir else 0) + demand true ≤ _
      have bound := old dir
      split <;> omega
  · change (if j = supplyParty dir e then
      (if e.1 = layout then s.surviving dir e.2 else s.shared n e.2) else 0) +
        (payload e + copies * tags) ≤ _
    have endActive := s.surviving_end dir e.2
    have endHidden := s.shared_end hn e.2
    have len := wire e
    split
    · split <;> omega
    · omega

private theorem descriptorBase_eq (s : Scratch) :
    descriptorBase (Bool × Fin 4) s.directory = s.descriptor := by
  change s.directory + 2 * Fintype.card (Bool × Fin 4) = s.directory + 16
  simp

private theorem source_eq (s : Scratch) :
    ordinalBase Bool (Bool × Fin 4) s.directory = s.source := by
  rw [ordinalBase, descriptorBase_eq]
  rfl

variable {K : Type} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable {grid : F.grid.demands} {j : Fin 6} {p r k u t n limit : ℕ}
variable (P : MapEntry.Program F grid j p r k)
variable (demand : Bool → ℕ) (payload : Bool × Fin 4 → ℕ)
variable (d : DemandBits demandSource demandTarget demand j)
variable (x : MotifSelector.Half supply (fun e ↦ Fin (payload e + u * F.selectorBits) → Bool) j)
variable (s : Scratch) (ord : ℕ) (layout : Bool) (cd : Bool → ℕ)

/-- All numerical premises concern physical interval endpoints and the fixed
word capacity. None refers to the map accepting or to its selector sequence. -/
structure Fits : Prop where
  capacity : Capacity F w n limit
  copies : u ≤ n
  ordinal : ord < s.motifs
  ab : demand false ≤ s.stride
  cd : ∀ dir, cd dir + demand true ≤ s.hidden
  supply : ∀ e, payload e + u * F.selectorBits ≤ s.stride
  histogram : s.hist + t ≤ s.directory
  room : s.target u + u ≤ limit

variable (ok : Fits (w := w) (n := n) (limit := limit) (u := u) (t := t)
  F demand payload s ord cd)

/-- The workspace handed to the fixed map-call program on the selected term. -/
noncomputable def workspace : MapEntry.Program.Workspace P demand payload d x t w :=
  scratchWorkspace P demand payload (s.fieldBase ord j layout cd) d x ok.capacity ok.copies
    (fun f ↦ s.rawEnd ord ok.ordinal j layout cd demand payload F.selectorBits u
      ok.ab ok.cd ok.supply f) ok.histogram (copies := u) le_rfl
      (by simpa only [scratchEnd, source_eq, Scratch.target] using ok.room)

local notation "XW" => workspace F P demand payload d x s ord layout cd ok

theorem workspace_cells (f : Endpoint) : (XW).base f = s.fieldBase ord j layout cd f := rfl

theorem workspace_source : (XW).source = s.source := source_eq s

theorem workspace_target : (XW).target = s.target u :=
  congrArg (· + u) (source_eq s)

include ok in
theorem workspace_descriptor_fit : s.descriptor + Fintype.card Arg ≤ 2 ^ w := by
  have room := ok.room.trans_lt ok.capacity.room
  unfold Scratch.target Scratch.source at room
  omega

variable {F}
variable {z : F.grid.demands} (A : MapEntryTable.Allocation F z j r k)
variable (loc : A.Address → Fin p)
local notation "HW" => workspace F (A.program loc) demand payload d x s ord layout cd ok

/-- Any positive input bit precedes every private descriptor and port-directory
cell, including on maps with no demand at the given party. -/
theorem separated (f : Endpoint) (i : Fin (rawWidth demand payload F.selectorBits u f)) :
    MapArgumentWriter.separated A loc (HW) (s.descriptor : Word w)
      ((s.fieldBase ord j layout cd f + i.val : ℕ) : Word w) := by
  have h := s.rawEnd ord ok.ordinal j layout cd demand payload F.selectorBits u
    ok.ab ok.cd ok.supply f
  have small : s.fieldBase ord j layout cd f + i.val < s.directory := by have := i.isLt; omega
  have space := ok.room.trans_lt ok.capacity.room
  unfold Scratch.target Scratch.source Scratch.descriptor at space
  have raw : ((s.fieldBase ord j layout cd f + i.val : ℕ) : Word w).val =
      s.fieldBase ord j layout cd f + i.val := Nat.mod_eq_of_lt (by omega)
  have desc : (s.descriptor : Word w).val = s.descriptor := Nat.mod_eq_of_lt (by
    unfold Scratch.descriptor; omega)
  refine ⟨Or.inl (by rw [raw, desc]; unfold Scratch.descriptor; omega), ?_⟩
  intro a eqn
  have len := MapPortAgreement.ports_length_le supply j A.edgeOrder
  have card : 2 * Fintype.card (Bool × Fin 4) = 16 := by simp
  rw [card] at len
  have fit : s.directory + a.val < 2 ^ w := by have := a.isLt.trans_le len; omega
  have val := congrArg Fin.val eqn
  change _ = ((s.directory : Word w) + (a.val : Word w)).val at val
  rw [← Nat.cast_add, show ((s.directory + a.val : ℕ) : Word w).val = _ from
    Nat.mod_eq_of_lt fit, raw] at val
  omega

end PairSimulation.ShrinkCallFields

end VPVNP
end Computability
end OAI
