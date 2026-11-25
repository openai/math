import OAI.ThreeFlat.Diagonal.TraceJournalRecoveryShrink
import OAI.ThreeFlat.Diagonal.TraceJournalRecoveryRefresh
import OAI.ThreeFlat.Diagonal.TraceJournalScanner
import OAI.ThreeFlat.Diagonal.CursorSeedSites

namespace OAI
/-! # Recovering the genuinely selected typed site archive from the width-generic native passes

The proof follows the selected native records and their committed memory through every
future stage. The degree cast at a refresh step preserves the exact physical row object.
-/

namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
/-- Recovery from the exact stored chronology at any native word size. -/
theorem reconstructRows {a : Archive} {W limit s : ℕ} {cur ctr : Word W}
    (P : Program F s) (Z tariff : ℕ)
    (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^W)
    (costs : ∀ n∈P.factors,n≤tariff) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    (room : Hierarchy.TraceRetainedRoom.Room limit W) (wide : 8≤W)
    (controls : cur.val<ctr.val) (old : X.ArchiveSites) (num : old.Numbered)
    (first : old.layer.first=c.node) (data : LayerData old.layer) («protected» : ℕ→Prop) (H MCap : ℕ)
    (initial : Layer→Prop) (seed : initial old.layer ∨ RowContents data «protected» (fun i=>(final i).val) H MCap)
    (space : JournalSpace a.K W H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected») :
    Recovered (P.run rem X) (P.table a.K W Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap initial) := by
  have every {t : ℕ} (p : Program F t) : RecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial p := by
    induction p with
    | done s =>
      intro bounds costs rem X reach c raw input final journal old num first data seed space
      refine ⟨(),raw,(),rfl,num,rfl,rfl,?_⟩
      intro q h
      rcases List.mem_singleton.mp h with rfl
      refine ⟨seed, ?_, ?_⟩
      · intro impossible
        cases impossible
      · intro impossible
        cases impossible
    | shrink s t G small tail ih => exact recoverShrink s t G small tail ih room wide controls
    | refresh s t h pad g γ cost G hm hh sym rows zero conn degree tail ih => exact recoverRefresh s t h pad g γ cost G hm hh sym rows zero conn degree tail ih room wide controls
  exact every P bounds costs reach c raw journal old num first data seed space

/-- All seed and descendant row contents are present in the final memory. -/
theorem reconstruct {a : Archive} {W limit s : ℕ} {cur ctr : Word W}
    (P : Program F s) (Z tariff : ℕ)
    (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^W)
    (costs : ∀ n∈P.factors,n≤tariff) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    (room : Hierarchy.TraceRetainedRoom.Room limit W) (wide : 8≤W)
    (controls : cur.val<ctr.val) (old : X.ArchiveSites) (num : old.Numbered)
    (first : old.layer.first=c.node) (data : LayerData old.layer) («protected» : ℕ→Prop) (H MCap : ℕ)
    (seed : RowContents data «protected» (fun i=>(final i).val) H MCap)
    (space : JournalSpace a.K W H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected») :
    Recovered (P.run rem X) (P.table a.K W Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap (fun _=>False)) :=
  reconstructRows P Z tariff bounds costs rem X reach c raw journal room wide controls old num first data «protected» H MCap (fun _=>False) (Or.inr seed) space

/-- For an owner-only pass the initial widths need not have been mounted. Owner
arrays and their occupied addresses are published unconditionally, including
the very first step; noninitial layers carry all their physical data reads. -/
theorem reconstruct_owners {a : Archive} {W limit s : ℕ} {cur ctr : Word W}
    (P : Program F s) (Z tariff : ℕ)
    (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^W)
    (costs : ∀ n∈P.factors,n≤tariff) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    (room : Hierarchy.TraceRetainedRoom.Room limit W) (wide : 8≤W)
    (controls : cur.val<ctr.val) (old : X.ArchiveSites) (num : old.Numbered)
    (first : old.layer.first=c.node) (data : LayerData old.layer) («protected» : ℕ→Prop) (H MCap : ℕ)
    (space : JournalSpace a.K W H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected») :
    Recovered (P.run rem X) (P.table a.K W Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap (·=old.layer)) :=
  reconstructRows P Z tariff bounds costs rem X reach c raw journal room wide controls old num first data «protected» H MCap (·=old.layer) (Or.inl rfl) space


end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI
