import OAI.ThreeFlat.Diagonal.TraceJournalWordRecoveryShrink
import OAI.ThreeFlat.Diagonal.TraceJournalWordRecoveryRefresh

namespace OAI
/-! # Word assembly visits of the actual retained receiver trace -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3200000 in
/-- Recovery from the exact stored chronology at any native word size. -/
theorem reconstruct {a : Archive} {W limit s : ℕ} {cur ctr : Word W}
    (P : Program F s) (Z tariff : ℕ)
    (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^W)
    (costs : ∀ n∈P.factors,n≤tariff) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    (room : Hierarchy.TraceRetainedRoom.Room limit W) (wide : 8≤W)
    (controls : cur.val<ctr.val) (old : X.ArchiveSites) (num : old.Numbered)
    (first : old.layer.first=c.node) (data : LayerData old.layer) («protected» : ℕ→Prop) (H MCap : ℕ)
    (initial : Layer→Prop) (seed : initial old.layer ∨ TraceRecovery.RowContents data «protected» (fun i=>(final i).val) H MCap)
    (space : TraceRecovery.JournalSpace a.K W H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected»)
    (allow : StaticMotif F→Prop) (support : P.SupportedBy allow)
    (wireBase : limit ≤ 2^(W/16))
    (headerDense : (finish a.K (P.directory rem (Fintype.card X.Base)) c).header ≤ a.cursor.dense)
    (headerStart : 21*(2^(W/16))^4 ≤ c.header) (denseStart : a.cursor.dense ≤ c.dense) :
    Words (P.run rem X) (P.table a.K W Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (fun Pins => P.assembly (Pins:=Pins) rem X)
      (fun Pins => RecordedWordStep a.K cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header
        (finish a.K (P.directory rem (Fintype.card X.Base)) c).heap final Pins allow)
      (TraceRecovery.stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap initial) := by
  have allPrograms {t : ℕ} (p : Program F t) :
      WordRecoveryFor (a:=a) (limit:=limit) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap initial allow p := by
    induction p with
    | done s =>
      intro bounds costs rem X reach c raw input final journal old num first data seed space support headerDense headerStart denseStart
      refine ⟨(),raw,(),rfl,num,(by intros; trivial),rfl,rfl,?_⟩
      intro q h
      rcases List.mem_singleton.mp h with rfl
      refine ⟨seed, ?_, ?_⟩
      · intro impossible
        cases impossible
      · intro impossible
        cases impossible
    | shrink s t G small tail ih =>
      exact recoverShrinkWords s t G small tail ih room wide controls wireBase
    | refresh s t h pad g γ cost G hm hh sym rows zero conn degree tail ih =>
      exact recoverRefreshWords s t h pad g γ cost G hm hh sym rows zero conn degree tail ih room wide controls wireBase
  exact allPrograms P bounds costs (rem:=rem) (X:=X) reach c raw journal old num first data seed space
    support headerDense headerStart denseStart


end
end ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery

end OAI
