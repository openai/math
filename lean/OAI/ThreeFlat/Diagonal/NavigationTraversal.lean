import OAI.ThreeFlat.Diagonal.NavigationTraversalShrink
import OAI.ThreeFlat.Diagonal.NavigationTraversalRefresh

namespace OAI
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory HistoryContraction
open Native.ShrinkStage Native.ShrinkStage.Resident PhysicalShrink
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

set_option maxHeartbeats 1000000 in
theorem Archive.Journal.reconstruct {a : Archive} {u s : ℕ} {cur ctr : Word (16*u^10)}
    (P : Program F s) (Z tariff : ℕ)
    (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^(16*u^10))
    (costs : ∀ n∈P.factors,n≤tariff) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory (16*u^10)} (journal : a.Journal u cur ctr P rem X c raw input final)
    (age : 40≤u) (controls : cur.val<ctr.val) (old : X.ArchiveSites) (num : old.Numbered)
    (first : old.layer.first=c.node) (data : LayerData old.layer) («protected» : ℕ→Prop) (H MCap : ℕ)
    (seed : RowContents data «protected» (fun i=>(final i).val) H MCap)
    (space : JournalSpace a.K (16*u^10) H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected»)
    (allow : StaticMotif F→Prop) (support : P.SupportedBy allow)
    (headerDense : (finish a.K (P.directory rem (Fintype.card X.Base)) c).header≤a.cursor.dense)
    (headerStart : TickWorkspace.base u 20 ≤ c.header) (denseStart : a.cursor.dense ≤ c.dense) :
    Recovered (P.run rem X) (P.table a.K (16*u^10) Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (RecordedStep a.K cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header
        (finish a.K (P.directory rem (Fintype.card X.Base)) c).heap final)
      (fun Pins=>P.assembly (Pins:=Pins) rem X)
      (fun Pins=>RecordedWordStep a.K cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header
        (finish a.K (P.directory rem (Fintype.card X.Base)) c).heap final Pins allow)
      (stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap) := by
  have every {t : ℕ} (p : Program F t) : WordRecoveryFor (a:=a) (u:=u) (cur:=cur) (ctr:=ctr) Z tariff «protected» H MCap allow p := by
    induction p with
    | done s =>
      intro bounds costs rem X reach c raw input final journal old num first data seed space support headerDense headerStart denseStart
      refine ⟨(),raw,(),rfl,num,trivial,fun _ _=>trivial,rfl,rfl,?_⟩
      intro q h
      rcases List.mem_singleton.mp h with rfl
      refine ⟨seed, ?_, ?_⟩
      · intro impossible
        cases impossible
      · intro impossible
        cases impossible
    | shrink s t G small tail ih => exact recoverWordShrink s t G small tail ih age controls
    | refresh s t h pad g γ cost G hm hh sym rows zero conn degree tail ih =>
      exact recoverWordRefresh s t h pad g γ cost G hm hh sym rows zero conn degree tail ih age controls
  exact every P bounds costs reach c raw journal old num first data seed space support headerDense headerStart denseStart

end
end ThreeFlat.Diagonal.NavigationPass

end OAI
