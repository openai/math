import OAI.ThreeFlat.Diagonal.TraceJournalRows

namespace OAI
/-! # The induction property for recovery of the selected journal -/
namespace ThreeFlat.Diagonal.NavigationPass.TraceRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

private theorem mapRecovered {d l : ℕ} {A : State d l} {r : Run F A} {E : r.Records} {C : r.Charges}
    {O : A.ArchiveSites} {data : LayerData O.layer} {raw : List Bool} {before after : List NodeRow → Layer → Prop}
    (history : Recovered r E C O data raw before)
    (update : ∀ xs last, before xs last → after xs last) : Recovered r E C O data raw after := by
  obtain ⟨h,suffix,p,parse,num,post⟩ := history
  exact ⟨h,suffix,p,parse,num,update _ _ post⟩

private theorem recovered_drop {d l : ℕ} {A : State d l} {r : Run F A} {E : r.Records} {C : r.Charges}
    {O : A.ArchiveSites} {data : LayerData O.layer} {raw : List Bool}
    {post : List NodeRow → Layer → Prop} {issued stored : ℕ} (width : issued=stored)
    (result : Recovered r E C O data (raw.drop stored) post) : Recovered r E C O data (raw.drop issued) post := by
  cases width
  exact result

open private prepend_recovered from OAI.ThreeFlat.Diagonal.TraceJournalRows

private theorem recoverJoinedStage {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t,Run F (R.next t)) (E : (Run.step R next).Records) (C : (Run.step R next).Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool) (t : Fin R.rules.count)
    (hit : E.1.read (raw.take E.1.width)=some t) (step : R.ArchiveStep t O (C.1 t))
    {K H M : ℕ} {op : Stage} {ops : List Stage} {c : Cursor} {mem : ℕ→ℕ}
    {«protected» : ℕ→Prop} {initial : Layer→Prop}
    (first : step.sites.layer.first=(allocate K c op).next.node)
    (owner : step.ownerPtr=(allocate K c op).words 44) (layer : step.sites.layer=nodeLayer K c op)
    (head : ArchivedSource (interleave R t O step data) «protected» mem H M initial)
    (tail : Recovered (next t) (E.2 t) (C.2 t) step.sites step.data (raw.drop E.1.width)
      (stagePost K ops (allocate K c op).next step.sites.layer «protected» mem H M initial)) :
    Recovered (.step R next) E C O data raw (stagePost K (op::ops) c O.layer «protected» mem H M initial) := by
  have parent : (interleave R t O step data).parent =
      ⟨false,(allocate K c op).next.node,(allocate K c op).words 44⟩ := by
    change Parent.mk false step.sites.layer.first step.ownerPtr=_
    rw [first,owner]
  exact prepend_recovered R next E C O data raw _ t hit step
    (mapRecovered tail (fun _ _ saved => extend_stagePost rfl parent layer head saved))

/-- Recover the chosen native history and every stored row, from any bounded input state of the program. -/
def RecoveryFor {a : Archive} {W limit s : ℕ} {cur ctr : Word W}
    (Z tariff : ℕ) («protected» : ℕ→Prop) (H MCap : ℕ) (initial : Layer→Prop) (P : Program F s) : Prop :=
    ∀ (bounds : ∀ b∈P.recordBounds,b.1≤a.K ∧ b.2*Z<2^W)
    (costs : ∀ n∈P.factors,n≤tariff) {rem : ℕ} {X : State (2^s) (P.charge+rem)}
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (_journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    (old : X.ArchiveSites) (_num : old.Numbered)
    (_first : old.layer.first=c.node) (data : LayerData old.layer) (_seed : initial old.layer ∨ RowContents data «protected» (fun i=>(final i).val) H MCap)
    (_space : JournalSpace a.K W H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected»),
    Recovered (P.run rem X) (P.table a.K W Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap initial)

end
end ThreeFlat.Diagonal.NavigationPass.TraceRecovery

end OAI
