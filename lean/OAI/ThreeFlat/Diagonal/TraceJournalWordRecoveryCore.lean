import OAI.ThreeFlat.Diagonal.TraceJournalRecovery
import OAI.Hierarchy.TraceShrinkWordVisitData
import OAI.ThreeFlat.Diagonal.NavigationRecordedWordStep
import OAI.ThreeFlat.Diagonal.PhysicalProgramAssembly

namespace OAI
/-! # Word recovery for a retained receiver trace -/

namespace ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalProcedure RAM.NavigationNodeRows
open PhysicalStage PhysicalStage.Run NavigationDirectory HistoryContraction CompressorPacking Native
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F]

private theorem saved {a : Archive} {W limit s : ℕ} {cur ctr : Word W}
    (P : Program F s) (rem : ℕ) (X : State (2^s) (P.charge+rem)) (c : Cursor) (raw : List Bool)
    {out final : Memory W} (tail : a.TraceJournal limit cur ctr P rem X c raw out final) :
    SavedFrame cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header c.header c.heap out final :=
  fun _x hc ht hdr low => Archive.TraceJournal.frame P rem X c raw tail hc ht ⟨hdr,Or.inl low⟩

def Words {d l : ℕ} {A : State d l} (r : Run F A) (E : r.Records) (C : r.Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool)
    (J : (Pins : Type) → r.Assembler Pins) (vis : (Pins : Type)→Run.WordVisit F Pins)
    (post : List NodeRow → Layer → Prop) : Prop :=
  ∃ (h : r.plan.History) (suffix : List Bool) (p : r.ArchivePath h C O),
    r.plan.read (r.codes E) raw=some (h,suffix) ∧ r.FinalNumbered h C O p ∧
    (∀ (Pins : Type) (L : A.Words Pins),r.WordVisits (vis Pins) h (J Pins).steps L C O p) ∧
    post (r.archiveList h C O p data) (r.finalArchive h C O p).1

theorem recast {d l L k w tariff : ℕ} (e : l=L) (A : State d l) (r : Run F (e ▸ A : State d L))
    {sizes : List ℕ} (table : Program.RecordTable r k w sizes) (C : Program.Certified r tariff)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool)
    (J : (Pins : Type) → r.Assembler Pins) (vis : (Pins : Type)→Run.WordVisit F Pins)
    (post : List NodeRow→Layer→Prop) :
    Words r table.records C.1 (TraceRecovery.castSites e A O) data raw J vis post →
    Words (Program.recast e A r) (Program.changeTable e A r table).records (Program.certRecast e A r C).1 O
      data raw (fun Pins=>Run.inputAssembler e A r (J Pins)) vis post := by cases e; exact id

private theorem prepend {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ t,Run F (R.next t)) (E : (Run.step R next).Records) (C : (Run.step R next).Charges)
    (O : A.ArchiveSites) (data : LayerData O.layer) (raw : List Bool)
    (J : (Pins : Type)→(Run.step R next).Assembler Pins) (vis : (Pins : Type)→Run.WordVisit F Pins)
    (post : List NodeRow→Layer→Prop) (t : Fin R.rules.count) (hit : E.1.read (raw.take E.1.width)=some t)
    (step : R.ArchiveStep t O (C.1 t))
    (word : ∀ (Pins : Type) (L : A.Words Pins),vis Pins R t L ((J Pins).steps.1 L t) O (C.1 t) step) :
    Words (next t) (E.2 t) (C.2 t) step.sites step.data (raw.drop E.1.width)
      (fun Pins=>⟨(J Pins).steps.2 t⟩) vis (fun xs last=>post (TraceRecovery.interleave R t O step data :: xs) last) →
    Words (.step R next) E C O data raw J vis post := by
  rintro ⟨h,suffix,p,parse,num,visits,valid⟩
  refine ⟨Run.joinHistory R next t h,suffix,Run.joinArchivePath R next C O t h step p,
    Run.read_joinHistory R next E raw t hit h suffix parse,Run.joined_finalNumbered R next C O t h step p num,
    fun Pins L=>Run.joined_wordVisits R next (vis Pins) (J Pins).steps L C O t h step p (word Pins L)
      (visits Pins ((J Pins).steps.1 L t).words),?_⟩
  rw [Run.archiveList_joinArchivePath,Run.finalArchive_layer_joinArchivePath]
  exact valid

private theorem monotone (K : ℕ) (c : Cursor) (op : Stage) :
    c.header ≤ (allocate K c op).next.header ∧ c.dense ≤ (allocate K c op).next.dense := by
  cases op <;> constructor <;> apply Nat.le_add_right

/-- The word-assembly recovery statement for one program and every admitted input state. -/
def WordRecoveryFor {a : Archive} {W limit : ℕ} {cur ctr : Word W}
    (Z tariff : ℕ) («protected» : ℕ → Prop) (H MCap : ℕ) (initial : Layer → Prop)
    (allow : StaticMotif F → Prop) {s : ℕ} (P : Program F s) : Prop :=
  ∀ (bounds : ∀ b ∈ P.recordBounds, b.1 ≤ a.K ∧ b.2*Z < 2^W)
    (costs : ∀ n ∈ P.factors, n ≤ tariff) (rem : ℕ) (X : State (2^s) (P.charge+rem))
    (reach : (P.run rem X).WidthCeiling Z) (c : Cursor) (raw : List Bool)
    {input final : Memory W} (_journal : a.TraceJournal limit cur ctr P rem X c raw input final)
    (old : X.ArchiveSites) (_num : old.Numbered) (_first : old.layer.first = c.node)
    (data : LayerData old.layer)
    (_seed : initial old.layer ∨ TraceRecovery.RowContents data «protected» (fun i => (final i).val) H MCap)
    (_space : TraceRecovery.JournalSpace a.K W H MCap (P.directory rem (Fintype.card X.Base)) c old.layer «protected»)
    (_support : P.SupportedBy allow)
    (_headerDense : (finish a.K (P.directory rem (Fintype.card X.Base)) c).header ≤ a.cursor.dense)
    (_headerStart : 21*(2^(W/16))^4 ≤ c.header) (_denseStart : a.cursor.dense ≤ c.dense),
    Words (P.run rem X) (P.table a.K W Z bounds rem X reach).records
      (P.certifiedCharges tariff costs rem X).1 old data raw
      (fun Pins => P.assembly (Pins:=Pins) rem X)
      (fun Pins => RecordedWordStep a.K cur ctr (finish a.K (P.directory rem (Fintype.card X.Base)) c).header
        (finish a.K (P.directory rem (Fintype.card X.Base)) c).heap final Pins allow)
      (TraceRecovery.stagePost a.K (P.directory rem (Fintype.card X.Base)) c old.layer «protected» (fun i=>(final i).val) H MCap initial)

end

end ThreeFlat.Diagonal.NavigationPass.TraceWordRecovery

end OAI
