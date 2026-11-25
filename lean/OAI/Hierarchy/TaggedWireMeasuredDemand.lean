import OAI.Hierarchy.TaggedWireElectedOutput
import OAI.Hierarchy.TaggedWireRepairStock

namespace OAI
/-! # The ordinary and catalyst debits in the elected packet source -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open ProtocolRAM Calendar StockCommit PurchaseStage RepairHistogram ChosenPackets Probe AdaptiveProbe
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing

private theorem keyed_widths {I H : Type} [Fintype I] [Fintype H] {K : ℕ}
    (G : PortGraph (Fin K) H) (owner : I→Option H) (amount : I→ℕ) :
    G.chordWidths (OuterBank.resourceBits owner amount)=
      ∑i, (owner i).elim 0 (fun j=>G.chordWidth j (amount i)) := by
  classical
  simp only [PortGraph.chordWidths,chordWidth_scaled,OuterBank.resourceBits,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases eq : owner i with
  | none => simp []
  | some j => simp [ite_smul]

namespace CalendarTape.HistogramFormat

variable {F X A : Type} [Field F] [Fintype A] {S W q d : ℕ} {C : Chart W q d}
    (D : HistogramFormat C X) (ev : Attempt) (x : X) (start post : Memory W)
    (a : Area) (s : Sources) (G : PortGraph (Fin S) (Fin a.goods)) (K : PortGraph (Fin S) A)
local notation "raw" => enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)
local notation "snap" => HistogramShelf.snapshot C ev start
local notation "I" => Fin (C.layout ev).candidates
local notation "picked" => fun i:I=>(raw).selected snap (i.val:Word W)
variable (view : D.observed ev x start)
    (menu : ∀i : Fin (C.layout ev).candidates,
      (enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).selected
        (HistogramShelf.snapshot C ev start) (i.val : Word W) → Placed F S)
    (arity : ∀i hi, (menu i hi).data.terms =
      ((enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).termCount.read
        (HistogramShelf.snapshot C ev start)
        ((enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev)).packet.eval
          (HistogramShelf.snapshot C ev start) (i.val : Word W))).val)
    (L : PortPlan (fresh a s) (enabledBatch (C.layout ev) (ProtocolRAM.Calendar.repair C ev))
      post (C.layout ev).candidates)
local notation "tag" => RepairHistogram.kind (goods:=a.goods) (fresh a s).plan.bank (fresh a s).columns post
local notation "debit" => RepairHistogram.consumedBits (n:=a.occurrences) (fresh a s).columns post
local notation "rows" => D.electedRow ev x start view menu arity

/-- Starting with native (padded) elected packet inputs, total every real
occurrence, including parallel debits of the same commodity or reserve pair. -/
theorem measured_source (wire : Fin a.occurrences→Chord S)
    (owner : Fin a.occurrences→Option A) (issued : Fin a.occurrences→ℕ)
    (ballot : BallChoices (D.letters ev x) (D.copies ev x))
    (quiet : ∀j:I,¬picked j→j∉liveRows raw post (C.layout ev).candidates)
    (active : ∀(j:I),picked j→((rows) j).input=
      optionWidths (fun v=>wire (L.enum ⟨j,v⟩)) (fun v=>(debit) (L.enum ⟨j,v⟩)))
    (classified : ∀i, Finsupp.single (wire i) ((debit) i)=
      ((tag) i).elim 0 (fun g=>G.chordWidth g ((debit) i))+
      (owner i).elim 0 (fun t=>K.chordWidth t (issued i))) :
    (∑j:I,((rows) j).input)=G.chordWidths (OuterBank.resourceBits tag debit)+
      K.chordWidths (OuterBank.resourceBits owner issued) := by
  classical
  rw [keyed_widths G,keyed_widths K,← Finset.sum_add_distrib]
  simp_rw [←classified]
  refine Eq.trans ?_ (L.enum.sum_comp (fun i => Finsupp.single (wire i) ((debit) i)))
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases elected : picked j
  · exact active j elected
  · rw [(D.electedRow_dormant ev x start view menu arity j elected (ballot j)).1]
    symm
    apply Finset.sum_eq_zero
    intro v _
    have dormant := (L.off (L.enum ⟨j,v⟩) (by simpa using quiet j elected)).2
    exact (Finsupp.single_eq_zero).mpr dormant

end CalendarTape.HistogramFormat
end Hierarchy.WireTelescope
end

end OAI
