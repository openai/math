import OAI.Computability.BorderVNP.DiagonalEnrichedInstalledTags
import OAI.Computability.BorderVNP.DiagonalInnerTagModels
import OAI.Computability.BorderVNP.DiagonalEnrichedOuterReplay

/-! # Private birth observations after one entire compiled enriched epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

open Diagonal.ExternalSew Diagonal.CellEntries Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Site.Programs PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

universe u

variable {D m start T exp : ℕ} [NeZero D] {K E P Team Param Gadget : Type} [Field K] [Field E] [Fintype P]
    [Fintype Team] [Fintype Param] {bits : P → ℕ} {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {good : ∀ t, State S start P bits shape W t → Prop} {deep : S.floor+1+S.drop*T ≤ start} {t : ℕ} {ht : t<T}
    {V : ℕ → Type} [∀ j, Fintype (V j)] {w : ℕ → ℕ}
    (F : Epoch.{u} deep ht good V w) (rows : F.F.SiteRows) {oldCap newCap : ℕ}
    (oldPort : Port (fan S) P t ↪ Fin oldCap) (nextPort : Port (fan S) P (t+1) ↪ Fin newCap)
    (layout : F.FieldRows rows oldPort nextPort)
    (y : e.Entry → E) (hy : ∀ p : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry p = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y p = 0)
    (pos : e.Entry → Gadget) (num : Gadget ↪ ℕ)
    (c : Fin (fan S) → Admissible good t) (old : ∀ j, Site.Programs (c j).val.pack.layout)


include layout in
/-- All retained private tapes in the active outer epoch implement the
specialized tag on every local input, while enforcing precisely the original
independent choices at its retained child hosts. -/
theorem privatePrograms_tagModels (tag : ∀ j : Fin (fan S), @Tracked _ _ _ (Port (fan S) Team t) Param Gadget (Replay.batchFinite (fan S) Team t) inferInstance exp ((c j).val.pack.layout))
    (pred : ∀ j : Fin (fan S), (c j).val.pack.layout.Site → (ℕ → Bool) → Prop)
    (prior : ∀ j, TagModels (c j).val.pack.layout (c j).val.rows.edge oldPort (old j) (@Tracked.tags _ _ _ (Port (fan S) Team t) Param Gadget (Replay.batchFinite (fan S) Team t) inferInstance exp _ (tag j)) num (pred j)) (q : F.F.Hist (F.run c).flat) :
    TagModels (F.term c q).val.pack.layout (F.term c q).val.rows.edge nextPort
      (F.privatePrograms rows c old (num ∘ pos) q) (@Tracked.tags _ _ _ (Port (fan S) Team (t+1)) Param Gadget (Replay.batchFinite (fan S) Team (t+1)) inferInstance exp _ (EnrichedOuterReplay.emit F y hy pos c tag q)) num
      (carryPred (enrichedEpochHosts (F.run c) F.saveNames q).site (fun v => pred v.1 v.2)) := by
  let : Fintype (Port (fan S) Team t) := Replay.batchFinite (fan S) Team t
  let : Fintype (Port (fan S) Team (t+1)) := Replay.batchFinite (fan S) Team (t+1)
  let run := F.run c
  let initial := F.installedPrivatePrograms rows c old
  let input i := EnrichedSiteReplay.installed run i (tag i)
  let kept i := enrichedInstalledHosts run.flat run.initialSites run.originalPack i
  let p i := carryPred (kept i).site (pred i)
  have model := F.F.flatPrivatePrograms_tagModels F.saveNames rows layout.layout y hy pos num run.flat initial input p
    (F.installedPrivatePrograms_tagModels rows oldPort nextPort layout c old num tag pred prior) q
  let keep := normalizedHosts F.F (namesStorage F.F F.saveNames) run.flat q
  have joint : carryPred keep.site (fun v => p v.1 v.2) =
      carryPred (enrichedEpochHosts run F.saveNames q).site (fun v => pred v.1 v.2) :=
    (congrArg (carryPred keep.site) (carryPred_parallel kept (fun v => pred v.1 v.2)).symm).trans
      (carryPred_trans (Retains.parallel kept).site keep.site (fun v => pred v.1 v.2))
  have changed := TagModels.changePrivate (instFintypeProd (Fin (fan S)) (Port (fan S) P t))
    (portFintype (k:=fan S) (P:=P) (b:=t+1)) (F.term c q).val.pack.layout (layout.layout.edges S.rounds (run.root q))
    (Flat.portRows S.rounds (rows.ports S.rounds)) (F.F.flatPrivatePrograms F.saveNames rows (num ∘ pos) run.flat initial q)
    (@Tracked.tags _ _ _ (Port (fan S) Team (t+1)) Param Gadget (Replay.batchFinite (fan S) Team (t+1)) inferInstance exp _ (EnrichedOuterReplay.emit F y hy pos c tag q)) num _ model
  have result := TagModels.renumber (F.term c q).val.pack.layout (layout.layout.edges S.rounds (run.root q)) (Flat.portRows S.rounds (rows.ports S.rounds))
    (F.privatePrograms rows c old (num ∘ pos) q) (@Tracked.tags _ _ _ (Port (fan S) Team (t+1)) Param Gadget (Replay.batchFinite (fan S) Team (t+1)) inferInstance exp _ (EnrichedOuterReplay.emit F y hy pos c tag q)) num _ changed
    (F.term c q).val.rows.edge nextPort layout.outputCap layout.outputPortCap (layout.outputRows c q) layout.outputPorts
  intro v
  exact (result v).congrPred fun g => Iff.of_eq (congrFun (congrFun joint v) (extendWork g))

end PackedHistoryCircuit.Normalized.EnrichedOuter.Epoch

end BorderVNP
end Computability
end OAI
