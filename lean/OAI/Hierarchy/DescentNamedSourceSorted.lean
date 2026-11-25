import OAI.Hierarchy.DescentNamedBranchPins
import OAI.Hierarchy.DescentSourceSorted

namespace OAI
/-! Source order of every reached positive cable, including the last reset's hub limbs. -/
namespace Hierarchy.DescentSixParty
open DescentPhysicalOrder DescentStageEdgeReceipt DescentPacking
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {n : ℕ} {bits : P→ℕ}

omit [Field F] in
private theorem sorted_after_names (W : MarkedWorld F n P bits)
    (site : W.graph.Site ↪ ℕ) (key : W.graph.Edge ↪ ℕ)
    (before : ∀e f,site (W.graph.src e) < site (W.graph.src f) → key e < key f) :
    IntrinsicallySorted (PhysicalRename.world W (rename site) (rename key)) := by
  let sites:=rename site
  let edges:=rename key
  intro i j
  obtain ⟨u,rfl⟩:=edges.surjective i
  obtain ⟨v,rfl⟩:=edges.surjective j
  change 0 < W.graph.width (edges.symm (edges u))→0 < W.graph.width (edges.symm (edges v))→
    (Fintype.equivFin W.graph.Site (sites (W.graph.src (edges.symm (edges u))))).val <
      (Fintype.equivFin W.graph.Site (sites (W.graph.src (edges.symm (edges v))))).val → Fintype.equivFin W.graph.Edge (edges u) < Fintype.equivFin W.graph.Edge (edges v)
  simp only [Equiv.symm_apply_apply,sites,edges,code_rename]
  intro _ _ order
  exact (physical_lt_iff key u v).2 (before u v ((physical_lt_iff site _ _).1 order))

end
end Hierarchy.DescentSixParty

namespace Hierarchy.DescentSixParty.ResetInput
open DescentCompiler DescentPacking DescentRosterOrder DescentStageEdgeReceipt GroupStage
open scoped Classical BigOperators
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {H M : ℕ} (vertex : Z.V↪Fin H) (key : A.graph.Edge↪Fin M)
local notation "norm" => orderedReblock Z T key
local notation "tape" => nativeResetEdges Z T vertex key
local notation "rank" => (rawHostRank Z T vertex).trans Fin.valEmbedding
variable {G : PoweredGadget F} {q fee : ℝ} {groups k i : ℕ} {S : AtomSchedule}
    (N : GroupStage (orderedOrdinary Z T key) G q fee (Fin groups) (↥(commonNames Z T)) k) (paid : N.StateBounds S i)
local notation "rows" => DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) rank
local notation "ps" => DescentPhysicalOrder.rename (N.siteFrom rows paid.coordinates)
local notation "rawId" => (tape).order.trans Fin.valEmbedding
local notation "siteId" => N.siteFrom rows paid.coordinates
local notation "shortId" => DescentResetLocalOrder.allCode N rawId S paid siteId
local notation "pe" => DescentPhysicalOrder.rename shortId

theorem named_source_sorted : SourceSorted (namedReset Z T vertex key N paid).result (namedOrder Z T vertex key N paid) := by
  apply IntrinsicallySorted.expose _ _ (namedEdges Z T vertex key N paid)
  change IntrinsicallySorted ((norm).appendNames ps pe).result
  rw [(norm).appendNames_result ps pe]
  apply sorted_after_names _ siteId shortId
  intro a b earlier
  have inside : rawId a < (Finset.univ.sup rawId)+1 := Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ a))
  have bound:=Nat.mul_le_mul_right ((Finset.univ.sup rawId)+1) (Nat.succ_le_of_lt earlier)
  rw [Nat.succ_mul] at bound
  simp only [DescentResetLocalOrder.code_val]
  omega

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k i z D j z' D' wire hist : ℕ}
  {bits : P→ℕ} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
  {U W : MarkedWorld F d P bits} {first : Reached U G q ε S k i z D wire hist}
  {last : Reached W G q ε S k j z' D' wire hist}

omit [Fintype P] in
theorem Path.final_sourceSorted (path : Path first last) (elapsed : i < j) : SourceSorted W last.order := by
  cases path with
  | here=>omega
  | ordinary prev ticket=>exact ticket.sourceSorted
  | reset prev closed=>exact closed.reset.named_source_sorted closed.terminals _ _ closed.raw closed.valid

end
end Hierarchy.DescentSixParty.Chronology

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

theorem Branch.final_sourceSorted (elapsed : 0 < S.length) :
    SourceSorted ((Epochs.finish G hu he r).state c) b.target.order := b.path.final_sourceSorted elapsed

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
