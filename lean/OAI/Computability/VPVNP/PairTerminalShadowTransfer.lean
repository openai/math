import OAI.Computability.VPVNP.PairTerminalShadowSpan
import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.CompressorSourceTransport

/-! # Preservation of the histogram descriptor through actual pair-stage transfers

A completed native stage can write the pair tag below the workspace. The
tag follows the grammar and motif counter arrays, whereas the auxiliary
histogram descriptor immediately precedes those arrays. Thus neither a tag
transfer nor a write in the compression workspace changes the shadow length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrimedInputRAM LiveAuxiliaryHeaders PairSimulation
open CompressorRecords.SourceTransport
open scoped Fin.CommRing

/-- Physical address of the auxiliary histogram descriptor's target word. -/
abbrev histogramCell (G : Group) := (terminalOperands G 4 - 1).val

theorem histogramCell_lt_tag (G : Group)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) :
    histogramCell G < (PairTag.address (terminalOperands G)).val := by
  have hp : shadowBase G ≤ (Layout.pairWorkspace G.constants).eval G.g := by
    change _ ≤ shadowBase G + _
    omega
  have hcs := counter_end_le_shadow G
  obtain ⟨_,_,ht,_⟩ := geometry_order G
  have hd : (desc G).val = tableBase G := Nat.mod_eq_of_lt (show tableBase G < 2^G.w by omega)
  have hv : (Pieces.word G.g G.lit (.geometry (Layout.oldState G.constants))).val =
      counterBase G + G.constants.labels.eval G.g := Nat.mod_eq_of_lt (show counterBase G + G.constants.labels.eval G.g < 2^G.w by omega)
  unfold histogramCell
  rw [histogramTargetAddress, LiveAuxiliaryDescriptorInit.address_val _ (by omega), hd,
    CompressedPair.tag_address, hv]
  change tableBase G + 20 < _
  omega

/-- Literal report emitted by the outer pair linker, including its transfer
when a source stage accepts. -/
theorem histogramCell_report (G : Group)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w) (stage : CompressedPair.Stage)
    (rep : Report G.w) (m : Memory G.w) (source : after m rep.events (histogramCell G) = m (histogramCell G)) :
    after m (CompressedPair.report (terminalOperands G) stage rep).events (histogramCell G) =
      m (histogramCell G) := by
  rw [(CompressedPair.report_effect (terminalOperands G) stage rep m).2.2.2]
  cases rep.result <;> cases CompressedPair.next stage <;> first
    | exact source
    | exact (ite_eq_right (histogramCell_lt_tag G fit).ne).trans source

/-- Each source report writes in the workspace. The actual chronological
sequence may transfer the pair tag arbitrarily many times. -/
theorem histogramCell_reports (G : Group)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (rs : List (CompressedPair.Stage × Report G.w)) (m : Memory G.w)
    (source : ∀ q ∈ rs, Writes ((terminalOperands G 2).val ≤ ·) q.2.events) :
    after m (eventLog (rs.map (fun q => CompressedPair.report (terminalOperands G) q.1 q.2))) (histogramCell G) =
      m (histogramCell G) := by
  induction rs generalizing m with
  | nil => rfl
  | cons q rest ih =>
    rw [List.map_cons, eventLog, List.flatMap_cons, after, List.foldl_append]
    refine (ih _ (fun r hr => source r (.tail _ hr))).trans ?_
    exact histogramCell_report G fit q.1 q.2 m
      (after_outside m (source q (.head _)) (histogramTarget_lt_workspace G fit).not_ge)

variable {G : Group} {m : Memory G.w} {i : Fin (2^(sizes G).h)}
  {hdr : Header (pairLengths G i) → Bool}
  {N : Indexed G Stage.nominations m (Nominations.Nom G)} {μ : Nominations.Nom G}

theorem PreparedBranch.shadowSpan_of_cell (B : PreparedBranch G m i hdr N μ) {mem : Memory G.w}
    (cell : mem (histogramCell G) = B.copy.memory () (histogramCell G)) :
    TerminalBootstrap.shadowSpan (terminalOperands G) mem =
      ((span (pairLengths G i) (histLength G) : ℕ) : Word G.w) := by
  rw [← B.shadowSpan]
  unfold TerminalBootstrap.shadowSpan
  rw [cell]

theorem PreparedBranch.shadowSpan_after_reports (B : PreparedBranch G m i hdr N μ)
    (fit : (Layout.pairWorkspace G.constants).eval G.g < 2^G.w)
    (rs : List (CompressedPair.Stage × Report G.w))
    (source : ∀ q ∈ rs, Writes ((terminalOperands G 2).val ≤ ·) q.2.events) :
    TerminalBootstrap.shadowSpan (terminalOperands G)
      (after (B.copy.memory ()) (eventLog (rs.map (fun q => CompressedPair.report (terminalOperands G) q.1 q.2)))) =
      ((span (pairLengths G i) (histLength G) : ℕ) : Word G.w) :=
  B.shadowSpan_of_cell (histogramCell_reports G fit rs _ source)

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
