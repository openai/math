import OAI.Computability.BorderVNP.ShortenCompiledAt
import OAI.Computability.BorderVNP.ShortenDenseTemplates
import OAI.Computability.BorderVNP.ShortenDenseSourceReceipts

/-!
# Source-visible stage templates for the native physical allocator

The finite bin system, Hecke word length, compiled candidate ordering and
deviation coefficient are chosen before the input packs or quotient depth.
The motion frames and the quantitative stage calibration use exactly the
same coefficient. A decoded child tuple can use its own labels and actual
wire-selected samples and receive a receipt on that exact stable ordering.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Cover Cover.Frame Hecke Shortening Shortening.Framed Packing
open scoped Classical BorderVNP.Epoch.Cube

universe u

variable {D m : ℕ} [NeZero D] {K : Type u} [Field K]

/-- A native source stage and its quantitative certificates. The compiled
motion coefficient used by the recurrence is the one actually certified
for the frame's returned samples. -/
structure SourceTemplate (e : PaidIdentity K D m) (h H ν : ℝ) (S : Finset (HyperbolicHost (Cube D))) where
  /-- Signed center and direction tolerance of this finite bin system. -/
  tolerance : ℝ
  /-- Actual finite relative bins and canonical lookup charts. -/
  bins : PreparedBins D S h tolerance
  /-- Prepared sample word length. -/
  word : ℕ
  /-- Lowest admissible output level. -/
  floor : ℕ
  /-- The compiled deck trace is defined at positive output depths. -/
  floor_pos : 0 < floor
  /-- Constant controlling the true mean's Euclidean norm. -/
  mean : ℝ
  /-- Nonnegativity required in the quantitative recurrence. -/
  mean_nonneg : 0 ≤ mean
  /-- The exact radius constant supplied by the native sample circuit. -/
  motion : ℕ
  /-- The uniform per-step factor for both types of site record. -/
  record : ℕ
  /-- Quantified physical circuit guarantee for this very word length and radius. -/
  compiled : PreparedBins.CompiledAt.{u} bins word motion
  /-- Install on the actual decoded labels, selected samples and stable row embedding.
  The returned step determines both measured rows and all outgoing site records. -/
  run_selected : ∀ d ≥ floor, ∀ {k rows : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*word)), (∀ i, Catalog.PlacedAt S h (child i)) →
      ∀ (L : PreparedBins.Labels bins (fun i => (child i).pack) (fun i => (child i).active)
        (PreparedBins.childSites child))
      (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) word)
      (slot : (raw child).layout.Edge ↪ Fin rows), bins.SampleDeviation child L ω hk motion →
      ∃ s : Stage m bins.Bin d child, Nonempty (bins.DenseReceipt e child L ω slot s hk H ν mean motion record)

variable {e : PaidIdentity K D m} {h H ν : ℝ} {S : Finset (HyperbolicHost (Cube D))}

namespace SourceTemplate

variable (src : SourceTemplate e h H ν S)

/-- The public source stage supplies a concrete sorted crossing for each
child tuple and row injection. One may alternatively invoke its
`run_selected` with labels and samples read from a shared upstream frame. -/
theorem realize (d : ℕ) (hd : src.floor ≤ d) {k rows : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
    (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*src.word)) (prep : ∀ i, Catalog.PlacedAt S h (child i))
    (slot : (raw child).layout.Edge ↪ Fin rows) :
    ∃ (L : PreparedBins.Labels src.bins (fun i => (child i).pack) (fun i => (child i).active)
      (PreparedBins.childSites child))
      (ω : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) src.word)
      (s : Stage m src.bins.Bin d child),
        Nonempty (src.bins.DenseReceipt e child L ω slot s hk H ν src.mean src.motion src.record) := by
  obtain ⟨L⟩ := src.bins.exists_childLabels child (fun i => (prep i).sites) (fun i => (prep i).short)
  obtain ⟨ω,hdev⟩ := src.bins.physical_choice src.compiled (src.floor_pos.trans_le hd) hk child L
    (fun i => (prep i).midpoint)
  exact ⟨L,ω,src.run_selected d hd hk child prep L ω slot hdev⟩

/-- Geometric stage view used by the recurrence. Its bin and its successor
catalog are the actual native data of this source template. -/
noncomputable def asTemplate : StageTemplate e (Cube D) h H ν S where
  Bin := src.bins.Bin
  nextSites := src.bins.successorSites src.word e
  word := src.word
  floor := src.floor
  meanFactor := src.mean
  motionFactor := src.motion
  nonneg := ⟨src.mean_nonneg,Nat.cast_nonneg _⟩
  run := by
    intro d hd k hk P bits child prep rows slot
    obtain ⟨L,ω,s,⟨receipt⟩⟩ := src.realize d hd hk child prep slot
    refine ⟨s,?_,?_,⟨receipt.measure⟩,receipt.closure⟩
    · rw [receipt.trace.realizes]; rfl
    · intro c; rw [receipt.trace.realizes]; rfl

end SourceTemplate

/-- All geometric, record and compiled-sample parameters come from the
same prepared finite bin system. -/
theorem sourceTemplate_of_bins (e : PaidIdentity K D m) {η θ : ℝ} (B : PreparedBins D S h η)
    (hm : 0 < m) (hh : 0 ≤ h) (hH : h ≤ H) (ht : 0 ≤ θ) (hθ : θ ≤ ν) (hsafe : θ ≤ 4) (hη : η ≤ θ/4) :
    Nonempty (SourceTemplate e h H ν S) := by
  obtain ⟨n,l,C,u,hu,hl,run⟩ := (B.eventually_dense_receipts e hm hh hH ht hθ hsafe hη).exists
  obtain ⟨N,compiled⟩ := PreparedBins.exists_compiledAt.{u} B n
  exact ⟨{
    tolerance := η
    bins := B
    word := n
    floor := l
    floor_pos := hl
    mean := u
    mean_nonneg := hu
    motion := N
    record := C
    compiled := compiled
    run_selected := fun d hd {_ _} hk {_ _} child prep L ω slot dev =>
      run d hd hk child prep L ω slot N dev }⟩

/-- Source path retaining all true bin, motion frame and record interfaces. -/
abbrev SourcePath (b : ℕ) (e : PaidIdentity K D m) (h H ν : ℝ) :=
  Adaptive.PreparedPath b (SourceTemplate e h H ν) (fun _ src => src.bins.successorSites src.word e)

/-- Projecting the path into its geometric recurrence view retains exactly
the source bins and public samples at each index. -/
noncomputable def SourcePath.asPath {b : ℕ} (path : SourcePath b e h H ν) :
    StagePath b e (Cube D) h H ν :=
  ⟨path.catalog,fun i => (path.pattern i).asTemplate,path.next⟩

/-- A fixed short radius and a source-visible path for every finite round count
and every initial relative catalog, before the fan-in and quotient depth. -/
theorem exists_source_path (e : PaidIdentity K D m) (hm : 0 < m) (hH : 0 < H) (hν : 0 < ν) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1/8 ∧ ∀ b (S : Finset (HyperbolicHost (Cube D))),
      ∃ path : SourcePath b e h H ν, path.catalog 0 = S := by
  let θ := min ν 1
  have ht : 0 < θ := lt_min hν zero_lt_one
  let η := θ/4
  obtain ⟨h₀,hp,charts⟩ := exists_preparedBins (D := D) (show 0 < η from div_pos ht (by norm_num))
  let h := min (min H h₀) (1/8)
  have hh : 0 < h := lt_min (lt_min hH hp) (by norm_num)
  have small : h ≤ min H h₀ := min_le_left ..
  refine ⟨h,hh,min_le_right ..,?_⟩
  intro b S
  apply Adaptive.exists_prepared_path
  intro S'
  obtain ⟨B⟩ := charts h ⟨hh,small.trans (min_le_right ..)⟩ S'
  exact sourceTemplate_of_bins e B hm hh.le (small.trans (min_le_left ..)) ht.le (min_le_left ..)
    ((min_le_right ν 1).trans (by norm_num)) le_rfl

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
