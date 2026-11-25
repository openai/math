import OAI.Computability.BorderVNP.ShortenEnrichedNamedProgram

/-! # Stage-wide seed numbering in the work circuit's physical rectangle

The selected geometric compiler fixes one seed code before all child states
and guesses. Its image gives the precise birth rows used by the arithmetic
work circuit. Densely saving cables retains every site row, including holes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Shortening Epoch Epoch.Round Shortening.StaticRows Shortening.PublicParallel Cover
open PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m b k : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes) (i : Fin b)

local notation3 "Seeds" => Shortening.PublicDenseReceipt.Seed (src.pattern i).bins (src.asPath.depth last high (i.val+1))

private theorem seedCard : r.seedCount i = Fintype.card Seeds := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (r.seedCode i)).symm

/-- The single common static seed enumeration for all site and cable emitters
at this stage, expressed in the true cardinality of its type. -/
noncomputable def directorySeed : Seeds ≃ Fin (Fintype.card Seeds) :=
  (r.seedCode i).trans (finCongr (seedCard r i))

/-- Both returned directories use this one code for every physical branch. -/
theorem directorySeed_spec (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) :
    (∀ v, ((r.directory i c q).sites v).val = (siteRows e (r.program.stage i c).input
      (parallelName fun j => (c j).val.names.sites) (r.directorySeed i).toEmbedding v).val) ∧
    ∀ z, ((r.directory i c q).cables z).val =
      (r.program.stage i c).cableNumber e (r.directorySeed i).toEmbedding q z :=
  by
    have castSpec {n : ℕ} (code : Seeds ≃ Fin n) (hn : n = Fintype.card Seeds)
        (old : (∀ v, ((r.directory i c q).sites v).val = (siteRows e (r.program.stage i c).input
          (parallelName fun j => (c j).val.names.sites) code.toEmbedding v).val) ∧
          ∀ z, ((r.directory i c q).cables z).val = (r.program.stage i c).cableNumber e code.toEmbedding q z) :
        (∀ v, ((r.directory i c q).sites v).val = (siteRows e (r.program.stage i c).input
          (parallelName fun j => (c j).val.names.sites) (code.trans (finCongr hn)).toEmbedding v).val) ∧
          ∀ z, ((r.directory i c q).cables z).val =
            (r.program.stage i c).cableNumber e (code.trans (finCongr hn)).toEmbedding q z := by
      subst n
      exact old
    exact castSpec (r.seedCode i) (seedCard r i) (r.numbered i c q)

/-- Recover the stage-wide seed ordering in the rectangle of its actual
cardinality. The natural row assertion holds for every selected child tuple
and every branch, simultaneously. -/
theorem fixed_birth_rows :
    ∃ code : Seeds ≃ Fin (Fintype.card Seeds),
      ∀ (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val) q v,
        ((r.directory i c q).sites v).val =
          (siteRows e (r.program.stage i c).input (parallelName fun j => (c j).val.names.sites) code.toEmbedding v).val :=
  ⟨r.directorySeed i,fun c q => (r.directorySeed_spec i c q).1⟩

/-- The physical site embedding after a dense save has exactly the work
compiler's indexing, now with the scheduled successor rectangle's type. -/
theorem fixed_birth_directory
    (rect : V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card Seeds)) :
    ∃ code : Seeds ≃ Fin (Fintype.card Seeds),
      ∀ (c : Fin k → NamedState.Admissible (src.NamedGood last high V E w cap keep) i.val) q,
        ((r.directory i c q).dense.sites.trans (finCongr rect).toEmbedding) =
          siteRows e (r.program.stage i c).input (parallelName fun j => (c j).val.names.sites) code.toEmbedding := by
  obtain ⟨code,hcode⟩ := r.fixed_birth_rows i
  refine ⟨code,fun c q => DFunLike.ext _ _ fun v => Fin.ext ?_⟩
  exact hcode c q v

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
