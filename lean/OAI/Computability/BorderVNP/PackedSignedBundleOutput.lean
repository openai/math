import OAI.Computability.BorderVNP.CellPacketGeometryProfileReturn
import OAI.Computability.BorderVNP.PackedBundleRoutingReturn
import OAI.Computability.BorderVNP.CrossingParallelFrame

/-! # Publishing and reading the two sorted bundle-header banks after the signed cell packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open Crossing Packing Packing.BottomReports RoutingISA VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM
open RoutingISA.Evaluator GeometryFrameEncoding ParseBatchSort Packing.CellAddressCircuit
set_option maxHeartbeats 800000
set_option maxRecDepth 4200

variable {Γ : Type} [Fintype Γ] {o extra w : ℕ}

/-- Consecutive output words from two frames over the same public input.
Adding the second field preserves every address of the first. -/
noncomputable def appendWords (first : Frame Γ (Fin o × Fin w)) (second : Frame Γ (Fin extra × Fin w)) :
    Frame Γ (Fin (o+extra) × Fin w) :=
  (parallelFrame first second).select fun z =>
    Fin.addCases (fun i => Sum.inl (i,z.2)) (fun i => Sum.inr (i,z.2)) z.1

theorem appendWords_size (first : Frame Γ (Fin o × Fin w)) (second : Frame Γ (Fin extra × Fin w)) :
    (appendWords first second).size = first.size+second.size := by
  simp [appendWords,parallelFrame_size]

theorem appendWords_first (first : Frame Γ (Fin o × Fin w)) (second : Frame Γ (Fin extra × Fin w))
    (x : Γ → Bool) (i : Fin o) (b : Fin w) :
    (appendWords first second).eval x (i.castAdd extra,b) = first.eval x (i,b) := by
  simp only [appendWords,Frame.select_eval,Fin.addCases_left,parallelFrame_eval_inl]

theorem appendWords_second (first : Frame Γ (Fin o × Fin w)) (second : Frame Γ (Fin extra × Fin w))
    (x : Γ → Bool) (i : Fin extra) (b : Fin w) :
    (appendWords first second).eval x (Fin.natAdd o i,b) = second.eval x (i,b) := by
  simp only [appendWords,Frame.select_eval,Fin.addCases_right,parallelFrame_eval_inr]

end PackedHistoryCircuit.Retained

namespace PackedHistoryCircuit

open Crossing Packing Packing.BottomReports RoutingISA VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM
open RoutingISA.Evaluator GeometryFrameEncoding ParseBatchSort Packing.CellAddressCircuit
set_option maxHeartbeats 800000
set_option maxRecDepth 4200

variable {X Y V Z : Type} [Fintype X] [Fintype Y] [Fintype V] [Fintype Z]
    {reserve active o w J s m n d k b : ℕ} (hist : Frame (X ⊕ Y) (V ⊕ Unit)) (ord : Y ≃ Fin active)
    (fit : active≤reserve) (x : X → Bool) (word : Fin reserve → Bool)
    (first : Frame ((X ⊕ Fin reserve) ⊕ V) (Fin o × Fin w)) (src : Frame ((X ⊕ Fin reserve) ⊕ V) Z)
    (banks : CellBanks.Layout) (F : Fields s m n banks.cells d k w Z)
    (old : Fin J → Fin s) (desc gap : ℕ) (shape : Fin J → BundleSort.Shape) (valid : Frame Z Unit)

local notation3 (prettyPrint := false) "bankWords" => (BundleSort.headerBanks banks F b old desc gap shape valid).subst src
local notation3 (prettyPrint := false) "both" => Retained.appendWords first bankWords
local notation3 (prettyPrint := false) "input" => Retained.branch hist ord fit x word
local notation3 (prettyPrint := false) "prepared" => BundleSort.source banks.cells b
  (BundleSort.geometryHeaders F old desc (BundleSort.bankConfig banks gap valid) shape)

/-- The same physical path publishes the unchanged cell packet, the sorted
header payload and its inverse marker ranks. Reconstruction has the same
running time, original private choices and preserved lower memory in both
components of this conclusion. -/
theorem ProfilePaths.split_headerBanks
    {CodeBits native time dest : ℕ} {code : Code} {pub : Arg → Word native} {mac : TeamOpcode.Macros native 8}
    {bank : RoutingISA.Bank native} {mem : Memory native} {ok : Prop} {resident : (Fin CodeBits → Bool) → Memory native → Prop}
    (paths : ProfilePaths code CodeBits pub mac bank mem ok time dest (emittedWords hist ord fit both x word) resident) :
    ProfilePaths code CodeBits pub mac bank mem ok time dest (emittedWords hist ord fit first x word) resident ∧
      ∀ (run : Returns code pub mac bank mem) (i : Fin (2^b+2^b)),
        readings run.val.2.2 (dest+o+i.val) = value (fun t =>
          (CellPacketGeometry.geometry prepared).eval (src.eval input) (.inl (i,t))) := by
  constructor
  · refine ⟨paths.passes,fun good => ?_,paths.memory⟩
    obtain ⟨E,all⟩ := paths.outputs good
    refine ⟨E,fun g => ⟨(all g).1,(all g).2.1,(all g).2.2.1,fun i => ?_⟩⟩
    have read := (all g).2.2.2 (i.castAdd (2^b+2^b))
    simpa only [emittedWords,Fin.val_castAdd,Retained.appendWords_first] using read
  · intro path i
    have read := paths.words_of_return path (Fin.natAdd o i)
    simpa only [emittedWords,Fin.val_natAdd,Retained.appendWords_second,Frame.subst_eval,BundleSort.headerBanks,
      Frame.select_eval,Retained.branch,Nat.add_assoc] using read

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
