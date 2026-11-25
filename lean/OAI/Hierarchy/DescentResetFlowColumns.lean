import OAI.Hierarchy.DescentPackedFlowStage
import OAI.Hierarchy.DescentResetIssuedWords
import OAI.Hierarchy.DescentResetContactRoster
import OAI.Hierarchy.DescentResetIssuedStencil

namespace OAI
/-! # The incoming and outgoing apertures use the same paid contact column -/
namespace Hierarchy.DescentSixParty.PackedFlow
open DescentGL DescentColonies DescentSIMDLookup DescentStageEdgeReceipt DescentIssuedFallbackPanel
open DescentPlainTerminal.Suffix
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m H R : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (groups : J≃Fin R) (hosts : V≃Fin H)

def portAt (v : V) (j : Fin A.degree) : Option V := (next A hosts (hosts v) j).map hosts.symm

theorem portAt_mem (v u : V) : u∈A.near v ↔ ∃j,portAt A hosts v j=some u := by
  constructor
  · intro hit
    refine ⟨socket A (hosts.toEmbedding.trans Fin.valEmbedding) v ⟨u,hit⟩,?_⟩
    simp [portAt,next_at]
  · rintro ⟨j,read⟩
    simp only [portAt,next] at read
    split at read
    · rename_i yes
      simp only [Option.map_some,Equiv.symm_apply_apply,Option.some.injEq] at read
      rw [← read]
      simpa only [Equiv.symm_apply_apply] using yes.choose.property
    · contradiction

theorem returned_pair (short : ℕ) (ok : A.degree<2^short) (digits : Block m≃J×Block k)
    (v u : V) (j : Fin A.degree) (read : portAt A hosts v j=some u) (x : Block m) :
    DescentPackedFlowPair.paid (next A hosts) (weights A native S ready groups hosts short)
      (hosts v) (groups (digits x).1) j (digits x).2=A.resetFlow digits v u x ∧
    DescentPackedFlowPair.paid (next A hosts) (weights A native S ready groups hosts short)
      (hosts v) (groups (digits x).1) j (digits x).2=A.resetFlow digits u v x := by
  have mem:=(portAt_mem A hosts v u).mpr ⟨j,read⟩
  have existsRaw : next A hosts (hosts v) j=some (hosts u) := by
    unfold portAt at read
    cases hit : next A hosts (hosts v) j with
    | none => simp [hit] at read
    | some z =>
      simp [hit] at read
      exact congrArg some ((hosts.symm_apply_eq.mp read))
  have same:=next_unique A hosts j _ existsRaw (next_at A hosts v ⟨u,mem⟩)
  rw [same]
  have val:=measured A native S ready groups hosts short ok digits v u mem x
  exact ⟨val,val.trans (A.mutual_reset_flow digits v u x)⟩

theorem actual_ports (sym : ∀v u,u∈A.near v→v∈A.near u) (v u : V) :
    u∈A.mutual v ↔ ∃j,portAt A hosts v j=some u := by
  rw [←portAt_mem A hosts v u]
  constructor
  · intro z;exact (Finset.mem_filter.mp z).1
  · intro z;exact Finset.mem_filter.mpr ⟨z,sym _ _ z⟩

end
end Hierarchy.DescentSixParty.PackedFlow

end OAI
