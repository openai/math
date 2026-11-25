import OAI.Hierarchy.DescentOrdinaryRawPublish
import OAI.Hierarchy.DescentOrdinaryEdgeTape

namespace OAI
/-! # Each physical wire's true source, target, width, retention and subdivision count at the emitted row -/

namespace Hierarchy.DescentOrdinaryRawRows
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentSixParty GadgetNetwork Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical
noncomputable section
variable {F I P : Type} [Field F] [Fintype I] [DecidableEq I] {d w n : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (S : Sources) (O : Output) (pick : I×Fin 2↪W.graph.Edge) (z : ℕ) (profile : I→Profile G.C)
variable (owner : GadgetNetwork.Site (I:=I) W.graph→ℕ)
variable (edge : W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (site : W.graph.Site↪ℕ)
variable (pair : I≃Fin n) (code : I→ℕ) (m : Memory w)
local notation "valAt" => truth W.graph G pick z profile owner W.core
local notation "ne" => Fintype.card W.graph.Edge

omit [DecidableEq I] in
theorem native_rows (f : Column) (room : Bounds S O G.b f w n ne)
    (full : Inputs W.graph G S pick z profile owner edge site W.core pair code m)
    (bitsRoom : 1<2^w) :
    ∃out : Memory w,(sweep S O G.b f w n ne 10).Exec m out (work S O G.b f n ne 10) ∧
      (∀a<O.base,out a=m a) ∧
      ∀e : GadgetNetwork.Edge (I:=I) W.graph,
        out (O.base+MarkedWorld.edgeNumber W edge pair e)=(valAt f e:Word w) := by
  let oldWord (i : Fin ne) : Word w:=valAt f (.inl (edge.symm i))
  let newWord (s : Born) (i : Fin n) : Word w:=valAt f (s.edge W.graph (pair.symm i))
  have org (i : Fin ne) : (S.old G.b f).eval m i.val=oldWord i := by
    simpa [oldWord] using old_values W.graph G S pick z profile owner edge site W.core pair code m full bitsRoom f (edge.symm i)
  have extra (s : Born) (i : Fin n) : (S.born G.b s f).eval m i.val=newWord s i := by
    simpa [newWord] using born_values W.graph G S pick z profile owner edge site W.core pair code m full f s (pair.symm i)
  obtain ⟨run,ok⟩:=publish S O G.b f oldWord newWord m room org extra 10 (by decide)
  refine ⟨_,run,ok.before,?_⟩
  rintro (e|⟨i,s⟩|⟨i,s⟩)
  · simpa [oldWord,MarkedWorld.edgeNumber] using ok.original (edge e)
  · simpa [newWord,Born.edge,Born.index,addr,MarkedWorld.edgeNumber,Nat.add_assoc] using
      read_born O oldWord newWord m ok (.arm s) (pair i)
  · simpa [newWord,Born.edge,Born.index,addr,MarkedWorld.edgeNumber,Nat.add_assoc] using
      read_born O oldWord newWord m ok (.supply s) (pair i)

end
end Hierarchy.DescentOrdinaryRawRows

end OAI
