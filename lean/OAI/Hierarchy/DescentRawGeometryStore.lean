import OAI.Hierarchy.DescentOrdinaryRawFields
import OAI.Hierarchy.DescentRawFieldBudget

namespace OAI
/-! # The five resident native columns of the chosen physical marked world -/

namespace Hierarchy.DescentOrdinaryRawRows.Five
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentSixParty GadgetNetwork Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical
noncomputable section
variable {F I P : Type} [Field F] [Fintype I] [DecidableEq I] {d w n : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F) (S : Sources)
variable (pick : I×Fin 2↪W.graph.Edge) (z : ℕ) (profile : I→Profile G.C)
variable (owner : GadgetNetwork.Site (I:=I) W.graph→ℕ)
variable (edge : W.graph.Edge≃Fin (Fintype.card W.graph.Edge)) (site : W.graph.Site↪ℕ)
variable (pair : I≃Fin n) (code : I→ℕ) (m : Memory w)
local notation "valAt" => truth W.graph G pick z profile owner W.core
local notation "ne" => Fintype.card W.graph.Edge

omit [DecidableEq I] in
theorem geometry (lens : Padded.Counts) (base oc pc : ℕ) (room : Bounds S lens G.b w base oc pc)
    (source : Inputs W.graph G S pick z profile owner edge site W.core pair code m) (wide : 1<2^w)
    (oldFit : ne≤oc) (pairFit : n≤pc) (oldCount : m lens.old=(ne:Word w)) (pairCount : m lens.pairs=(n:Word w)) :
    ∃o,(program S lens G.b w base oc pc 5).Exec m o (steps S lens G.b base oc pc 5) ∧
      (∀a, a<base→ o a=m a) ∧
      (∀f e,o ((output base oc pc (index f)).base+MarkedWorld.edgeNumber W edge pair e)=(valAt f e:Word w)) ∧
      (∀ f j,ne+10*n≤j→j<capacity oc pc→ o ((output base oc pc (index f)).base+j)=0) := by
  let org (f : Column) (i : Fin ne) : Word w:=valAt f (.inl (edge.symm i))
  let add (f : Column) (s : Born) (i : Fin n) : Word w:=valAt f (s.edge W.graph (pair.symm i))
  have original (f : Column) (i : Fin ne) : (S.old G.b f).eval m i.val=org f i := by
    simpa [org] using old_values W.graph G S pick z profile owner edge site W.core pair code m source wide f (edge.symm i)
  have fresh (f : Column) (s : Born) (i : Fin n) : (S.born G.b s f).eval m i.val=add f s i := by
    simpa [add] using born_values W.graph G S pick z profile owner edge site W.core pair code m source f s (pair.symm i)
  obtain ⟨o,exec,done⟩:=publish S lens G.b w base oc pc org add m room oldFit pairFit oldCount pairCount original fresh 5 le_rfl
  refine ⟨o,exec,done.frame,?_,fun f j lo hi=>done.padding (index f) (index_lt f) j lo hi⟩
  intro f e
  rcases e with e|⟨i,j⟩|⟨i,j⟩
  · simpa [org,MarkedWorld.edgeNumber] using done.original (index f) (index_lt f) (edge e)
  · simpa [add,Born.edge,Born.index,MarkedWorld.edgeNumber,addr,Nat.add_assoc] using
      done.fresh (index f) (index_lt f) (.arm j) (pair i)
  · simpa [add,Born.edge,Born.index,MarkedWorld.edgeNumber,addr,Nat.add_assoc] using
      done.fresh (index f) (index_lt f) (.supply j) (pair i)

end
end Hierarchy.DescentOrdinaryRawRows.Five

end OAI
