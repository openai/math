import OAI.Hierarchy.DescentNodeCellRolePage
import OAI.Hierarchy.DescentPaddedNodeCells
import OAI.Hierarchy.DescentScalarRoleCounts

namespace OAI
/-! Recover all original node counts, including uncharged sites, from the physical role page. -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler DescentSIMDLookup
open DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (ord : Local B)
  {H N a mb : ℕ} (name : cap.V↪Fin H) (faith : ∀v,(name v).val=(cap.vertex v).val)
  (label : NodeOrder.All B→Cell a) (active : ∀n,label n≠0)
include faith in
theorem role_at (v : W.graph.Site) (n : (B.recipe v).Node) (j : Fin N)
    (number : j.val=(ord v n).val) :
    (encode a N).symm (rolePage cap B ord label (cap.placement.block v) (name (cap.placement.pos v).2)
      (cap.placement.pos v).1) j=label ⟨v,n⟩:=by
  have hit:=(atPhysical_some cap B ord _ j _ _ v n).mpr ⟨(faith _).symm,rfl,rfl,number⟩
  simp only [rolePage,Equiv.symm_apply_apply,hit]
  rfl

include faith active in
theorem role_count_at (v : W.graph.Site) (fit : Fintype.card (B.recipe v).Node≤N) (room : N<2^mb) :
    (RoleCounts.count mb (rolePage (N:=N) cap B ord label (cap.placement.block v)
      (name (cap.placement.pos v).2) (cap.placement.pos v).1)).val=Fintype.card (B.recipe v).Node:=by
  let ids:=(ord v).toEmbedding.trans (Fin.castLEEmb fit)
  apply RoleCounts.exact_count ids _ _ room
  intro j
  simp only [rolePage,Equiv.symm_apply_apply]
  constructor
  · intro present
    cases h:atPhysical cap B ord (cap.placement.block v) j (name (cap.placement.pos v).2) (cap.placement.pos v).1 with
    | none=>simp [h] at present
    | some node=>
      obtain ⟨u,t⟩:=node
      obtain ⟨host,group,block,rk⟩:=(atPhysical_some cap B ord _ j _ _ u t).mp h
      have owner : u=v:=cap.valid.coordinates (Prod.ext (Prod.ext group
        (cap.vertex.injective (Fin.ext (host.trans (faith _))))) block)
      subst u
      exact ⟨t,Fin.ext rk.symm⟩
  · rintro ⟨t,rfl⟩
    have found:=(atPhysical_some cap B ord _ (ids t) _ _ v t).mpr ⟨(faith _).symm,rfl,rfl,rfl⟩
    rw [found]
    exact active ⟨v,t⟩

theorem role_count_empty (x : Block k) (h : Fin H) (g : Fin (S.groupCount age))
    (vacant : ¬∃u,cap.placement.block u=x ∧ (cap.vertex (cap.placement.pos u).2).val=h.val ∧ (cap.placement.pos u).1=g) :
    RoleCounts.count mb (rolePage (N:=N) cap B ord label x h g)=0:=by
  have absent j : atPhysical cap B ord x (j:Fin N) h g=none:=by
    cases hit:atPhysical cap B ord x j h g with
    | none=>rfl
    | some node=>
      obtain ⟨u,t⟩:=node
      obtain ⟨hv,grp,block,_⟩:=(atPhysical_some cap B ord x j h g u t).mp hit
      exact (vacant ⟨u,block,hv,grp⟩).elim
  have zero : rolePage (N:=N) cap B ord label x h g=0:=by
    apply Fin.ext
    change (finFunctionFinEquiv (fun j:Fin N=>(atPhysical cap B ord x j h g).elim (0:Cell a) label)).val=0
    simp [absent]
  rw [zero,RoleCounts.empty]

end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
