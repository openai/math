import OAI.Hierarchy.DescentResetStemMaskedPorts

namespace OAI
/-! # Read only the actual old vertex selected by the occupied reset row -/
namespace Hierarchy.DescentResetStemMaskedPorts
open ProtocolRAM DescentPackedColony DescentResetStemTemplatePorts Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {V : Type*} {w oldH palette count : ℕ}

def priorHub (rank : V↪Fin oldH) (isHub : V→Bool) (j : Fin oldH) : Bool :=
  if h : ∃v,rank v=j then isHub h.choose else false

@[simp] theorem priorHub_at (rank : V↪Fin oldH) (isHub : V→Bool) (v : V) :
    priorHub rank isHub (rank v)=isHub v := by
  have hit : ∃u,rank u=rank v:=⟨v,rfl⟩
  rw [priorHub,dite_eq_left hit,rank.injective hit.choose_spec]

/-- Active compact parents address genuine previous vertices. The previous public
hub column is pulled from the same tape through the low-address frame. -/
theorem stored_active (B : Banks) (number : Bank) (here : Fin count→Fin (oldH*palette))
    (rank : V↪Fin oldH) (origin : Fin count→V)
    (near : Fin (oldH*palette)→Fin 3→Option (Fin (oldH*palette))) (isHub : V→Bool) (prior entry : Memory w)
    (low : ∀v, entry (B.hub.base+(rank v).val)=prior (B.hub.base+(rank v).val))
    (words : ∀v,prior (B.hub.base+(rank v).val)=((isHub v).toNat:Word w))
    (measured : entry number.base=(count:Word w))
    (raw : ∀r,entry (B.here.base+r.val)=((here r).val:Word w))
    (roots : ∀r,entry (B.parent.base+r.val)=((rank (origin r)).val:Word w))
    (adjacent : ∀i v,entry ((B.neighbors i).base+v.val)=(target (near v i):Word w)) :
    Stored B number here (fun r=>rank (origin r)) near (priorHub rank isHub) entry := by
  refine ⟨measured,raw,roots,adjacent,fun r=>?_⟩
  rw [priorHub_at]
  exact (low (origin r)).trans (words (origin r))

end
end Hierarchy.DescentResetStemMaskedPorts

end OAI
