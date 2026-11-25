import OAI.Hierarchy.DescentResetStemPriorHub
import OAI.Hierarchy.DescentResetStemPaddedParent
import OAI.Hierarchy.DescentResetParentDirectoryRead

namespace OAI
/-! # Raw evidence, compact inverse, native predecessor and previous hub on the same tape -/
namespace Hierarchy.DescentSixParty.ResetInput
open DescentDenseHostOrder DescentCommonHost DescentDyadicSpan DescentPackedColony DescentResetStemMaskedPorts
open DescentResetParentAperture (parent)
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits} {price ε : ℝ}
    {h C height : ℕ} (Z : ResetInput A price ε h C height) (T : Terminals Z)
local notation "pool" => roster Z.graph (Z.k-T.commonDepth) height
set_option quotPrecheck false in
local notation "Vnew" => ↥(Z.commonNames T)
variable {H pad w : ℕ} (vertex : Z.V↪Fin H)
local notation "N" => H*(Finset.card pool)
local notation "raw" => rawHostRank Z T vertex
local notation "denseId" => denseHostRank Z T vertex
local notation "order" => DescentStageEdgeReceipt.dense (denseId)

def rawAtIndex (r : Fin (Fintype.card Vnew)) : Fin N :=raw ((order).symm r)

@[simp] theorem rawAtIndex_at (v : Vnew) : Z.rawAtIndex T vertex ((denseId) v)=raw v :=
  congrArg raw ((order).symm_apply_apply v)

def originAtIndex (r : Fin (Fintype.card Vnew)) : Z.V :=position Z.graph ((order).symm r).val

@[simp] theorem originAtIndex_at (v : Vnew) : Z.originAtIndex T vertex ((denseId) v)=position Z.graph v.val :=
  congrArg (fun u : Vnew=>position Z.graph u.val) ((order).symm_apply_apply v)

theorem parent_stored_chart (base : ℕ) (number flags inverse hub : Bank) (neighbors : Fin 3→Bank)
    (capacity : Fintype.card Vnew≤pad) (mem : Memory w) (isHub : Z.V→Bool) (network : Fin N→Fin 3→Option (Fin N))
    (old : flags.Fits w base) (rows : N≤flags.size) (room : DescentResetParentDate.endAddress base N pad<2^w)
    (bitmap : ∀j : Fin N,mem (flags.base+j.val)=if ∃v,raw v=j then 1 else 0)
    (countAt : mem number.base=(Fintype.card Vnew:Word w))
    (inverseAt : ∀v,mem (inverse.base+((denseId) v).val)=((raw v).val:Word w))
    (nearAt : ∀i v,mem ((neighbors i).base+v.val)=(target (network v i):Word w))
    (hubAt : ∀v,mem (hub.base+(vertex v).val)=((isHub v).toNat:Word w))
    (countLow : number.base<base) (inverseLow : inverse.base+Fintype.card Vnew≤base)
    (nearLow : ∀i,(neighbors i).base+N≤base) (hubLow : hub.base+H≤base) :
    let last:=DescentResetParentDate.memory base N pad (Finset.card pool) flags mem room
    let banks : DescentResetStemTemplatePorts.Banks:=⟨inverse,parent base N pad,neighbors,hub⟩
    DescentResetStemKeyReindex.Directory (parent base N pad).base (Z.parentIndex T vertex) last ∧
      Stored banks number (Z.rawAtIndex T vertex) (Z.parentIndex T vertex) network (priorHub vertex isHub) last ∧
      ∀j : Fin pad,Fintype.card Vnew≤j.val→last ((parent base N pad).base+j.val)=0 := by
  let vm:=DescentResetParentDate.memory base N pad (Finset.card pool) flags mem room
  have chips (j : Fin N) : mem (flags.base+j.val)=(DescentEdgeTapePrefix.row (fun _ : Vnew=>1) (fun v=>(raw v).val) j.val:Word w) := by
    rw [bitmap]
    by_cases occupied : ∃v,raw v=j
    · obtain ⟨v,hv⟩:=occupied
      subst j
      rw [ite_eq_left ⟨v,rfl⟩, DescentEdgeTapePrefix.row_present (fun _ : Vnew => 1)
        (fun u : Vnew => (raw u).val) (fun _ _ hit => (raw).injective (Fin.ext hit)) v]
      rfl
    · rw [ite_eq_right occupied,DescentEdgeTapePrefix.row_absent _ _ _ (fun v eqn=>occupied ⟨v,Fin.ext eqn⟩)]; rfl
  obtain ⟨previous,empty,frame⟩:=Z.bounded_parent_directory T vertex capacity base flags mem old rows room chips
  refine ⟨previous,?_,fun j unused=>empty j (fun ⟨v,at_⟩=>by
    have hit:=congrArg Fin.val at_
    change ((denseId) v).val=j.val at hit
    exact (Nat.not_lt_of_ge unused) (hit ▸ ((denseId) v).isLt))⟩
  apply stored_active (V:=Z.V) _ number (Z.rawAtIndex T vertex) vertex (Z.originAtIndex T vertex) network isHub mem vm
  · intro v
    exact frame _ (.inl ((Nat.add_lt_add_left (vertex v).isLt _).trans_le hubLow))
  · exact hubAt
  · exact (frame _ (.inl countLow)).trans countAt
  · intro j
    have h:=inverseAt ((order).symm j)
    have hi:((denseId) ((order).symm j)).val=j.val:=congrArg Fin.val ((order).apply_symm_apply j)
    rw [hi] at h
    exact (frame _ (.inl ((Nat.add_lt_add_left j.isLt _).trans_le inverseLow))).trans h
  · exact previous
  · intro i v
    exact (frame _ (.inl ((Nat.add_lt_add_left v.isLt _).trans_le (nearLow i)))).trans (nearAt i v)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
