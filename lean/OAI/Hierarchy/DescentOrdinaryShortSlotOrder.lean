import OAI.Hierarchy.DescentParentGroupSlot
import OAI.Hierarchy.DescentOrdinaryDonorOrder

namespace OAI
/-! # Ordering original positive donor slots within one old group -/
namespace Hierarchy.DescentRawCablePanel
open DescentSharedCableNames DescentCableDonorNames DescentSixParty DescentPacking
open DescentStageEdgeReceipt
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {I F P J V : Type} [Fintype I] [DecidableEq I] [Field F] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {d k H age : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {price ε : ℝ} (A : GroupStage W G price ε J V k)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age) (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))
    (name : V↪Fin H) (groups : J↪ℕ)
local notation "dense" u:arg => (name (A.pos u).2).val*2^k+(A.block u).val
variable (named : A.SiteNamed (groupRank groups (name.trans Fin.valEmbedding)))

include named ready in
private theorem source_rank {u v : W.graph.Site} (group : (A.pos u).1=(A.pos v).1) :
    (dense u<dense v ↔ originalId W.graph.Site u<originalId W.graph.Site v) :=by
  let num:=A.siteFrom (groupRank groups (name.trans Fin.valEmbedding)) ready.coordinates
  have ids (x : W.graph.Site) : originalId W.graph.Site x=(DescentPhysicalOrder.physical num x).val :=
    (named x).trans (DescentPhysicalOrder.physical_val num x).symm
  rw [ids,ids]
  change _ ↔ DescentPhysicalOrder.physical num u < DescentPhysicalOrder.physical num v
  rw [DescentPhysicalOrder.physical_lt_iff]
  change _ ↔ (groups (A.pos u).1*DescentStageEdgeReceipt.pitch (name.trans Fin.valEmbedding)+(name (A.pos u).2).val)*2^k+(A.block u).val <
    (groups (A.pos v).1*DescentStageEdgeReceipt.pitch (name.trans Fin.valEmbedding)+(name (A.pos v).2).val)*2^k+(A.block v).val
  rw [group]
  simp only [Nat.add_mul,Nat.add_assoc,Nat.add_lt_add_iff_left]

variable (pick : I×Fin 2↪W.graph.Edge)
local notation "rack" e:arg => (shortSlot A S ready (edge.trans Fin.valEmbedding) name pick e).1
local notation "offset" e:arg => (shortSlot A S ready (edge.trans Fin.valEmbedding) name pick e).2
local notation "site" e:arg => W.graph.src (anchor pick (e).val)
local notation "oid" e:arg => originalId W.graph.Site (site e)
local notation "old" e:arg => edge (anchor pick (e).val)
local notation "out" e:arg => Stage.outgoing A (edge.trans Fin.valEmbedding) S ready ⟨anchor pick (e).val,(e).property⟩
local notation "total" => 2^k*A.cap*11

omit [Fintype I] [DecidableEq I] in
private theorem short_value (e : Live A pick) :
    (rack e).val*(total)+(offset e).val=((dense (site e))*A.cap+(out e).val)*11+(role e.val).val :=by
  simp only [shortSlot,finProdFinEquiv_apply_val]
  ring

open private Hierarchy.DescentCableDonorNames.digit_eq from
  OAI.Hierarchy.DescentCableDonorNames

include named in
omit [Fintype I] [DecidableEq I] in
theorem shortSlot_order (e f : Live A pick) (group : birthGroup A pick e=birthGroup A pick f) :
    (rack e<rack f ∨ rack e=rack f ∧ offset e<offset f) ↔
      (oid e<oid f ∨ oid e=oid f ∧ (old e<old f ∨ old e=old f ∧ role e.val<role f.val)) :=by
  change (A.pos (site e)).1=(A.pos (site f)).1 at group
  have siteLess:=source_rank A S ready name groups named group
  have siteMore:=source_rank A S ready name groups named group.symm
  have siteEq : dense (site e)=dense (site f) ↔ oid e=oid f :=by omega
  have flat : ((rack e).val*(total)+(offset e).val<(rack f).val*(total)+(offset f).val) ↔
      (rack e<rack f ∨ rack e=rack f ∧ offset e<offset f) :=by
    simpa only [Fin.lt_def,Fin.ext_iff] using
      (digit_lt (a:=(rack e).val) (b:=(rack f).val) (offset e).isLt (offset f).isLt)
  rw [←flat,short_value A S ready edge name pick e,short_value A S ready edge name pick f]
  rw [digit_lt (role e.val).isLt (role f.val).isLt,digit_lt (out e).isLt (out f).isLt,
    Hierarchy.DescentCableDonorNames.digit_eq (out e).isLt (out f).isLt,siteLess,siteEq]
  by_cases same : oid e=oid f
  · have sameSite:site e=site f:=(originalId _).injective same
    have lt₀:=Stage.outgoing_lt A (edge.trans Fin.valEmbedding) S ready
      ⟨anchor pick e.val,e.property⟩ ⟨anchor pick f.val,f.property⟩ sameSite
    have gt₀:=Stage.outgoing_lt A (edge.trans Fin.valEmbedding) S ready
      ⟨anchor pick f.val,f.property⟩ ⟨anchor pick e.val,e.property⟩ sameSite.symm
    change (out e).val<(out f).val ↔ (old e).val<(old f).val at lt₀
    change (out f).val<(out e).val ↔ (old f).val<(old e).val at gt₀
    have eq₀ : (out e).val=(out f).val ↔ old e=old f :=by rw [Fin.ext_iff];omega
    simp only [same,true_and,lt_self_iff_false,false_or,Fin.lt_def,lt₀,eq₀]
  · simp only [same,false_and,or_false]

end
end Hierarchy.DescentRawCablePanel

end OAI
