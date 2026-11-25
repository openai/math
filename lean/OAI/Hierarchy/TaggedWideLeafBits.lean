import OAI.Hierarchy.TaggedWideLeafContraction
import OAI.Hierarchy.TaggedWideOutputRecords

namespace OAI
/-! # Decoded bits of the original reported row at either physical end -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical

def stageKey (height m : ℕ) : Fin (m+1) ↪ ℕ×ℕ :=
  ⟨fun t=>(height,t.val),fun _i _j eqn=>Fin.ext (congrArg Prod.snd eqn)⟩

variable {F : Type*} [Field F] {N groups ports lanes height w m : ℕ}
    (raw : Fin N→ProtocolRAMEmit.Row) (positive : Fin N→Prop) (stage : Fin N→ℕ)
private abbrev liveRecord (rs : Fin N→ProtocolRAMEmit.Row) (w : ℕ) :=
  {i : Fin N // 0<pieces rs w i}

variable (s : ∀ t : Fin (m+1),Installed F groups ports lanes w m t.val (atScale positive stage height raw))
    (id : Function.Injective fun i=>(atScale positive stage height raw i).link) (port : Bool→Fin N→Fin ports)
    (same : ∀t,(s t).port=port)
    (anchor : (liveRecord (atScale positive stage height raw) w) × Bool ↪ Fin groups × Fin ports)
    (owner : ∀i b,(anchor (i,b)).1.val=(atScale positive stage height raw i.val).group)
    (pin : ∀i b,(anchor (i,b)).2=port b i.val) (room : ∀i,pieces (atScale positive stage height raw) w i≤lanes)

include id port same owner pin room

private theorem same_place (t : Fin (m+1)) :
    (s t).bank.place=placedRecord (atScale positive stage height raw) w m id port anchor owner pin room t := by
  funext g side
  apply Function.Embedding.ext
  intro u
  apply Fin.ext
  let v := (common (atScale positive stage height raw) w m t.val g.val id).symm u
  change (fixedSlot le_rfl ((s t).port side v.1.val,v.2.castLE ((s t).room _))).val =
    (fixedSlot le_rfl (port side v.1.val,v.2.castLE (room _))).val
  rw [same]

theorem decoded_original (hw : 0<w) (a : (i:Fin N)→Fin (2^(raw i).width))
    (r : liveRecord (atScale positive stage height raw) w) (side : Bool) (j : Fin (atScale positive stage height raw r.val).width) :
    positivePlane (fun t : Fin (m+1)=>⌈dyadic t.val*w⌉₊) (voltage (banks s) (placed (banks s)
      (publicLabels (stageKey height m) raw positive stage s a))) (anchor (r,side)) j.val =
      (a r.val).val.testBit j.val := by
  let word (r : liveRecord (atScale positive stage height raw) w)
      (j : Fin (atScale positive stage height raw r.val).width) := (a r.val).val.testBit j.val
  have eqn := output_expanded (atScale positive stage height raw) w m id port anchor owner pin room word hw
  have back := output_record (atScale positive stage height raw) w m id port anchor owner pin room hw word r side j
  rw [←eqn] at back
  refine Eq.trans ?_ back
  apply congrArg (fun x=>positivePlane (fun t : Fin (m+1)=>⌈dyadic t.val*w⌉₊) x (anchor (r,side)) j.val)
  funext q
  change encode (s q.1).bank.place (fun _ : Fin (s q.1).bank.width=>false)
    (publicLabels (stageKey height m) raw positive stage s a q.1) q.2.1 q.2.2 = _
  rw [same_place raw positive stage s id port same anchor owner pin room]; rfl

end Hierarchy.Tagged.WideStack.Leaf

end
end OAI
