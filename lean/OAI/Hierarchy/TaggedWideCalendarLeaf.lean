import OAI.Hierarchy.TaggedWideCalendarSites
import OAI.Hierarchy.TaggedWideLeafContraction
import OAI.Hierarchy.TaggedWideCutParts

namespace OAI
/-! # The physical reported leaf on the same pins as the purchased cuts -/

noncomputable section
namespace Hierarchy.Tagged.WideCalendarSites
open ThreeFlat Routing
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts WideStack
open WideStack.Leaf
open scoped Classical BigOperators
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] {V : Type} [Fintype V]

def attach (left right : Net F V) : Net F V :=
  WideHost.localFamily (I:=Fin 2) (A:=fun _=>V) ![left,right] (fun _ i=>.inl i)

theorem attach_value (left right : Net F V) (v : V→Bool) :
    TypedWiring.value (attach left right) v = TypedWiring.value left v * TypedWiring.value right v := by
  rw [attach,WideHost.localFamily_eval,Fin.prod_univ_two]
  rfl

omit [Field F] in
theorem attach_cost (left right : Net F V) : (attach left right).cells+(attach left right).internal =
    (left.cells+left.internal)+(right.cells+right.internal) := by
  rw [attach,WideHost.localFamily_size,Fin.sum_univ_two]
  rfl

/-- The paid flag is read once. Every positive-bank mask, private equality,
output-plane equation and chronological gate shares the same external pins. -/
def reportedSite (keep pad privateGate plane timeline chrono : Net F V) : Net F V :=
  attach keep (attach pad (attach privateGate (attach plane (attach timeline chrono))))

omit [Field F] in
theorem reported_cost (keep pad privateGate plane timeline chrono : Net F V) :
    (reportedSite keep pad privateGate plane timeline chrono).cells+
      (reportedSite keep pad privateGate plane timeline chrono).internal =
    (keep.cells+keep.internal)+((pad.cells+pad.internal)+((privateGate.cells+privateGate.internal)+
      ((plane.cells+plane.internal)+((timeline.cells+timeline.internal)+(chrono.cells+chrono.internal))))) := by
  simp only [reportedSite,attach_cost]

variable {T : Type} [Fintype T] {N groups ports lanes view w m n : ℕ} (key : T ↪ ℕ×ℕ)
    (raw : Fin N→ProtocolRAMEmit.Row) (positive : Fin N→Prop) (stage : Fin N→ℕ)
local notation "γ" => fun t:T=>(key t).2
local notation "rows" => fun t:T=>atScale positive stage (key t).1 raw
local notation "Free" => {i : Fin N // ¬positive i}
local notation "used" => fun e:Free=>(raw e.val).width
variable (b : ∀ t, Installed F groups ports lanes w m (key t).2 (atScale positive stage (key t).1 raw))
  (cap : {i : Fin N // ¬positive i} → ℕ)
local notation "B" => banks b
local notation "H" => Fin n
local notation "P" => (Fin groups×Fin ports)×Fin view
local notation "D" => Pin B cap H P
local notation "Words" => (i:Fin N)→Fin (2^(raw i).width)

/-- The literal voltages on a kept branch after closing the positive cut
banks and decoding both endpoints of each original word. -/
def nativePins (a : Words) (history : H→Bool) : D→Bool :=
  let z : ∀ t : T, ((Leaf.banks b) t).Slots :=
    Leaf.placed (Leaf.banks b) (Leaf.publicLabels key raw positive stage b a)
  Leaf.write (Leaf.banks b) cap z (Leaf.freeLabels raw positive cap a) history
    (Leaf.decoded (view:=view) key (Leaf.voltage (Leaf.banks b) z))

theorem close_reported (hw : 0<w) (room : ∀ e,used e≤cap e)
    (cover : ∀i,positive i→0<(raw i).width→∃t,key t=(stage i,widthIndex m ((raw i).width/(w:ℝ))) ∧ (raw i).group<groups)
    (pins : (D→Bool)→V→Bool) (cut : T→CutFormat F V)
    (keep pad privateGate plane timeline chrono : Net F V)
    (kept : Prop) [Decidable kept] (live : Fin n→Prop)
    (flag : ∀ d,TypedWiring.value keep (pins d)=if kept then 1 else 0)
    (cuts : ∀ z y h p i,(cut i).closed (pins (write B cap z y h p))=(B i).settings.close (z i))
    (masks : ∀ z y h p,TypedWiring.value pad (pins (write B cap z y h p))=
      if supported B (active b) z then 1 else 0)
    (free : ∀ z y h p,TypedWiring.value privateGate (pins (write B cap z y h p))=
      if EndsPadded used cap y then privateWeight raw positive cap y else 0)
    (output : ∀ z y h p,TypedWiring.value plane (pins (write B cap z y h p))=
      TypedWiring.value (decoder (F:=F) (groups:=groups) (ports:=ports) (lanes:=lanes)
        (view:=view) (w:=w) key) (Sum.elim (voltage B z) p))
    (historyMask : ∀ (a : Words) (h : Fin n → Bool),TypedWiring.value timeline (pins (nativePins (view:=view) key raw positive stage b cap a h))=
      if ∀j,h j=true→live j then 1 else 0) :
    (∑d : D→Bool,(∏i,(cut i).closed (pins d))*
        TypedWiring.value (reportedSite keep pad privateGate plane timeline chrono) (pins d)) =
      if kept then ∑a : Words,∑h : H→Bool,if ∀j,h j=true→live j then
        TypedWiring.value chrono (pins (nativePins (view:=view) key raw positive stage b cap a h)) else 0 else 0 := by
  by_cases accepted : kept
  · simp only [reportedSite,attach_value,flag,ite_eq_left accepted,one_mul]
    refine (contract_reported (view:=view) key raw positive stage b cap hw room cover
      (fun i d=>(cut i).closed (pins d)) (fun d=>TypedWiring.value pad (pins d))
      (fun d=>TypedWiring.value privateGate (pins d)) (fun d=>TypedWiring.value plane (pins d))
      (fun d=>TypedWiring.value timeline (pins d)*TypedWiring.value chrono (pins d))
      cuts masks free output).trans ?_
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr (by ext h; simp)
    intro h _
    let assignment := nativePins (view:=view) key raw positive stage b cap a h
    change TypedWiring.value timeline (pins assignment) * TypedWiring.value chrono (pins assignment) = _
    rw [show TypedWiring.value timeline (pins assignment) =
      (if ∀j,h j=true→live j then 1 else 0) from historyMask a h]
    split_ifs <;> simp [assignment]
  · simp [reportedSite,attach_value,flag,accepted]

end Hierarchy.Tagged.WideCalendarSites

end
end OAI
