import OAI.ThreeFlat.RAM.HistoryStageShapeWires
import OAI.ThreeFlat.RAM.HistoryStageNumericTape
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly

namespace OAI
/-! # Numerical wire addresses across an input chart and output form -/
namespace ThreeFlat.RAM.HistoryStageShapeWires

open LinearAlgebra.SpectralBooks Diagonal Diagonal.HistoryContraction Diagonal.HistoryRelabel BitLayout
open scoped BigOperators Classical
noncomputable section
section Chart
variable {V E U D Pins F : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D] [Field F]
    {G : PortGraph V E} {H : PortGraph U D} {w : E→ℕ} {b : D→ℕ}
    {I : Iso (WordLayout.shape G w) (WordLayout.shape H b)} {L : WordLayout G w Pins}
    {R : Rewrite (WordLayout.shape H b) F} {t : Fin R.count} {W : Form (R.target t) Pins}
    {s : Stage R t (I.pushWord L).ports.form W}
    {hw : ∀ e,w e=b (I.edge e)} {hv : ∀ e z,(I.label e z).val=z.val}
    {v : (R.target t).Site} {external : ℕ}
local notation "next" => I.onStage L s hw hv

/-- Neither external nor internal half-port ordinals change when moving the old
graph to its physical chart. Finite casts in the old forest preserve these ordinals. -/
theorem At.onStage (a : At (I.pushWord L).ports s v external) :
    At L.ports next v external := by
  have oldExt (i : Fin (s.count v)) :
      (I.pushWord L).ports.ext (s.child v i).val=L.ports.ext ((next).child v i).val := rfl
  have oldHalf (i : Fin (s.count v)) :
      (I.pushWord L).ports.halfBits (s.child v i).val=L.ports.halfBits ((next).child v i).val := by
    let y:=(s.child v i).val
    have same:=I.pushWord_halfBits L hw (I.site.symm y)
    rw [I.site.apply_symm_apply] at same
    exact same
  have extFn : (fun i=>(I.pushWord L).ports.ext (s.child v i).val)=
      fun i=>L.ports.ext ((next).child v i).val:=funext oldExt
  have halfFn : (fun i=>(I.pushWord L).ports.halfBits (s.child v i).val)=
      fun i=>L.ports.halfBits ((next).child v i).val:=funext oldHalf
  refine ⟨?_,a.root,?_⟩
  · exact a.hidden.trans (Finset.sum_congr rfl fun i _=>oldHalf i)
  · intro i j
    let k:=pointer I L.ports (I.pushWord L).ports hw (I.pushExternal L) ((next).child v i).val j
    have kv : k.val=j.val:=I.pushWord_pointer_val L hw _ j
    have wh : (I.pushWord L).ports.form.width (I.site ((next).child v i).val)=
        (I.pushWord L).ports.form.width (s.child v i).val := by
      apply congrArg
      exact I.site.apply_symm_apply _
    change sourceAddress (s.childWire v i (Fin.cast wh k))=_
    refine (a.child i (Fin.cast wh k)).trans ?_
    have beforeExt := congrArg (fun f : Fin (s.count v) → ℕ => Tree.before f i) extFn
    have beforeHalf := congrArg (fun f : Fin (s.count v) → ℕ => Tree.before f i) halfFn
    change HistoryPortMap.piecewise k.val _ _ _ = _
    rw [kv,oldExt i,beforeExt,beforeHalf]
    with_unfolding_all rfl
end Chart

section Native
open HistoryStageRoot HistoryStageNumericTape
variable {F Pins : Type} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
    {L : PortLayout S Pins} {W : Form (R.target t) Pins} {s : Stage R t L.form W}
    {v : (R.target t).Site} {external : ℕ} (forest : Forest F L.form) (T : Input) (raw : ℕ→ℕ)

/-- Read numerical extents from the actual S12 kernel/child headers and the true
stage's endpoint/half descriptor. These equations include every operand of opcode 8. -/
theorem At.wiring (a : At L s v external)
    (degree : childCount T raw=s.count v) (ext : outer T raw=external)
    (pins : outPins T raw=W.width v)
    (arity : ∀ k : Fin (s.count v),(atResult raw (childPtr T raw k.val)).pins=L.form.width (s.child v k).val)
    (ends : ∀ k : Fin (s.count v),(atResult raw (childPtr T raw k.val)).extCount=L.ext (s.child v k).val) :
    Wiring T raw (s.tapePin forest v) := by
  have old (i : Fin (s.count v)) : oldHalf (atResult raw (childPtr T raw i.val))=L.halfBits (s.child v i).val := by
    rw [oldHalf,arity i,ends i];simp [PortLayout.form]
  have shared : HistoryStageRoot.hidden T raw=s.hidden v := by
    rw [HistoryStageRoot.hidden,degree,a.hidden]
    exact prefix_value oldHalf (fun i=>L.halfBits (s.child v i).val) old _ le_rfl
  refine ⟨by rw [degree],pins,shared,?_⟩
  intro i
  refine Fin.cases ?_ (fun k=>?_) i
  · intro j
    change sourceAddress (s.rootWire v j)=HistoryPortMap.piecewise j.val (HistoryStageRoot.hidden T raw)
      (2+outPins T raw) (2+outer T raw)
    rw [shared,pins,ext];exact a.root j
  · intro j
    change sourceAddress (s.childWire v k j)=HistoryPortMap.piecewise j.val
      (atResult raw (childPtr T raw k.val)).extCount (2+HistoryStageRoot.prefix T raw k.val Result.extCount)
      (2+outPins T raw+HistoryStageRoot.prefix T raw k.val oldHalf)
    rw [ends k,pins,prefix_value Result.extCount (fun i=>L.ext (s.child v i).val) ends k.val k.isLt.le,
      prefix_value oldHalf (fun i=>L.halfBits (s.child v i).val) old k.val k.isLt.le]
    exact a.child k j
end Native
end
end ThreeFlat.RAM.HistoryStageShapeWires

namespace ThreeFlat.RAM.HistoryStageShapeWires

open Diagonal.HistoryContraction

theorem At.reform {F P : Type} [CommSemiring F] {S : Shape} {R : Rewrite S F}
    {i : Fin R.count} {L : PortLayout S P} {a b : Form (R.target i) P}
    {s : Stage R i L.form a} {z : (R.target i).Site} {external : ℕ}
    (h : At L s z external) (e : a=b) : At L (s.reform e) z external := by
  cases e
  exact ⟨h.hidden,h.root,h.child⟩

end ThreeFlat.RAM.HistoryStageShapeWires

end OAI
