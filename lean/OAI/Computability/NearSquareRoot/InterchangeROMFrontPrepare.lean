import OAI.Computability.NearSquareRoot.InterchangeROMFrontCost
import OAI.Computability.NearSquareRoot.InterchangeROMExpose

/-! # The two endpoint leaf calls in the shared physical prelude -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFront

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMAddress
  InterchangeROMLeafMasks

abbrev Descr := Tally × Header
abbrev Frames := Header × Descr × Descr

def frames (x : InterchangeROMFrame.Input) : Frames :=
  let s := InterchangeROMFrame.split x
  (s.2.2,(x.1.1,s.2.1),(x.1.1,s.1))

theorem frames_poly : Poly frames := by
  unfold frames
  fun_prop

private theorem count_fork {I : Type} {s : Scale I} {u v : I → Tree}
    (a : s.Cost fun i => (u i).count) (b : s.Cost fun i => (v i).count) :
    s.Cost (fun i => ((u i).fork (v i)).count) :=
  (a.add b).add (Scale.Cost.compact (Dom.const _ 1))

theorem leaf {I : Type} {s : Scale I} (q : I → Instance)
    (card : ∀ i, (q i).D ≤ s.endpoint i)
    (head : Dom s.header (fun i => size (InterchangeROMLeafMasksShape.descriptor (q i).req)))
    (data : ∀ i, (InterchangeROMLeaf.payload (q i).req).count ≤ s.payload i) :
    s.Run (fun i => InterchangeROMLeaf.leafQuery (q i).req)
      (fun i => (Request.job (q i).radix).reply (q i).req) := by
  obtain ⟨k,run⟩ := InterchangeROMLeaf.universal_leaf
  refine ⟨_,?_,run.on q⟩
  refine ⟨_,_,((Dom.base s.endpoint).add (Dom.const _ 1)).pow k,
    (head.add (Dom.const _ 1)).pow 2,fun i => ?_⟩
  dsimp only
  gcongr
  · exact card i
  · exact data i

namespace Internal
open InterchangeROMExpose

def scale : Scale Input where
  endpoint i := i.b^i.n
  header i := size (template i)
  payload i := i.req.payload.count

private noncomputable def lead (i : Input) : Instance := ⟨⟨i.b,leadRequest i⟩,i.radix,(admissible i).1⟩
private noncomputable def tail (i : Input) : Instance := ⟨⟨i.b,tailRequest i⟩,i.radix,(admissible i).2⟩

private theorem compact : Dom scale.header (fun i =>
    size (InterchangeROMLeafMasksShape.descriptor (lead i).req) +
    size (InterchangeROMLeafMasksShape.descriptor (tail i).req) + size (centerHeader i)) :=
  header_budget

private def encoded (i : Input) : InterchangeROMFrame.Spec × Header × Tree :=
  ((template i).1,(template i).2,i.req.payload)

private def wire (q : Frames × Tree) : Header × Descr × Descr × Tree :=
  (q.1.1,q.1.2.1,q.1.2.2,q.2)

private def internalQuery (i : Input) := Tree.fork (send (tally i.b,tally i.n)) ((Request.job i.b).issue i.req)

/-- Run the leading and trailing interchanges using the common leaf
program. The remaining center header is parked by the prelude and returned
together with the rearranged stream, ready for the generated stage. -/
theorem prepare : scale.Run internalQuery
    (fun i => Tree.fork (send (centerHeader i)) (centerPayload i)) := by
  have first : scale.Run internalQuery (fun i => Tree.fork (send (template i)) i.req.payload) := by
    apply Scale.Run.easy (f:=fun t : InterchangeROMFrame.Spec × Header × Tree => ((t.1,t.2.1),t.2.2))
      encoded (by fun_prop)
    apply ((Scale.Cost.compact (Dom.base scale.header)).add
      (Scale.Cost.scan (s:=scale))).add (Scale.Cost.compact (Dom.const _ 1)) |>.mono
    intro i
    simp only [encoded,scale,template,size_prod]
    have eq : size i.req.payload = i.req.payload.count := rfl
    omega
  have prog := (Scale.Run.poly (s:=scale) template frames_poly (Dom.base _)).left
    (fun i => i.req.payload)
  have formed := first.compose prog
  have hf : Dom scale.header (fun i => size (frames (template i))) :=
    (frames_poly.length.map template)
  have wires := Scale.Run.easy (s:=scale) (fun i => (frames (template i),i.req.payload))
    (show Easy wire from by unfold wire; fun_prop)
    (count_fork (Scale.Cost.compact hf) (Scale.Cost.scan (s:=scale)))
  have next := formed.compose wires
  have hfst : Dom scale.header (fun i => size (InterchangeROMLeafMasksShape.descriptor (lead i).req)) :=
    compact.mono (by intro i; omega)
  have hsnd : Dom scale.header (fun i => size (InterchangeROMLeafMasksShape.descriptor (tail i).req)) :=
    compact.mono (by intro i; omega)
  have hc : Dom scale.header (fun i => size (centerHeader i)) := compact.mono (by intro i; omega)
  have f := leaf (s:=scale) lead (fun i => (endpoint_cardinalities i).1) hfst
    (fun i => (data_counts i).1.le)
  have t := leaf (s:=scale) tail (fun i => (endpoint_cardinalities i).2) hsnd
    (fun i => (data_counts i).2.2.1.le)
  let meta2 (i : Input) := Tree.fork (send (tally i.b)) (tailRequest i).header
  have complete := (f.right meta2 (Scale.Cost.compact hsnd)).compose
    (show scale.Run (fun i => Tree.fork (meta2 i) ((Request.job i.b).reply (leadRequest i)))
        (fun i => centerPayload i) from by
      have a (i : Input) : InterchangeROMLeaf.leafQuery (tail i).req =
          Tree.fork (meta2 i) ((Request.job i.b).reply (leadRequest i)) :=
        congrArg (Tree.fork (meta2 i)) (tail_payload i)
      simpa only [funext a,show (fun i => (Request.job (tail i).radix).reply (tail i).req) =
        centerPayload from funext tail_reply] using t)
  apply next.compose
  have routed := complete.right (fun i => send (centerHeader i)) (Scale.Cost.compact hc)
  convert routed using 1
  funext i
  obtain ⟨hl,ht,hc⟩ := header_tree i
  simp only [wire,frames,meta2, InterchangeROMLeaf.leafQuery]
  change (Tree.fork (send _) (.fork (.fork _ (send _)) (.fork (.fork _ (send _)) i.req.payload))) = _
  rw [← hl,← ht,← hc,← lead_payload i]
  rfl

end Internal
end InterchangeROMFront

end NearSquareRoot
end Computability
end OAI
