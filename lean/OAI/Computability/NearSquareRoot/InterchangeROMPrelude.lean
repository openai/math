import OAI.Computability.NearSquareRoot.InterchangeROMFrontPrepare
import OAI.Computability.NearSquareRoot.InterchangeROMFrontBranch
import OAI.Computability.NearSquareRoot.InterchangeROMDriver

/-! # A fixed physical prelude for every interchange template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFront

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Adic NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMAddress

structure Input where
  b : ℕ
  n : ℕ
  req : Request b
  radix : 2 ≤ b
  slots : 0 < n
  valid : Request.Admissible req

namespace Input

def template (i : Input) : InterchangeROMFrame.Input :=
  ((tally i.b,tally i.n),header i.req.width i.req.before i.req.between i.req.after_)

def scale : Scale Input := ⟨fun i => i.b^i.n,fun i => size i.template,fun i => i.req.payload.count⟩

def stage (i : Input) := i.n < i.req.width
instance (i : Input) : Decidable i.stage := inferInstanceAs (Decidable (i.n < i.req.width))

def inside (i : Input) (h : i.stage) : InterchangeROMExpose.Input :=
  ⟨i.b,i.n,i.req,i.radix,i.slots,h,i.valid⟩

def query (i : Input) := Tree.fork (InterchangeROMFrame.literal i.b i.n) ((Request.job i.b).issue i.req)

noncomputable def result (i : Input) := if h : i.stage then
  .fork (.atom true) (.fork (send (InterchangeROMExpose.centerHeader (i.inside h)))
    (InterchangeROMExpose.centerPayload (i.inside h)))
  else Tree.fork (.atom false) ((Request.job i.b).reply i.req)

private def encoded (i : Input) : InterchangeROMFrame.Spec × Header × Tree :=
  (i.template.1,i.template.2,i.req.payload)

private theorem encoded_cost : scale.Cost (fun i => size i.encoded) := by
  apply ((Scale.Cost.compact (Dom.base scale.header)).add
    (Scale.Cost.scan (s:=scale))).add (Scale.Cost.compact (Dom.const _ 1)) |>.mono
  intro i
  simp only [encoded,scale,template,size_prod]
  have eq : size i.req.payload = i.req.payload.count := rfl
  omega

private theorem flagged {X : Type} {s : Scale X} {q r : X → Tree} (bit : Bool) (h : s.Run q r) :
    s.Run q (fun i => .fork (.atom bit) (r i)) :=
  h.compose ⟨_,Scale.Cost.compact (Dom.const _ 0),Task.supply _ _⟩

private theorem small :
    (scale.on (fun z : {i // ¬stage i} => z.val)).Run (fun z => z.val.query) (fun z => z.val.result) := by
  let J := {i // ¬stage i}
  let get (z : J) := z.val
  let q (z : J) : InterchangeROMLeafMasks.Instance := ⟨⟨z.val.b,z.val.req⟩,z.val.radix,z.val.valid⟩
  have unzip : scale.Run query (fun i => InterchangeROMLeaf.leafQuery i.req) := by
    exact Scale.Run.easy encoded (show Easy (fun a : InterchangeROMFrame.Spec × Header × Tree =>
      ((a.1.1,a.2.1),a.2.2)) from by fun_prop) encoded_cost
  have cap (z : J) : (q z).D ≤ (scale.on get).endpoint z := by
    change (line z.val.b z.val.req.width).count ≤ z.val.b^z.val.n
    rw [lineSize]
    exact Nat.pow_le_pow_right (by have := z.val.radix; omega) (Nat.le_of_not_gt z.property)
  have tags : Dom (scale.on get).header (fun z => size
      (InterchangeROMLeafMasksShape.descriptor (q z).req)) := by
    apply (Dom.base _).mono
    intro z
    change size (tally z.val.b,(z.val.template).2) ≤ size z.val.template
    simp only [template,size_prod]
    omega
  have code := flagged false ((unzip.on get).compose (leaf q cap tags fun _ => le_rfl))
  convert code using 1 <;> first | rfl | skip
  funext z
  simp [result,z.property,q]

private theorem large :
    (scale.on (fun z : {i // stage i} => z.val)).Run (fun z => z.val.query) (fun z => z.val.result) := by
  have code := flagged true (Internal.prepare.on (fun z : {i // stage i} => z.val.inside z.property))
  convert code using 1 <;> first | rfl | skip
  funext z
  simp [result,z.property]

private def tag (q : InterchangeROMFrame.Spec × Header × Tree) :=
  (InterchangeROMFrame.internal (q.1,q.2.1),q)

private theorem tag_easy : Easy tag :=
  ((show Easy (fun q : InterchangeROMFrame.Spec × Header × Tree => (q.1,q.2.1)) from
    by fun_prop).compose InterchangeROMFrame.internal_easy).pair easy_id

/-- A single physical program handles both branches for every radix,
template width, spectator shape and stream of arbitrarily sized records. -/
theorem prelude : ∃ d, Task (scale.work d) query result := by
  have dispatch := Scale.Run.branch query result stage small large
  have test : scale.Run query (fun i => .fork (.atom (decide i.stage)) i.query) := by
    have code := Scale.Run.easy encoded tag_easy encoded_cost
    convert code using 1 <;> first | rfl | skip
    funext i
    change Tree.fork (.atom (decide i.stage)) i.query =
      Tree.fork (.atom (InterchangeROMFrame.internal i.template)) i.query
    rw [template,InterchangeROMFrame.internal_header]
    rfl
  exact (test.compose dispatch).extract

/-- The prelude and its register set are fixed before the template index is supplied. -/
theorem exists_core :
    ∃ (c : Cmd) (R d C : ℕ), 0 < R ∧ CommonRegisters.Within R c ∧
      ∀ i env deck, Fits env c (pile 0 i.query deck) (pile 0 i.result deck) (C*(scale.work d i+1)) := by
  obtain ⟨d,c,C,ok⟩ := prelude
  obtain ⟨R,pos,bounded⟩ := ((Filter.eventually_gt_atTop (0:ℕ)).and (RegisterSelect.within_eventually c)).exists
  exact ⟨c,R,d,C,pos,bounded,ok⟩

end Input
end InterchangeROMFront

end NearSquareRoot
end Computability
end OAI
