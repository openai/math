import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWordUniform
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyLedger

/-! # The exact recursive docket of all native words in one selected stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization

open IntegerMultiplication.Code InterchangeROM

private theorem flat_length {A Q : Type} (l : List A) (q : A → List Q) (price : A → ℕ)
    (h : ∀ a, (q a).length = price a) :
    (l.flatMap q).length = (l.map price).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,h,ih]

theorem ledger_length_eq_scriptCharge {g : Frame} (r : Realization g) {Q : Type} (d : ℕ)
    (qs : (k : Fin 6) → r.Field d k → List Q) (price : Frame.Move → ℕ)
    (h : ∀ k z, (qs k z).length = price (r.operand (r.moveAt k z.1))) :
    (r.ledger d qs).length = scriptCharge price (g.script d) := by
  let t (k : Fin 6) := charge (T:=Frame.Table) price (.inr (g.route d (routePos k)))
  have each (k : Fin 6) : ((r.cells (routePos k+1) d).flatMap (qs k)).length = t k := by
    unfold t
    rw [r.charge_cells]
    exact flat_length _ _ _ (h k)
  apply (flat_length (List.finRange 6) _ t each).trans
  rw [show List.finRange 6 = [0,1,2,3,4,5] from by decide]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,t,scriptCharge,Frame.script,
    routePos,charge,Nat.add_zero,Nat.zero_add]

end InterchangeROMStage.Frame.Realization

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  InterchangeAddress InterchangeROMStage InterchangeROMRepair Space

theorem ledger_eq_literal {j threshold : ℕ} {x : Data} (h : Valid j threshold x) {Q : Type}
    (qs : (k : Fin 6) → (roleRealization h).Field (Raw.rowCount x.m) k → List Q)
    (hq : ∀ k z, (qs k z).length = wordPrice h ((roleRealization h).moveAt k z.1)) :
    ((roleRealization h).ledger (Raw.rowCount x.m) qs).length = x.literalStageCharge :=
  (roleRealization h).ledger_length_eq_scriptCharge _ qs (fun op => Opcode.price (lookup x.chart op)) hq

/-- All six movements share one physical child docket and one computable
local envelope. The billed cardinal is exactly the price of the finite
serialized stage script, even when different rows issue identical requests. -/
theorem selected_stage_dockets : ∃ M C K e : ℕ, 1 ≤ e ∧ ∀ {j threshold f l : ℕ}
    {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    (h : Valid j threshold x) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
    {D : Type} (pay : Series D) (v : x.Wide P G S f D),
    let r := roleRealization h
    let hdr := InterchangeROMAddress.header f P G S
    let rows := x.stageRows P G S f
    let F := rowFactor M C K e x * rowMass e hdr rows.count pay.count
    ∃ qs : (k : Fin 6) → r.Field (Raw.rowCount x.m) k → List (Request x.b),
      (r.ledger (Raw.rowCount x.m) qs).length = x.literalStageCharge ∧
      (∀ q∈r.ledger (Raw.rowCount x.m) qs, OpcodeProgram.Valid (b:=x.b) f rows.count l
        P G S (x.recordGood pay) q) ∧
      ∀ k u, let n := Frame.Realization.routePos k
             let μ := r.operand (r.moveAt k u.1)
             let src := stripe rows (stateRecord h pay v n (r.srcAt k u.1) u.2)
             let dst := stripe rows (stateRecord h pay v (n+1) u.1 u.2)
             InterchangeROMSequence.Step (Request.job x.b) (x.moveCmd μ) (send hdr) src dst (qs k u) F F F := by
  obtain ⟨M,C,K,e,he,run⟩ := selected_state_uniform
  refine ⟨M,C,K,e,he,?_⟩
  intro j threshold f l x nz hp h P G S p g s D pay v
  let r := roleRealization h
  let d := Raw.rowCount x.m
  have all (k : Fin 6) (u : r.Field d k) := run (l:=l) h P G S p g s pay v k u.1 u.2
  choose qs hqs using all
  refine ⟨qs,ledger_eq_literal h qs (fun k u => (hqs k u).1),?_,fun k u => (hqs k u).2.2⟩
  intro q hq
  obtain ⟨k,u,hu⟩ := (r.mem_ledger d).mp hq
  exact (hqs k u).2.1 q hu

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
