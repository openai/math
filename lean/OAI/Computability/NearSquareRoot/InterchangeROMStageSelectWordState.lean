import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectWordBound
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifySelected
import OAI.Computability.NearSquareRoot.InterchangePayloadBank

/-! # Actual child ledgers between successive typed sparse movement states

Each move permutes complete payload records. Its output is the register
occurrence in the verified eleven-operation trajectory. The record-width,
inherited shape, and finite ground-symbol assertions hold on the contents of
every recursive child appearing in the returned ledger.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom InterchangeROMStage
  InterchangeAddress InterchangeSpectralFibre InterchangeROMTable Space

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D : Type}
  [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

/-- The complete payload record at one address of the selected stage state. -/
noncomputable def stateRecord (h : Valid j threshold x) (pay : Series D) (v : x.Wide P G S f D)
    (n : ℕ) (row : (roleRealization h).Boundary n) (d : x.WideIndex) (a : x.Address P G S f) : Tree :=
  stripe pay fun k => numeral (stageStates h v n row (a,k) d).val

abbrev recordGood (x : Data) {D : Type} (pay : Series D) : Tree → Prop :=
  InterchangePayloadBank.Good (I:=Unit) (D:=fun _ => D) (fun _ => pay)
    (fun a : x.Ground => numeral a.val) ()

theorem stateRecord_good (h : Valid j threshold x) (pay : Series D) (v : x.Wide P G S f D)
    (n : ℕ) (row : (roleRealization h).Boundary n) (d : x.WideIndex) (a : x.Address P G S f) :
    x.recordGood pay (stateRecord h pay v n row d a) :=
  ⟨fun k => stageStates h v n row (a,k) d, rfl⟩

theorem stateRecord_move (h : Valid j threshold x) (pay : Series D) (v : x.Wide P G S f D)
    (k : Fin 6) (z : (roleRealization h).Boundary (Frame.Realization.routePos k+1)) (d : x.WideIndex) :
    let r := roleRealization h
    let n := Frame.Realization.routePos k
    stateRecord h pay v n (r.srcAt k z) d ∘ ((nativeLayout h P G S f).perm (r.moveAt k z)).symm =
      stateRecord h pay v (n+1) z d := by
  funext a
  apply congrArg (stripe pay)
  funext y
  have ht := stageStates_route h v k z (a,y)
  dsimp only at ht
  erw [withPayload_perm D (nativeLayout h P G S f) ((roleRealization h).moveAt k z)] at ht
  exact congrArg (fun val : x.WideIndex → x.Ground => numeral (val d).val) ht.symm

/-- The local movement program contract supplied to `execute_route`. The
induction hypothesis on the recursive parent is quantified by `Step`, so it
can charge the actual requests once at any subsequent recursive depth. -/
theorem selected_state_word_run : ∃ M C K e : ℕ, 1 ≤ e ∧ ∀ {j threshold f l : ℕ}
    {x : Data} [NeZero x.b] [Fact (x.modulusIndex+1).Prime]
    (h : Valid j threshold x) (P G S : Tape) (_ : solid P) (_ : solid G) (_ : solid S)
    {D : Type} (pay : Series D) (v : x.Wide P G S f D)
    (k : Fin 6) (z : (roleRealization h).Boundary (Frame.Realization.routePos k+1)) (d : x.WideIndex),
    let r := roleRealization h
    let n := Frame.Realization.routePos k
    let op := r.moveAt k z
    let μ := r.operand op
    let hdr := InterchangeROMAddress.header f P G S
    let rows := x.stageRows P G S f
    let u := stripe rows (stateRecord h pay v n (r.srcAt k z) d)
    let y := stripe rows (stateRecord h pay v (n+1) z d)
    let F := moveWeight M C K e x μ * OpcodeProgram.geometry e hdr rows.count u u
    ∃ qs, qs.length = wordPrice h op ∧
      (∀ q∈qs, OpcodeProgram.Valid (b:=x.b) f rows.count l P G S (x.recordGood pay) q) ∧
      InterchangeROMSequence.Step (Request.job x.b) (x.moveCmd μ) (send hdr) u y qs F F F := by
  obtain ⟨M,C,K,e,he,run⟩ := selected_word_run_scaled
  refine ⟨M,C,K,e,he,?_⟩
  intro j threshold f l x nz hp h P G S p g s D pay v k z d
  let r := roleRealization h
  let n := Frame.Realization.routePos k
  have res := run (l := l) h (r.moveAt k z) P G S p g s
    (stateRecord h pay v n (r.srcAt k z) d) (x.recordGood pay) (stateRecord_good h pay v n (r.srcAt k z) d)
  dsimp only at res
  rw [stateRecord_move h pay v k z d] at res
  exact res

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
