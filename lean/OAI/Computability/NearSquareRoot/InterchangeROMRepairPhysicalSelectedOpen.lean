import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalOpen
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalOpenModel
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelectedCaseRelease

/-! # The selected interchange with an exact ledger for a nonuniform recursive parent -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  IntegerMultiplication.Strip.Dims Space InterchangeSpace InterchangeROM InterchangeROMAddress
  Interchange.Template Interchange.StageScript InterchangeSpectralFibre

private theorem docket_bounded {Q : Type} (leaf : Leaf → List Tree → List Tree)
    (emit : Leaf → List Tree → List Q) (dom : Leaf → List Tree → Prop)
    (num : Leaf → ℕ) (valid : Q → Prop)
    (one : ∀ k u, dom k u → (emit k u).length ≤ num k ∧ ∀ q ∈ emit k u, valid q)
    (ss : List Step) (xs : List Tree) (ok : Ready leaf dom ss xs) :
    (docket leaf emit ss xs).length ≤ (ss.map fun s => num s.2).sum ∧
      ∀ q ∈ docket leaf emit ss xs, valid q := by
  induction ss generalizing xs with
  | nil => simp [docket]
  | cons s ss ih =>
    obtain ⟨a,b⟩ := one s.2 (xs.drop s.1) ok.2.1
    obtain ⟨c,d⟩ := ih (applyStep leaf xs s) ok.2.2
    exact ⟨by simpa only [docket,List.length_append,List.map_cons,List.sum_cons] using Nat.add_le_add a c,
      fun q hq => (List.mem_append.mp hq).elim (b q) (d q)⟩

theorem packed_injective {A D : Type} {l w p : ℕ} (addr : Series A) (pay : Series D) :
    Function.Injective (fun u : Bank (ZMod (p+1)) (Fin l) (A × D) (Fin w) =>
      LocalTable.Lift.bank addr (fun _ => pay) Prod.mk u) := by
  intro u v eq
  have e := LocalTable.Lift.render_injective addr (fun _ => pay) eq
  funext a z i
  rcases z with ⟨z,j⟩
  have h := congrFun (congrFun (congrFun e z) j) (finProdFinEquiv (a,i))
  let F : Fin l × Fin w ≃ Fin (l*w) := finProdFinEquiv
  change u (F.symm (F (a,i))).1 (z,j) (F.symm (F (a,i))).2 =
    v (F.symm (F (a,i))).1 (z,j) (F.symm (F (a,i))).2 at h
  simpa only [Equiv.symm_apply_apply] using h

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D Q : Type}
variable [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

/-- The same compiled command accepts every parent. The only child runs it uses
are exactly those in the emitted finite list, with their individual clocks. -/
theorem program_open_of_phases (h : Data.Valid j threshold x) (pay : Series D) (width : ℕ)
    (hw : pay.count ≤ width) (job : Job Q) (valid : Q → Prop) (L : ℕ)
    (phases : ∀ k u v, transfer h P G S f pay k u v →
      let H := send (header f P G S)
      let z := L*InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
      ∃ qs : List Q, qs.length ≤ phaseCalls h k ∧ (∀ q∈qs, valid q) ∧
        InterchangeROMSequence.Step job (commands x k) H (Task.forest id u) (packet H v) qs z z z)
    (u : x.Wide P G S f D) :
    let H := send (header f P G S)
    let M := InterchangeROMStageVolume.mass H (SweepBank.layout P G S x.a x.m x.b f).count width
    ∃ qs : List Q, qs.length ≤ x.calls ∧ (∀ q ∈ qs, valid q) ∧ ∀ parent,
      InterchangeROMRecursion.At parent (program x) job qs [] (packet H (wideBank x P G S f pay u))
        (packet H (wideBank x P G S f pay (swapPayload u))) (compiledRate x L*M) 0 0 := by
  intro H M
  let ord := SweepBank.layout P G S x.a x.m x.b f
  let n := x.labels*rows x
  let q := x.labels*checks x
  let s := Sizes.pencilOrder x.m
  let shape := 1+ord.count*(2+width*(2*x.modulusIndex+2))
  let w := wideBank x P G S f pay
  let b := shortBank x P G S f pay
  let charge (_ : Leaf) (_ : List Tree) : Allowance := ⟨L*M,L*M,L*M⟩
  let good (a : Leaf) (_ : List Tree) (qs : List Q) := qs.length ≤ phaseCalls h a ∧ ∀ y ∈ qs, valid y
  have hw' (y) : (w y).length = n := LocalTable.Lift.bank_length ..
  have hs' (y) : (b y).length = q := LocalTable.Lift.bank_length ..
  have per (a v z) (tr : transfer h P G S f pay a v z) :
      ∃ qs, good a v qs ∧ InterchangeROMSequence.Step job (commands x a) H (Task.forest id v)
        (packet H z) qs (charge a v).time (charge a v).cap (charge a v).depth := by
    obtain ⟨qs,hl,hv,hs⟩ := phases a v z tr
    exact ⟨qs,⟨hl,hv⟩,hs⟩
  obtain ⟨model,emit,sem,run⟩ := model_of_steps job (commands x) H charge good hw' hs'
    (packed_injective ord pay) (packed_injective ord pay) per
  let ss := steps n s
  have ready := ready_steps sem (inputs_domains ..) n hw' s u
  obtain ⟨hl,hv⟩ := docket_bounded model emit (Inputs w b) (phaseCalls h) valid
    (fun a v hv => (run a v hv).1) ss (w u) ready
  let stage := Raw.rowCount x.m * cost (Data.wordPrice h) (Data.predictorStage h)
  have total : (ss.map fun a => phaseCalls h a.2).sum ≤ x.calls := by
    change ((steps n s).map (price stage q x.m)).sum ≤ x.calls
    rw [total_price]
    simpa only [s,stage,q,checks,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Data.predictor_charge h
  refine ⟨_,hl.trans total,hv,?_⟩
  have openrun := command_open model emit charge H job (commands x) (Inputs w b)
    (fun a u hu => (run a u hu).2) ss (w u) ready
  let ac := allowance model charge H ss (w u)
  have eb := allowance_steps sem n q shape hw' hs'
    (bank_small ord (fun _ => pay) Prod.mk width (fun _ => hw))
    (bank_small ord (fun _ => pay) Prod.mk width (fun _ => hw))
    H s 0 0 (L*M) (L*M) (L*M) charge
    (fun _ _ _ => ⟨by simp [charge], le_rfl, le_rfl⟩) u
  let o := 256*(H.count+2+(7*n+2*q)*(shape+1)+1)
  obtain ⟨ht,hc,hd⟩ := eb
  change ac.time ≤ 1+(4*s+8)*(L*M+3*n*o+2)+(4*s*0+4*q*x.m)*0 at ht
  simp only [Nat.mul_zero,Nat.add_zero] at ht
  change ac.cap ≤ L*M+o at hc
  change ac.depth ≤ L*M+o+1 at hd
  obtain ⟨tlim,slim⟩ := resource_bounds H ord.count width x.modulusIndex n q s L
  have cap : L*M+o+1 ≤ compiledRate x L*M := slim
  have entire := at_of_open openrun (ht.trans tlim) (hc.trans ((Nat.le_succ _).trans cap)) (hd.trans cap)
  have er : runSteps model ss (w u) = w (swapPayload u) :=
    (run_steps sem n hw' s u).trans (congrArg w (Data.schedule_payload h u))
  rw [er] at entire
  exact entire

end InterchangeROMRepair.Physical.Selected

end

end NearSquareRoot
end Computability
end OAI
