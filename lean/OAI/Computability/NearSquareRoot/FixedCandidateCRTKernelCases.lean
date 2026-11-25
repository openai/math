import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchKernel
import OAI.Computability.NearSquareRoot.FixedCandidateCRTDispatchCases

/-! # The single family of original coefficient arrays presented to native CRT kernels -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code Adic Strip Loom Space Controlled CRTTable DigitPacking FixedPoint
open CRTDispatch

noncomputable section

/-- Full mathematical context of a physical request. The executable receives the
serialized stage seed and actual record rows, independently of this type. -/
structure Site (ρ : ℝ) (inv : Bool) where
  n : ℕ
  valid : Directory n
  stage : Switch n
  generated : stage ∈ order n inv
  β : Fin (CRTBudget.batches (addressBits n))
  admit : CRTBudget.NativeAdmission
    (selection (FixedCandidate.box n) stage.1.val (addressBits n) stage.2.2 β.val)
    (addressBits n) stage.2.2 (addressBits n/16) 0 (addressBits n) ρ
  values : Packed n stage → Record (addressBits n)

namespace Site

variable {ρ : ℝ} {inv : Bool} (x : Site ρ inv)

abbrev k := addressBits x.n

def actual : CRTKernel.Batch :=
  CRTKernel.Batch.admitted x.valid _ x.admit (selection ..).injective x.stage.1.isLt (fun q => selection_wide q)
    (which _ _ (Cap x.k)) x.β.val x.stage.2.1 inv (fun q => selection_batch q)
    (fun r a w => selection_covers r a w)

theorem actual_k : x.actual.k = x.k := x.admit.total

theorem actual_seed : x.actual.seed = issue low (seed inv x.stage,tally x.β.val) := by
  rw [issueAt x.valid]
  unfold CRTKernel.Batch.seed CRTTable.Native.seed
  congr 2
  exact Prod.ext (congrArg tally x.actual_k) rfl

private def original (x : Site ρ inv) : Input (fun x : Site ρ inv => x.n) inv :=
  ⟨x,⟨x.stage,x.generated⟩,x.values ∘ packing x.valid x.stage⟩

theorem sizeDom : Dom (fun x : Site ρ inv => x.actual.k) (fun x => size x.actual.seed) := by
  let idx (x : Site ρ inv) : Fin (batchN (seed inv (original x).2.1.val)) :=
    ⟨x.β.val,by change x.β.val < batchN (seed inv x.stage); rw [countAt x.valid]; exact x.β.isLt⟩
  have h := (issueSizeDom (fun x : Site ρ inv => x.n) inv).map (fun x => ⟨original x,idx x⟩)
  simpa only [actual_k,actual_seed,idx,original,k] using h

abbrev filmWidth := 2*(componentBits x.k+1)
abbrev u := Series.natural x.filmWidth
abbrev f (a : x.actual.Address) := Dusk.stock (x.values a)

def scattered := Benes.scatter x.actual.action x.values

private def modelList {w : ℕ} (p : CRTKernel.Batch) (v : p.Address → Dusk.Grain w) :=
  let idx := (flatAddress 2 p.k).symm.trans p.view
  List.ofFn fun t : Fin (2^p.k) => Dusk.tie (Dusk.mark (v (idx t)))

private theorem cloth_model {w : ℕ} (p : CRTKernel.Batch) (v : p.Address → Dusk.Grain w) :
    cloth (fun _ : Unit => line 2 p.k) (fun _ => Series.natural (2*(w+1)))
      (fun _ a => Dusk.stock (v (p.view a))) () = send (modelList p v) := by
  unfold cloth stackRun
  simp only [stripe_eq',Dusk.stockera]
  unfold modelList
  have tab := line_tab_addresses 2 p.k (fun t => Dusk.tie (Dusk.mark (v (p.view ((flatAddress 2 p.k).symm t)))))
  simpa only [Equiv.trans_apply,Function.comp_def,Equiv.symm_apply_apply] using congrArg send tab

private def rankPack (p : CRTKernel.Batch) : Fin (2^p.k) ≃ p.Address :=
  (BoxFin.recordIndex p.valid).symm.trans (packAddress _ _ (Native.fitAxis p.valid) p.n)

private theorem unflat (p : CRTKernel.Batch) (t : Fin (2^p.k)) :
    p.view ((flatAddress 2 p.k).symm t) = rankPack p t :=
  congrArg (rankPack p) ((flatAddress 2 p.k).apply_symm_apply t)

private theorem model_eq (v : x.actual.Address → Record x.k) :
    send (modelList x.actual v) = packedRows x.valid x.stage v := by
  unfold packedRows records modelList
  rw [List.map_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [capacity,x.actual_k]
  · intro j hi hj
    simp only [List.getElem_ofFn,Equiv.trans_apply,Function.comp_apply]
    rw [unflat]
    rfl

theorem array_eq : CRTKernel.array actual u f x = packedRows x.valid x.stage x.values :=
  (cloth_model x.actual x.values).trans (model_eq x x.values)

theorem result_eq : CRTKernel.result actual u f x = packedRows x.valid x.stage x.scattered :=
  (cloth_model x.actual x.scattered).trans (model_eq x x.scattered)

theorem volume_eq : CRTKernel.volume actual u x = CRTBudget.volume x.n := by
  simp [CRTKernel.volume,CRTBudget.volume,u,filmWidth,capacity,x.actual_k]

/-- One numerical cutoff serves every valid original width, switch, batch and
arbitrary record payload for this exponent and direction. -/
theorem run {ρ : ℝ} (hρ : 1/2 < ρ) (h₁ : ρ ≤ 1) (inv : Bool) :
    ∃ K : ℕ, ∀ {Y : Type} (pick : Y → Site ρ inv), (∀ y, K ≤ (pick y).k) →
    BoundedTask (fun y => CRTBudget.batchClock ρ (pick y).k (CRTBudget.volume (pick y).n))
      (fun y => CRTBudget.volume (pick y).n)
      (fun y => .fork (send (issue low (seed inv (pick y).stage,tally (pick y).β.val)))
        (packedRows (pick y).valid (pick y).stage (pick y).values))
      (fun y => packedRows (pick y).valid (pick y).stage (pick y).scattered) := by
  obtain ⟨K,execute⟩ := CRTKernel.bounded_fixedLow (actual (ρ := ρ) (inv := inv)) u f ρ hρ h₁ sizeDom
    (fun x => by simp [u,filmWidth])
  refine ⟨K,fun pick good => ?_⟩
  have pass := execute pick (fun y => (actual_k _).symm ▸ good y)
    (fun y => by rw [actual_k]; exact le_rfl)
    (fun y => by rw [actual_k]; exact (Nat.le_add_left ..).trans (pick y).admit.prefix_room)
  apply pass.conform
  · intro y; simp only [actual_k,volume_eq]
  · intro y; exact volume_eq _
  · intro y; simp only [together,Function.comp_apply,actual_seed,array_eq]
  · intro y; exact result_eq _

end Site
end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
