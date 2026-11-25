import OAI.Computability.NearSquareRoot.InterchangeROMOuterBody
import OAI.Computability.NearSquareRoot.InterchangeROMOuterCost
import OAI.Computability.NearSquareRoot.InterchangeROMFrontNode

/-! # Closing the actual selected controller on the entire native request type -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom NearSquareRoot.Space
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request NearSquareRoot.InterchangeROMExpose
  NearSquareRoot.InterchangeROMRecursion NearSquareRoot.InterchangeSpectralFibre

/-- The three local interfaces of the native center. Their wire types are
fixed before the complete controller is tied. The outside reserves, the
leaf case and both resource recurrences are discharged by `compile_native`. -/
def Components {b p a m l n : ℕ} (q : Request b) (hb : 2 ≤ b) (hn : 0 < a+m+a) (hw : a+m+a < q.width)
    (ok : Packed (@value (p+1)) q) (parent enter main leave : Cmd)
    (limit B C U kb kc ku : ℕ) : Prop :=
  let i := InterchangeROMStars.frame a m q hb hn hw ok.1
  let tag := send (centerHeader i)
  let head := send (groupedHeader i (l*n))
  let op : key i (l*n) → key i (l*n) := swapMain (OuterReserves.main a m)
  At parent enter (job b) [] [] (.fork tag (centerPayload i)) (.fork tag (.fork head (stream i (l*n) id)))
    (B*(localMass q kb+1)) 0 0 ∧
  (∀ x : tensor i p l n, ∃ sm : List (Request b), sm.length ≤ limit ∧
    (∀ y ∈ sm, Packed (@value (p+1)) y ∧ y.width=f i ∧ y.recordWidth=q.recordWidth ∧
      y.rows.count=(groupedRows i (l*n)).count) ∧
    At parent main (job b) sm [] (cubic i x) (cubic i (permute x op)) (C*(localMass q kc+1)) 0 0) ∧
  At parent leave (job b) [] [] (.fork tag (.fork head (stream i (l*n) op)))
    (.fork tag (InterchangeROMStars.afterMain a m q hb hn hw ok.1)) (U*(localMass q ku+1)) 0 0

/-- A single reserve degree works across all templates. For each chosen
template the emitted prelude, bank, cubic core, inverse bank and reserve
commands give one specified closed program. Its time and both stack bounds
hold on every thick native request, including noninternal widths. -/
theorem compile_native (F : InterchangeROMFront.Core) :
    ∃ k : ℕ, ∀ {b p a m l n : ℕ} (hb : 2 ≤ b) (hm : 1 < m) (_ : 3 ≤ l*n) (_ : l*n ≤ b)
      (α : ℝ) (_ : 0 ≤ α) (limit B C U kb kc ku : ℕ)
      (_ : (((limit*BatchRows.groups b (l*n):ℕ):ℝ)/b+(2*a:ℕ)) < (m:ℝ)^α)
      (enter main leave : Cmd),
      let slots := a+m+a
      let center := stage b a m enter main leave
      let parent := InterchangeROMFrame.node F.cmd center b slots
      let valid := Packed (b:=b) (@value (p+1))
      let degree := max (F.degree+1) (stageDegree kb kc ku k)
      (∀ (q : Request b) (good : valid q) (hw : slots < q.width),
        Components (l:=l) (n:=n) q hb (by omega) hw good parent enter main leave limit B C U kb kc ku) →
      Certified (InterchangeROMFrame.controller F.cmd center b slots)
        (fun x : ThickRequest valid degree => ⌈(x.val.recordVolume:ℝ)*(x.val.width:ℝ)^α⌉₊)
        (fun x => x.val.recordVolume) (fun x => (job b).issue x.val) (fun x => (job b).reply x.val) := by
  obtain ⟨k,A,worker⟩ := body
  refine ⟨k,?_⟩
  intro b p a m l n hb hm hW under α hα limit B C U kb kc ku contract enter main leave slots center parent valid degree pieces
  let θ : ℝ := ((limit*BatchRows.groups b (l*n):ℕ):ℝ)/b+(2*a:ℕ)
  let frontRate := InterchangeROMFront.rate F (p+1) b slots
  let rate := nodeRate F A k b a m p B C U + frontRate
  let H := InterchangeROMStars.reserve b a + 3
  let park (q : Request b) := H*(Nat.log 2 q.recordVolume+1)
  have hn : 0 < slots := by dsimp [slots]; omega
  have one (q : Request b) (good : valid q) :
      ∃ sm fu : List (Request b), stepAccount valid slots θ q (sm++fu) ∧
      (∀ y∈sm, 3*y.rows.count ≤ 2*q.rows.count) ∧
      At parent parent (job b) sm fu ((job b).issue q) ((job b).reply q)
        (rate*(localMass q degree+1)) (park q) (park q) := by
    let input : InterchangeROMFront.Input := ⟨b,slots,q,hb,hn,good.1⟩
    by_cases internal : slots < q.width
    · have parts := pieces q good internal
      obtain ⟨sm,fu,ledger,shrink,raw⟩ := worker q hb hn internal hW under good parent enter main leave
        (B*(localMass q kb+1)) (C*(localMass q kc+1)) (U*(localMass q ku+1)) limit parts.1 parts.2.1 parts.2.2
      refine ⟨sm,fu,ledger,shrink,?_⟩
      have test : input.stage := internal
      have insideFee := body_work_le q hb hn internal good.1 A k p (le_refl (B*(localMass q kb+1)))
        (le_refl (C*(localMass q kc+1))) (le_refl (U*(localMass q ku+1)))
      have chosen : At parent (bif decide input.stage then center else .pass) (job b)
          sm fu input.middle ((job b).reply q)
          (bodyRate A k b a m p B C U*(localMass q (stageDegree kb kc ku k)+1))
          (InterchangeROMStars.reserve b a*(Nat.log 2 q.recordVolume+1)) 3 := by
        have middle : input.middle = .fork
            (send (centerHeader (InterchangeROMStars.frame a m q hb hn internal good.1)))
            (centerPayload (InterchangeROMStars.frame a m q hb hn internal good.1)) := by
          unfold InterchangeROMFront.Input.middle
          split
          · rfl
          · contradiction
        rw [show (bif decide input.stage then center else .pass) = center by simp [test],middle]
        exact raw.mono insideFee le_rfl le_rfl
      have cost := node_work_le F q A k a m p B C U kb kc ku
        (le_refl (bodyRate A k b a m p B C U*(localMass q (stageDegree kb kc ku k)+1)))
      apply (F.node (p+1) input center sm fu good _ _ _ chosen).mono
      · exact cost.trans (Nat.mul_le_mul_right _ (by dsimp [rate]; omega))
      · exact Nat.mul_le_mul_right _ (by dsimp [H]; omega)
      · exact (show 3 ≤ H by dsimp [H]; omega).trans
          (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    · have test : ¬ input.stage := internal
      let work := input.middle.count+1
      have pass : At parent .pass (job b) [] [] input.middle input.middle work 0 0 := by
        apply At.local_run
        intro env deck base live
        exact (BoundedFits.pass (env:=parent::env) (depth:=work)
          ((live.pile 0 input.middle).mono (by dsimp [work]; omega : _ ≤ base+work))).mono (by dsimp [work]; omega) le_rfl le_rfl
      have chosen : At parent (bif decide input.stage then center else .pass) (job b) [] [] input.middle
          ((job b).reply q) work 0 0 := by
        simpa [InterchangeROMFront.Input.middle,test] using pass
      refine ⟨[],[],⟨by simp,by dsimp [θ]; simp only [List.map_nil,List.sum_nil]; positivity⟩,
        by simp,?_⟩
      have size := InterchangeROMFront.rate_bound F (p+1) input good
      change _ + input.middle.count + 20 ≤ frontRate*localMass q (F.degree+1) at size
      have fee : work ≤ frontRate*(localMass q (F.degree+1)+1) :=
        (show work ≤ frontRate*localMass q (F.degree+1) by dsimp only [work]; omega).trans
          (Nat.mul_le_mul_left _ (Nat.le_succ _))
      have setup := Nat.mul_le_mul_left frontRate (Nat.le_succ (localMass q (F.degree+1)))
      have bound := Nat.add_le_add setup fee
      have fees : frontRate+frontRate ≤ rate := by
        dsimp only [rate,nodeRate,frontRate,slots]
        omega
      apply (F.node (p+1) input center [] [] good _ _ _ chosen).mono _ (Nat.zero_le _) (Nat.zero_le _)
      rw [← Nat.add_mul] at bound
      exact bound.trans (Nat.mul_le_mul fees (Nat.succ_le_succ (localMass_mono q (show F.degree+1 ≤ degree from le_max_left ..))))
  choose sm fu facts using fun x : Subtype valid => one x.val x.property
  exact close_native hb hm (by dsimp [slots]; omega) F.cmd center hα contract valid (fun _ h => h.1) (fun _ h => h.2.1)
    degree rate H sm fu (fun x => (facts x).1) (fun x => (facts x).2.1) (fun x => (facts x).2.2)

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
