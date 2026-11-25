import OAI.Computability.NearSquareRoot.FixedCandidateCRTBudget
import OAI.Computability.NearSquareRoot.CRTTableNativePlanSpec
import OAI.Computability.NearSquareRoot.PermutationLayoutMask

/-! # Admission of concrete CRT target batches to the native sparse mask -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTBudget

open IntegerMultiplication Controlled CRTTable CRTTable.Native
open SynchronizedPermutationBudget (rowFactor)

/-- Flattening the external fields of the emitted plan uses exactly their
total width in the original CRT tree. This counts every port on a control
axis, including those of the shorter final field. -/
theorem externalSlots_length (box : List (ℕ × ℕ)) (n : ℕ) :
    (externalSlots (axisWidth box) n).length = ((CRTTree.controls n box).map Prod.fst).sum := by
  have recover : (List.finRange box.length).map box.get = box := by
    apply List.ext_getElem <;> simp
  have eq := CRTTree.controls_map box.get n (List.finRange box.length)
  rw [recover] at eq
  have count (xs : List (Fin box.length)) :
      (xs.sigma fun i => List.finRange (axisWidth box i)).length = (xs.map (axisWidth box)).sum := by
    induction xs with
    | nil => rfl
    | cons i xs ih => simp [List.sigma] at *
  rw [externalSlots,count,List.map_reverse,List.sum_reverse,eq,List.map_map]
  rfl

/-- The local control list contains the nonswitched ports of only the
selected axes. The estimate also works when a bit index exceeds a width. -/
theorem localSlots_le {k b n : ℕ} {box : List (ℕ × ℕ)}
    (hb : BoxShape.Valid k (BoxScale.width k) box)
    (sel : Fin b → Fin (targetOrder box.length n).length) (j : ℕ) :
    (localSlots (axisWidth box) sel j).length ≤ b*stride k := by
  let w := axisWidth box
  change ((List.ofFn (Chosen sel)).sigma (fun g => (List.finRange (w g)).eraseIdx j)).length ≤ _
  simp only [List.sigma,List.length_flatMap,List.length_map,List.map_ofFn,List.sum_ofFn]
  calc
    _ ≤ ∑ _ : Fin b, stride k := by
      apply Finset.sum_le_sum
      intro q _
      have le := (List.eraseIdx_sublist (List.finRange (w (Chosen sel q))) j).length_le
      rw [List.length_finRange] at le
      exact le.trans ((hb.axisBounds _ (List.get_mem box (Chosen sel q))).2.1.trans (le_max_right ..))
    _ = _ := by simp

/-- The prefix occupies all remaining physical bits after both guarded
chunks and the collapsed low payload. -/
def nativePrefix (k b low : ℕ) : ℕ :=
  k - (low + 2*((b+1)*Controlled.guardWidth k))

/-- Concrete layout and clock inputs shared by the reflected directory
generator and the bounded native sparse-mask command. -/
structure NativeAdmission {box : List (ℕ × ℕ)} {b n : ℕ}
    (sel : Fin b → Fin (targetOrder box.length n).length) (k j low D Q : ℕ) (ρ : ℝ) : Prop where
  guard_pos : 0 < Controlled.guardWidth k
  capacity_pos : 0 < blocksPerBatch k 4 (stride k)
  low_pos : 0 < low
  payload : payloadBits D Q ≤ low
  target_fits : b*Controlled.guardWidth k + low ≤ k
  prepare_fits : low + 2*((b+1)*Controlled.guardWidth k) + (controlSlots (axisWidth box) sel j).length ≤ k
  prefix_room : (controlSlots (axisWidth box) sel j).length + payloadBits 2 k ≤ nativePrefix k b low
  total : PermutationLayout.maskWidth (nativePrefix k b low) b (Controlled.guardWidth k) low = k
  sparse : (3*Packed.cap b (Controlled.guardWidth k - 1) 0+1)*(32*b) ≤
    2^(Packed.width (Controlled.guardWidth k-1) 0)
  rate : 2*(((b+1)*Controlled.guardWidth k:ℕ)+1:ℝ)^ρ ≤ rowFactor k ρ
  rows : rowFactor k ρ ≤ 2^(nativePrefix k b low)

theorem native_admission {k b n j low D Q : ℕ} {box : List (ℕ × ℕ)} {ρ : ℝ}
    (hk : 1 ≤ k) (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) (hb : BoxShape.Valid k (BoxScale.width k) box)
    (sel : Fin b → Fin (targetOrder box.length n).length)
    (half : 2*BoxScale.width k ≤ k) (room : 8*4*stride k ≤ k)
    (card : b ≤ blocksPerBatch k 4 (stride k))
    (res : 32*(low + payloadBits 2 k) ≤ 3*k) (posLow : 0 < low) (pay : payloadBits D Q ≤ low) :
    NativeAdmission sel k j low D Q ρ := by
  let e := (externalSlots (axisWidth box) n).length
  have he : 4*e ≤ 3*k := by
    dsimp only [e]; rw [externalSlots_length]
    exact CRTTree.controlFraction hb n half
  have alloc : b*(32*stride k) ≤ k :=
    (Nat.mul_le_mul_right _ card).trans (Nat.div_mul_le_self ..)
  have alloc' : 32*(b*stride k) ≤ k := by
    rwa [show 32*(b*stride k) = b*(32*stride k) by ring]
  have body : e + b*stride k + (b+1)*stride k + (b+1)*stride k + (low+payloadBits 2 k) ≤ k := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have g : 0 < Controlled.guardWidth k := by unfold Controlled.guardWidth; omega
  have gs : Controlled.guardWidth k ≤ stride k := le_max_left ..
  have chunk := Nat.mul_le_mul_left (b+1) gs
  have locals := localSlots_le hb sel j
  have slots : (controlSlots (axisWidth box) sel j).length =
      e + (localSlots (axisWidth box) sel j).length := List.length_append
  have full : low+2*((b+1)*Controlled.guardWidth k) + (controlSlots (axisWidth box) sel j).length +
      payloadBits 2 k ≤ k := by omega
  have chunkFit : (b+1)*Controlled.guardWidth k ≤ k := by omega
  have main : b*Controlled.guardWidth k + low ≤ k := by
    have ht : b*Controlled.guardWidth k ≤ (b+1)*Controlled.guardWidth k :=
      Nat.mul_le_mul_right _ (Nat.le_succ b)
    omega
  have freeSlots : (controlSlots (axisWidth box) sel j).length + payloadBits 2 k ≤ nativePrefix k b low := by
    unfold nativePrefix; omega
  have stridePos := lt_of_lt_of_le g gs
  refine ⟨g,Nat.div_pos room (by positivity),posLow,pay,main,by omega,freeSlots,?_,
    SynchronizedPermutationBudget.sparse_of_fits chunkFit,
    SynchronizedPermutationBudget.row_rate chunkFit h₀,?_⟩
  · simp only [PermutationLayout.maskWidth,Packed.cap,Packed.width,Nat.add_zero,
      show Controlled.guardWidth k - 1 + 1 = Controlled.guardWidth k by omega,nativePrefix]
    omega
  · exact (SynchronizedPermutationBudget.row_factor_high hk h₁).trans
      (Nat.pow_le_pow_right (by decide) (by omega))

/-- If a regime scale is polynomial in the original address width, a fixed
increase of the low-reserve degree pays its payload condition. -/
theorem payload_of_polynomial_scale {D Q pow k : ℕ} (hk : 1 ≤ k) (hQ : Q ≤ (k+1)^pow) :
    payloadBits D Q ≤ payloadBits (D*(pow+1)) k := by
  have grow : (k+1)^pow + 1 ≤ (k+1)^(pow+1) := by
    rw [pow_succ]
    have p : 1 ≤ (k+1)^pow := Nat.one_le_pow _ _ (by omega)
    nlinarith [Nat.mul_le_mul_left ((k+1)^pow) hk]
  have powBound := Nat.pow_le_pow_left (Nat.le_pow_clog (b:=2) (by decide) (k+1)) (pow+1)
  have clog : Nat.clog 2 (Q+1) ≤ (pow+1)*Nat.clog 2 (k+1) := by
    apply Nat.clog_le_of_le_pow
    rw [Nat.mul_comm, Nat.pow_mul]
    exact (Nat.succ_le_succ hQ).trans (grow.trans powBound)
  simpa only [payloadBits,Nat.mul_assoc] using Nat.mul_le_mul_left D clog

/-- A single size threshold admits every balanced depth, switch position,
active sublist and reserve-payment scale satisfying the stated polynomial
bound. The selected reserve degree depends only on the two polynomial degrees. -/
theorem eventually_native_admission (D pow : ℕ) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    let lowDegree := max 1 (D*(pow+1))
    ∀ᶠ k in Filter.atTop, ∀ {b n j Q : ℕ}
      (sel : Fin b → Fin (targetOrder (CoprimeBox.box k).length n).length),
      b ≤ blocksPerBatch k 4 (stride k) → Q ≤ (k+1)^pow →
      NativeAdmission sel k j (payloadBits lowDegree k) D Q ρ := by
  dsimp only
  obtain ⟨K,valid⟩ := CoprimeBox.eventually_valid
  filter_upwards [eventually_layout_room (max 1 (D*(pow+1))) 2, Controlled.eventually_clog_fits 40,
    Filter.eventually_ge_atTop K, Filter.eventually_ge_atTop (1:ℕ)] with k room hwidth hv hk
  intro b n j Q sel card scale
  have c := Nat.clog_mono_right 2 (show k ≤ k+1 by omega)
  have half : 2*BoxScale.width k ≤ k := by unfold BoxScale.width; omega
  apply native_admission hk h₀ h₁ (valid k hv) sel half room.1 card (by have := room.2.1; omega)
  · have pos := Nat.clog_pos (by decide : 1 < 2) (show 1 < k+1 by omega)
    exact Nat.mul_pos (by omega) pos
  · exact (payload_of_polynomial_scale (D:=D) hk scale).trans (Nat.mul_le_mul_right _ (le_max_right ..))

/-- The emitted directory may reserve exactly one sixteenth of the address
bits for the low payload, independently of the polynomial degree revealed
by the eventual row-program analysis. The external controls, guards and an
additional high reserve still fit for every selected batch. -/
theorem eventually_fixedLow_native_admission (D pow : ℕ) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    ∀ᶠ k in Filter.atTop, ∀ {b n j Q : ℕ}
      (sel : Fin b → Fin (targetOrder (CoprimeBox.box k).length n).length),
      b ≤ blocksPerBatch k 4 (stride k) → Q ≤ (k+1)^pow →
      NativeAdmission sel k j (k/16) D Q ρ := by
  obtain ⟨K,valid⟩ := CoprimeBox.eventually_valid
  filter_upwards [eventually_layout_room 0 0,Controlled.eventually_clog_fits 64,
    Controlled.eventually_clog_fits (16*(D*(pow+1))),Filter.eventually_ge_atTop K,
    Filter.eventually_ge_atTop (16:ℕ)] with k room hi lo hvalid hk
  intro b n j Q sel card scale
  have guard := room.1
  have width : BoxScale.width k ≤ stride k := le_max_right ..
  have res : 32*(k/16+payloadBits 2 k) ≤ 3*k := by unfold payloadBits; omega
  apply native_admission (by omega) h₀ h₁ (valid k hvalid) sel (by omega) guard card res (by omega)
  apply (payload_of_polynomial_scale (D:=D) (by omega) scale).trans
  unfold payloadBits
  rw [Nat.mul_assoc] at lo
  omega

theorem eventually_capacity_pos :
    ∀ᶠ k in Filter.atTop, 0 < blocksPerBatch k 4 (stride k) := by
  filter_upwards [eventually_layout_room 0 0] with k h
  have pos : 0 < stride k := (by unfold Controlled.guardWidth; omega : 0 < Controlled.guardWidth k).trans_le
    (le_max_left ..)
  exact Nat.div_pos h.1 (by positivity)

/-- The uniform polynomial certificate on an actual regime scale supplies a
single admission threshold, independent of all subbatch ports and depths. -/
theorem fixedLow_admission_of_dom {X : Type*} (k Q : X → ℕ) (scale : Code.Dom k Q)
    (D : ℕ) {ρ : ℝ} (h₀ : 0 ≤ ρ) (h₁ : ρ ≤ 1) :
    ∃ K : ℕ, ∀ x, K ≤ k x → ∀ {b n j : ℕ}
      (sel : Fin b → Fin (targetOrder (CoprimeBox.box (k x)).length n).length),
      b ≤ blocksPerBatch (k x) 4 (stride (k x)) →
      NativeAdmission sel (k x) j (k x/16) D (Q x) ρ := by
  obtain ⟨pow,C,bound⟩ := scale
  obtain ⟨cut,admit⟩ := Filter.eventually_atTop.mp (eventually_fixedLow_native_admission D (pow+1) h₀ h₁)
  refine ⟨max C cut,fun x hx b n j sel card => admit _ ((le_max_right ..).trans hx) sel card ?_⟩
  rw [pow_succ']
  exact (bound x).trans (Nat.mul_le_mul_right _ (by omega))

end FixedCandidate.CRTBudget

end NearSquareRoot
end Computability
end OAI
