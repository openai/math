import OAI.Optimization.LinearProgramming.Compression.ProxyQueryRAM
import OAI.Optimization.LinearProgramming.RAM.CallableWindow

/-! Polynomial address windows for initializing and resetting both forms of the proxy-query tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- The signed-token budget counts ordinary binary digits and framing words. -/
def preparedTokenBudget (n fuel : ℕ) : ℕ := 2*(2*fuel+3)+3+n*(2*(fuel+3)+3)

def preparedProxyRawSpan (n fuel : ℕ) : ℕ := 3*preparedTokenBudget n fuel + n + 16

def preparedProxyTapeSpan (n fuel : ℕ) : ℕ := 2*(preparedProxyRawSpan n fuel+1)

theorem preparedProxyRawSpan_le (n fuel : ℕ) : preparedProxyRawSpan n fuel ≤ 64*(n+1)*(fuel+1) := by
  unfold preparedProxyRawSpan preparedTokenBudget
  nlinarith

theorem preparedProxyTapeSpan_le (n fuel : ℕ) : preparedProxyTapeSpan n fuel ≤ 128*(n+1)*(fuel+1) := by
  unfold preparedProxyTapeSpan preparedProxyRawSpan preparedTokenBudget
  nlinarith

private theorem tokenCode_bound (t : PowerToken) : t.code ≤ 4 := by
  cases t with
  | beginTerm => decide
  | bit v | finish v => cases v <;> decide

private theorem encoder_length (ts : List PowerToken) : (powerEncoderAddressInput ts).length = 3*ts.length+8 := by
  simp [powerEncoderAddressInput]; omega

private theorem encoder_word (ts : List PowerToken) (x : ℕ) (hx : x ∈ powerEncoderAddressInput ts) :
    x ≤ 3*ts.length+8 := by
  simp only [powerEncoderAddressInput,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) | hz | hm
  all_goals try omega
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp hz
    omega
  · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hm
    have h := tokenCode_bound t
    omega

private theorem tokenLength_le (ps : List (ℚ × ℤ)) :
    (signedBitTape (ps.map Prod.snd)).length ≤ (ps.map fun p => 2*p.2.natAbs.size+3).sum := by
  rw [signedBitTape_length]
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons,List.sum_cons]; omega

private theorem sum_le_len (xs : List ℕ) (M : ℕ) (h : ∀ x ∈ xs, x≤M) : xs.sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

private theorem prepared_raw_shape {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0<mag i)
    (hbits : ∀ i, ratBits (mag i) ≤ B) (hform : |c|+∑ i, |a i| ≤ A)
    (hcut : (2:ℤ)^prec*A ≤ 2^fuel) :
    let p := preparedProxyQuery fuel prec c a mag
    let room := preparedProxyRawSpan n fuel
    p.address.length ≤ room ∧ p.scalar.length ≤ room ∧ ∀ x∈p.address, x≤room := by
  classical
  dsimp only
  by_cases hn : proxyLargeIndices fuel prec mag = []
  · simp only [preparedProxyQuery,ite_eq_left hn,List.length_cons,List.length_nil,affineInputPairs_length]
    unfold preparedProxyRawSpan preparedTokenBudget
    refine ⟨by omega,by nlinarith,?_⟩
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    omega
  · let idx := proxyLargeIndices fuel prec mag
    let large := Finset.univ.filter fun i => logProxyNumerator fuel prec (mag i) = none
    let D : ℕ := 2^(prec+2)
    let grid i := (logProxyNumerator fuel prec (mag i)).getD 0
    let off := clearedProxyOffset large D c a grid
    let ps := proxyPowerOperands idx off D a mag
    let ts := signedBitTape (ps.map Prod.snd)
    have hs : ∃ j, logProxyNumerator fuel prec (mag j) = none := by
      by_contra! h
      exact hn ((proxyLargeIndices_empty_iff fuel prec mag).mpr h)
    have heq : (proxyLargeIndices fuel prec mag).toFinset = large := by
      ext i; simp [large,mem_proxyLargeIndices]
    have hp := proxyLargeIndices_perm fuel prec mag
    have hp' : ps.Perm (proxyPowerOperands large.toList off D a mag) :=
      List.Perm.cons _ (hp.map (fun i => (mag i,(D:ℤ)*a i)))
    have hb := (computedProxy_operand_bounds fuel prec B c a mag hm hbits hform hcut hs).2.2
    have ht : ts.length ≤ preparedTokenBudget n fuel := (tokenLength_le ps).trans <|
      (hp'.map (fun p => 2*p.2.natAbs.size+3)).sum_eq.le.trans (by simpa only [preparedTokenBudget,large,off,D,grid,Fintype.card_fin] using hb)
    have hidx : idx.length ≤ n := by
      simpa [idx,proxyLargeIndices] using (List.length_filter_le (fun i : Fin n =>
        (logProxyNumerator fuel prec (mag i)).isNone) (List.finRange n))
    simp only [preparedProxyQuery,ite_eq_right hn,heq]
    change (powerEncoderAddressInput ts).length ≤ _ ∧ (powerTapeScalarInput (ps.map Prod.fst)).length ≤ _ ∧ _
    rw [encoder_length]
    have hx : (powerTapeScalarInput (ps.map Prod.fst)).length = 5+idx.length := by
      simp [powerTapeScalarInput,ps,proxyPowerOperands]; omega
    rw [hx]
    unfold preparedProxyRawSpan
    exact ⟨by omega,by omega,fun x h => (encoder_word ts x h).trans (by omega)⟩

/-- A caller invoking the branch directly can clear this raw window on each call. -/
theorem preparedProxyQuery_raw_window {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0<mag i)
    (hbits : ∀ i, ratBits (mag i) ≤ B) (hform : |c|+∑ i, |a i| ≤ A)
    (hcut : (2:ℤ)^prec*A ≤ 2^fuel) :
    let p := preparedProxyQuery fuel prec c a mag
    let room := preparedProxyRawSpan n fuel
    p.address.length ≤ room ∧ p.scalar.length ≤ room ∧ p.address.sum ≤ room^2 ∧ ∀ x∈p.address,x≤room := by
  obtain ⟨hd,hs,hw⟩ := prepared_raw_shape fuel prec B c a mag hm hbits hform hcut
  exact ⟨hd,hs,(sum_le_len _ _ hw).trans (by simpa only [pow_two] using Nat.mul_le_mul_right _ hd),hw⟩

private theorem dispatch_word (b : Bool) (xs : List ℕ) (M : ℕ) (hM : ∀ x∈xs,x≤M) :
    ∀ w∈dispatchDims b xs, w≤2*(M+1) := by
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  change (if i.val%2=0 then 2*(xs[i.val/2]?.getD 0) else if i.val/2=0 then b.toNat else 0) ≤ _
  have h : xs[i.val/2]?.getD 0 ≤ M := by
    by_cases hi : i.val/2 < xs.length
    · simpa [List.getElem?_eq_getElem hi] using hM xs[i.val/2] (List.getElem_mem _)
    · simp [List.getElem?_eq_none (by omega : xs.length ≤ i.val/2)]
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  split_ifs <;> omega

/-- Every input word, both actual tape lengths, and the sum of the address words have
polynomial envelopes independent of the rational data and precision parameter. -/
theorem preparedProxyQuery_window {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0<mag i)
    (hbits : ∀ i, ratBits (mag i) ≤ B) (hform : |c|+∑ i, |a i| ≤ A)
    (hcut : (2:ℤ)^prec*A ≤ 2^fuel) :
    let p := preparedProxyQuery fuel prec c a mag
    let dims := dispatchDims p.symbolic p.address
    let scalars := dispatchScalars p.scalar
    let room := preparedProxyTapeSpan n fuel
    dims.length ≤ room ∧ scalars.length ≤ room ∧ dims.sum ≤ room^2 ∧ ∀ x∈dims,x≤room := by
  obtain ⟨hd,hs,hw⟩ := prepared_raw_shape fuel prec B c a mag hm hbits hform hcut
  let p := preparedProxyQuery fuel prec c a mag
  let dims := dispatchDims p.symbolic p.address
  let room := preparedProxyTapeSpan n fuel
  have hl : dims.length ≤ room := by simp only [dims,p,room,length_dispatchDims,preparedProxyTapeSpan]; omega
  have hx := dispatch_word p.symbolic p.address _ hw
  refine ⟨hl,?_,(sum_le_len dims room hx).trans (by simpa only [pow_two] using Nat.mul_le_mul_right room hl),hx⟩
  simp only [length_dispatchScalars,preparedProxyTapeSpan]
  omega

/-- The exact reset-window expression used by an arbitrary fixed native branch program. -/
theorem preparedProxyQuery_raw_nativeWindow (prog : Program) {n : ℕ} (fuel prec B : ℕ) {A : ℤ}
    (c : ℤ) (a : Fin n → ℤ) (mag : Fin n → ℚ) (hm : ∀ i, 0<mag i)
    (hbits : ∀ i, ratBits (mag i) ≤ B) (hform : |c|+∑ i, |a i| ≤ A)
    (hcut : (2:ℤ)^prec*A ≤ 2^fuel) :
    let p := preparedProxyQuery fuel prec c a mag
    Callable.nativeWindow prog p.address p.scalar ≤ max (addressBudget prog) ((preparedProxyRawSpan n fuel)^2) := by
  let room := preparedProxyRawSpan n fuel
  obtain ⟨hd,hs,hw,_⟩ := preparedProxyQuery_raw_window fuel prec B c a mag hm hbits hform hcut
  have hroom : room ≤ room^2 := Nat.le_self_pow (by decide) room
  exact max_le_max le_rfl (max_le (hs.trans hroom) (max_le (hd.trans hroom) hw))

end Compression
end LinearProgramming
end Optimization
end OAI
