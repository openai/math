import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapRulers
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyTally
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect

/-! # Literal specialization of a joint Walsh ruler program

The source prelude writes five tally constants and preserves the input node
descriptor. A single body reads this pair, so its register cutoff and the
degree of its compact setup time are independent of all five constants.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapRulers

open IntegerMultiplication Code Strip PhysicalWalsh PhysicalWalshNode CommonRegisters GeneratorSyntax
open KernelEffectiveFamily Filter

variable {Z : Type} [Codec Z]

def Configured (f : World → Z) (extra : World → ℕ) (d : ℕ) (c : Control → Cmd) : Prop :=
  ∀ (a W : ℕ) (i j : Fin (a+1)) (D : ℕ), ∃ C : ℕ, ∀ (s : Shape) env r,
    let t : World := ⟨a,W,i,j,D,s⟩
    Fits env (c (control t)) (pile 0 (send (descriptor t)) r) (pile 0 (send (f t)) r)
      (C*((Header.scale (a+1) s+1)^d+extra t))

private theorem supply {R : ℕ} (hr : 3 ≤ R) :
    Family R (fun k : Control => fun w : Header.Wire =>
      (params k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2,w)) :=
  Family.pair hr (Family.pair hr (Family.tally (by omega) _ Computable.fst)
    (Family.pair hr (Family.tally (by omega) _ (Computable.fst.comp Computable.snd))
      (Family.pair hr (Family.tally (by omega) _ (Computable.fst.comp (Computable.snd.comp Computable.snd)))
        (Family.pair hr (Family.tally (by omega) _ (Computable.fst.comp
          (Computable.snd.comp (Computable.snd.comp Computable.snd))))
          (Family.tally (by omega) _ (Computable.snd.comp
            (Computable.snd.comp (Computable.snd.comp Computable.snd)))))))) Family.identity

private theorem specialize {f : World → Z} (t extra : World → ℕ) (small : Dom regime.scale t)
    (body : Task (fun u => t u+extra u) regime.header (send ∘ f)) :
    ∃ (R d : ℕ) (c : Control → Cmd), 1 ≤ d ∧ Effective ltr c ∧ (∀ k, Within R (c k)) ∧
      Configured f extra d c := by
  obtain ⟨clock,C,small⟩ := small
  obtain ⟨cmd,K,ok⟩ := body
  obtain ⟨R,hr,hreg⟩ := ((eventually_ge_atTop 3).and (RegisterSelect.within_eventually cmd)).exists
  obtain ⟨pre,eff,correct⟩ := supply hr
  refine ⟨R,clock+1,fun k => (pre k).join cmd,by omega,eff.join (effective_const ltr cmd),
    fun k => ⟨(correct k).1,hreg⟩,?_⟩
  intro a W i j D
  let k : Control := (a+1,W,i.val,j.val,D)
  let P := size (params (a+1) W i.val j.val D)+2
  let coeff := C*P^clock
  obtain ⟨B,hB⟩ := (correct k).2
  refine ⟨B+K*(coeff+1)+K+2,fun s env r => ?_⟩
  let u : World := ⟨a,W,i,j,D,s⟩
  let H := Header.scale (a+1) s+1
  let M := H^(clock+1)
  have hm : 1 ≤ M := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hH : H ≤ M := by simpa only [pow_one] using
    Nat.pow_le_pow_right (n:=H) (by dsimp [H]; omega) (by omega : 1 ≤ clock+1)
  have inputSize : regime.scale u+1 ≤ P*H := by
    change size (params (a+1) W i.val j.val D)+Header.scale (a+1) s+1+1 ≤
      (size (params (a+1) W i.val j.val D)+2)*(Header.scale (a+1) s+1)
    rw [Nat.mul_succ,Nat.add_mul]; omega
  have baseCost : t u ≤ coeff*M := by
    have hb := (small u).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left inputSize clock))
    rw [mul_pow,← Nat.mul_assoc] at hb
    exact hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)))
  have bodyCost : K*(t u+extra u+1) ≤ K*(coeff+1)*M+K*extra u := by
    rw [Nat.mul_assoc K, Nat.add_mul coeff, Nat.one_mul, ← Nat.mul_add]
    apply Nat.mul_le_mul_left
    omega
  have prefixCost := Nat.mul_le_mul_left B hH
  apply ((hB (Header.wire (a+1) s) env r).join (ok u env r)).mono
  change B*H + K*(t u+extra u+1)+2 ≤ (B+K*(coeff+1)+K+2)*(M+extra u)
  calc
    _ ≤ B*M + (K*(coeff+1)*M+K*extra u)+2 := by omega
    _ ≤ _ := by
      generalize K*(coeff+1) = J
      simp only [Nat.add_mul,Nat.mul_add]
      omega

/-- All five input parameters may vary in the generated source. The body
charges the compact polynomial setup and the actual emitted tape size. -/
theorem configuredMint {f : World → Z} (h : Mint regime f) :
    ∃ (R d : ℕ) (c : Control → Cmd), 1 ≤ d ∧ Effective ltr c ∧ (∀ k, Within R (c k)) ∧
      Configured f (size ∘ f) d c := by
  obtain ⟨t,small,body⟩ := h
  exact specialize t (size ∘ f) small body

/-- Compact outputs carry no separate output-length charge. -/
theorem configured {f : World → Z} (h : regime.Has f) :
    ∃ (R d : ℕ) (c : Control → Cmd), 1 ≤ d ∧ Effective ltr c ∧ (∀ k, Within R (c k)) ∧
      Configured f (fun _ => 0) d c := by
  obtain ⟨t,small,body⟩ := h
  exact specialize t (fun _ => 0) small (by simpa using body)

/-- The degree for lengths of compact emitted descriptors also works for every
choice of the five template constants. -/
theorem compact_size {f : World → Z} (h : regime.Has f) : ∃ d : ℕ,
    ∀ (a W : ℕ) (i j : Fin (a+1)) (D : ℕ), ∃ C : ℕ, ∀ (s : Shape),
      let u : World := ⟨a,W,i,j,D,s⟩
      size (f u) ≤ C*(Header.scale (a+1) s+1)^d := by
  obtain ⟨d,K,hK⟩ := Regime.Small.extent h
  refine ⟨d,fun a W i j D => ?_⟩
  let P := size (params (a+1) W i.val j.val D)+2
  refine ⟨K*P^d,fun s => ?_⟩
  let u : World := ⟨a,W,i,j,D,s⟩
  have budget : regime.scale u+1 ≤ P*(Header.scale (a+1) s+1) := by
    change size (params (a+1) W i.val j.val D)+Header.scale (a+1) s+1+1 ≤
      (size (params (a+1) W i.val j.val D)+2)*(Header.scale (a+1) s+1)
    rw [Nat.mul_succ,Nat.add_mul]; omega
  change ((send ∘ f) u).count ≤ K*P^d*(Header.scale (a+1) s+1)^d
  simpa only [mul_pow,Nat.mul_assoc] using
    (hK u).trans (Nat.mul_le_mul_left K (Nat.pow_le_pow_left budget d))

end PhysicalWalshCompileSwapRulers

end NearSquareRoot
end Computability
end OAI
