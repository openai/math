import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildHeader
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyTally
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect

/-! # Effective source specialization of the recursive descriptor command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileChild

open IntegerMultiplication Code Strip PhysicalWalshNode CommonRegisters GeneratorSyntax
open KernelEffectiveFamily Filter

abbrev Control := ℕ × ℕ × ℕ

def ConfiguredWith {H : Type} [Codec H] (f : World → H) (d : ℕ) (c : Control → Cmd) : Prop :=
  ∀ (a W : ℕ) (axis : Fin (a+1)), ∃ C : ℕ, ∀ (s : Shape),
    let t := (⟨a,W,axis,s⟩ : World)
    (∀ env r, Fits env (c (a+1,W,axis.val)) (pile 0 (send (Header.wire (a+1) s)) r)
      (pile 0 (send (f t)) r) (C*(Header.scale (a+1) s+1)^d)) ∧
      size (f t) ≤ C*(Header.scale (a+1) s+1)^d

abbrev Configured := ConfiguredWith tag

private theorem supply {R : ℕ} (hr : 3 ≤ R) :
    Family R (fun k : Control => fun w : Header.Wire => (params k.1 k.2.1 k.2.2,w)) :=
  Family.pair hr (Family.pair hr (Family.tally (by omega) _ Computable.fst)
    (Family.pair hr (Family.tally (by omega) _ (Computable.fst.comp Computable.snd))
      (Family.tally (by omega) _ (Computable.snd.comp Computable.snd)))) Family.identity

/-- The same register cutoff and polynomial degree apply to the full
parameterized compact descriptor generator, including its literal prelude. -/
theorem configuredWith {H : Type} [Codec H] (f : World → H) (hf : regime.Has f) : ∃ (R d : ℕ) (c : Control → Cmd), 1 ≤ d ∧
    Effective ltr c ∧ (∀ k, Within R (c k)) ∧ ConfiguredWith f d c := by
  have ext : Dom regime.scale (fun t => size (f t)) := Regime.Small.extent hf
  obtain ⟨clock,dt,body,K,hbody⟩ := hf
  obtain ⟨d,C,bound⟩ := dt.add ext
  obtain ⟨R,hr,hreg⟩ := ((eventually_ge_atTop 3).and (RegisterSelect.within_eventually body)).exists
  obtain ⟨pre,he,hpre⟩ := supply hr
  refine ⟨R,d+1,fun k => (pre k).join body,by omega,he.join (effective_const ltr body),
    fun k => ⟨(hpre k).1,hreg⟩,?_⟩
  intro a W ax
  let k : Control := (a+1,W,ax.val)
  obtain ⟨B,hB⟩ := (hpre k).2
  let P := size (params (a+1) W ax.val)+2
  let D := C*P^d
  refine ⟨B+K*(D+1)+D+2,fun s => ?_⟩
  let t : World := ⟨a,W,ax,s⟩
  let N := Header.scale (a+1) s+1
  have npos : 0 < N := Nat.succ_pos _
  have qpos : 1 ≤ N^(d+1) := Nat.one_le_pow _ _ npos
  have nle : N ≤ N^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right npos (by omega : 1 ≤ d+1)
  have inp : regime.scale t+1 ≤ P*N := by
    change size (params (a+1) W ax.val) + Header.scale (a+1) s +1+1 ≤
      (size (params (a+1) W ax.val)+2)*(Header.scale (a+1) s+1)
    rw [Nat.mul_succ,Nat.add_mul]; omega
  have caps : clock t + size (f t) ≤ D*N^(d+1) := by
    have h := (bound t).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left inp d))
    rw [mul_pow,← Nat.mul_assoc] at h
    exact h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right npos (by omega)))
  have timeGen : K*(clock t+1) ≤ (K*(D+1))*N^(d+1) := by
    rw [Nat.mul_assoc,Nat.succ_mul]
    exact Nat.mul_le_mul_left K (by omega)
  have timePre := Nat.mul_le_mul_left B nle
  constructor
  · intro env r
    have first := hB (Header.wire (a+1) s) env r
    have bod := hbody t env r
    apply (first.join bod).mono
    change B*N + K*(clock t+1)+2 ≤ (B+K*(D+1)+D+2)*N^(d+1)
    simp only [Nat.add_mul]; omega
  · change size (f t) ≤ (B+K*(D+1)+D+2)*N^(d+1)
    simp only [Nat.add_mul]; omega

/-- Specialize the emitter to the tagged recursive child descriptor. -/
theorem configured : ∃ (R d : ℕ) (c : Control → Cmd), 1 ≤ d ∧
    Effective ltr c ∧ (∀ k, Within R (c k)) ∧ Configured d c :=
  configuredWith tag generated

end PhysicalWalshCompileChild

end NearSquareRoot
end Computability
end OAI
