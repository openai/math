import OAI.Hierarchy.TaggedPassRunCore
import OAI.Hierarchy.TaggedRadixChainCalls

namespace OAI
/-! # Cost and exposed gap of a physically installed radix pass sequence -/
noncomputable section
namespace Hierarchy.Tagged.Radix
open Catalyst CatalystSubstitution RadixStage ThreeFlat Routing
open scoped Classical BigOperators
variable {F : Type*} [Field F] {k h n : ℕ} {format : ℕ → PassFormat}

omit [Field F] in
private theorem chain_good (os : ℕ → List (Occurrence F k)) (n : ℕ) (P : Occurrence F k → Prop)
    (good : ∀ i,i≤n → ∀ o ∈ os i,P o) : ∀ o ∈ chainCalls os n,P o := by
  induction n with
  | zero => exact good 0 le_rfl
  | succ n ih =>
    intro o ho
    rcases List.mem_append.mp ho with hx|hx
    · exact ih (fun i hi => good i (Nat.le_succ_of_le hi)) o hx
    · exact good (n+1) le_rfl o hx

theorem StageRun.install {Y : ∀ i,(format i).Calls F k} (R : StageRun h n Y)
    {c : ℕ} (room : R.Room c) {L W G : ℝ} (paid : ∀ i,i≤n → (Y i).Paid L W G) :
    ∃ X : Approximation F k (pins h h),
      (X.size:ℝ) ≤ ((n+1:ℕ):ℝ)*(2*(c:ℝ)*((2:ℝ)^h*h)+2*L+W) ∧
      X.Gap (coeff F h h) (G-2*(k:ℝ)*(3*((n+1:ℕ):ℝ))) := by
  let os := fun i => (Y i).occurrences
  have allg := chain_good os n (fun o => o.replacement.Gap o.target G)
    (fun i hi => (paid i hi).gaps)
  obtain ⟨X,size,gap⟩ := install_chain R.state R.holes R.stage os R.sockets n R.run
    R.reachable R.computes R.keep R.scan R.feed R.start G allg
  rw [show (fun x => TypedWiring.value R.scan (advance R.state R.run n (Sum.elim x id ∘ R.feed))) =
    coeff F h h from funext R.finish] at gap
  have number : (chainCalls os n).length = (n+1)*3 := by
    rw [chainCalls_length]
    simp [os,PassFormat.Calls.occurrences]
  refine ⟨X,?_,by simpa [number,mul_comm] using gap⟩
  let bar := c*(2^h*h)
  have shell : (chain R.state R.holes R.stage n).cells + (chain R.state R.holes R.stage n).internal
      + Fintype.card (R.state (n+1)) ≤ (n+1)*bar := by
    rw [chain_cells,chain_internal]
    have final := Finset.sum_range_succ (fun i => Fintype.card (R.state (i+1))) n
    rw [show (∑ i ∈ Finset.range (n+1), (R.stage i).cells) +
       ((∑ i ∈ Finset.range (n+1), (R.stage i).internal)+
       ∑ i ∈ Finset.range n,Fintype.card (R.state (i+1)))+Fintype.card (R.state (n+1)) =
      ∑ i ∈ Finset.range (n+1),((R.stage i).cells+(R.stage i).internal+Fintype.card (R.state (i+1))) by
      simp only [Finset.sum_add_distrib,final]; omega]
    exact (Finset.sum_le_sum (fun i hi => room.pass i (by simpa using Finset.mem_range.mp hi))).trans_eq
      (by simp [bar])
  have frame := room.scan
  have fee : (∑ i ∈ Finset.range (n+1), ((((os i).map (·.replacement.size)).sum:ℕ):ℝ)) ≤
      ((n+1:ℕ):ℝ)*(2*L+W) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (n+1), (2*L+W) :=
        Finset.sum_le_sum (fun i hi => (paid i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).total)
      _ = ((n+1:ℕ):ℝ)*(2*L+W) := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have exactBill : X.size ≤ (n+1)*bar+bar+((chainCalls os n).map (·.replacement.size)).sum := by omega
  have bill : (X.size:ℝ) ≤ ((n+1:ℕ):ℝ)*(bar:ℝ)+(bar:ℝ)+
      ∑ i ∈ Finset.range (n+1), ((((os i).map (·.replacement.size)).sum:ℕ):ℝ) := by
    rw [chainCalls_total] at exactBill
    exact_mod_cast exactBill
  have fixed : (bar:ℝ) ≤ ((n+1:ℕ):ℝ)*bar := by
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) (by exact_mod_cast Nat.succ_pos n)
  have br : (bar:ℝ)=(c:ℝ)*((2:ℝ)^h*h) := by simp [bar]
  calc
    (X.size:ℝ) ≤ ((n+1:ℕ):ℝ)*(2*(bar:ℝ)+2*L+W) := by
      nlinarith only [bill,fee,fixed]
    _ = _ := by rw [br]; ring

end Hierarchy.Tagged.Radix

end
end OAI
