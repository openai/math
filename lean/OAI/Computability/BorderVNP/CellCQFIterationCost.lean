import OAI.Computability.BorderVNP.CellCQFCost
import OAI.Computability.QuantumFactoring.BitStackNaturals

/-! # Actual cost of bounded iteration in the private packet compiler

One unary loop token pays one dispatch and one invocation of the body. The
two moves into and out of the fixed in-place register are charged at the
lengths of the *actual* intermediate values.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {α : Type} {ea : α → List Bool} {f : α → α}

/-- Reusing a designated argument register incurs two linear word moves in addition to the native call. -/
theorem cost_inplace (p : Procedure ea ea f) (a : α) :
    p.inplace.cost a ≤ p.cost a + 4*(ea a).length + 4*(ea (f a)).length + 4 := by
  have h₁ := moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1) (by simp) (by simp) (by simp) (ea a)
  have h₂ := (p.ticks_cost a).relabel (leftEmbed p.K (Fin 2)) (fun _ => [])
  simp only [overlay_singleton] at h₂
  have h₃ := moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1) (by simp) (by simp) (by simp) (ea (f a))
  exact (p.inplace.cost_le_of_ticks (Runs.seq h₁ (Runs.seq h₂ h₃))).trans (by omega)

private theorem loop_clock {L : Type} [DecidableEq L] (p : Procedure ea ea f)
    (he : p.output=p.input) (k : L) (n : ℕ) (a : α) (C : ℕ)
    (hC : ∀ i<n, p.cost ((f^[i]) a) ≤ C) (s : Store L) (hs : s k=List.replicate n true) :
    ∃ c ≤ n*(C+1)+1, Runs (.loop (Sum.inr k) (p.program.relabel Sum.inl) (p.program.relabel Sum.inl))
        (sumStore (singletonStore p.input (ea a)) s)
        (sumStore (singletonStore p.input (ea ((f^[n]) a))) (Function.update s k [])) c := by
  induction n generalizing a s with
  | zero =>
    have hu : Function.update s k [] = s := by
      change s k = [] at hs
      rw [← hs,Function.update_eq_self]
    rw [Function.iterate_zero_apply,hu]
    exact ⟨1,by simp,Runs.loop_nil hs⟩
  | succ n ih =>
    let t := Function.update s k (List.replicate n true)
    obtain ⟨ct,hct,rest⟩ := ih (f a) (fun i hi => by simpa only [Function.iterate_succ_apply] using hC (i+1) (by omega))
      t (Function.update_self ..)
    have one := p.ticks_cost a
    change Runs p.program _ (singletonStore p.output _) _ at one
    rw [he] at one
    have body := one.left t
    have head : sumStore (singletonStore p.input (ea a)) s (Sum.inr k)=true::List.replicate n true := by
      simpa only [sumStore_right,List.replicate_succ] using hs
    have run := Runs.loop_true head (by simpa only [sumStore_update_right] using body) rest
    refine ⟨ct+p.cost a+1,?_,?_⟩
    · have h := hC 0 (by omega)
      rw [Function.iterate_zero_apply] at h
      rw [Nat.succ_mul]
      omega
    · simpa only [t,Function.update_idem,Function.iterate_succ_apply] using run

private theorem move_on_bank {K : Type} [DecidableEq K] (a b z : K) (hab : a≠b) (haz : a≠z) (hbz : b≠z)
    (s : Store K) (hz : s z = []) (hb : s b = []) :
    Runs (moveWord a b z) s (Function.update (Function.update s a []) b (s a)) (4*(s a).length+2) := by
  let t := Function.update (Function.update s a []) z (s a).reverse
  have h₁ : Runs (reverseMove a z) s t (2*(s a).length+1) := by simpa [t,hz] using reverseMove_runs a z haz s
  have h₂ := reverseMove_runs z b hbz.symm t
  have htz : t z = (s a).reverse := Function.update_self ..
  have htb : t b = [] := by simp [t,hbz,Ne.symm hab,hb]
  rw [htz,htb,List.reverse_reverse,List.append_nil,List.length_reverse] at h₂
  have he : Function.update t z [] = Function.update s a [] := by
    dsimp [t]
    rw [Function.update_idem]
    apply Function.update_eq_self_iff.mpr
    rw [Function.update_of_ne haz.symm,hz]
  rw [he] at h₂
  have hh := Runs.seq h₁ h₂
  unfold moveWord
  rw [← show 2*(s a).length+1+(2*(s a).length+1) = 4*(s a).length+2 by omega]
  exact hh

/-- Charge the actual body on the orbit visited by the installed iterator. The
size invariant in its type can use any growth polynomial. Only visited lengths
and costs enter the displayed estimate. -/
theorem cost_iterate (p : Procedure ea ea f) (q : Polynomial ℕ)
    (growth : ∀ n a i, i ≤ n → (ea ((f^[i]) a)).length ≤ q.eval (n+(ea a).length))
    (n : ℕ) (a : α) {L C : ℕ} (hL : ∀ i ≤ n, (ea ((f^[i]) a)).length ≤ L)
    (hC : ∀ i < n, p.cost ((f^[i]) a) ≤ C) :
    (p.iterate q growth).cost (n,a) ≤ n*(C+8*L+5)+7*n+4*(ea a).length+9 := by
  let r := p.inplace
  let s : Store (r.K ⊕ Fin 4) := singletonStore (.inr 0) (prodCode unaryCode ea (n,a))
  let u : Store (r.K ⊕ Fin 4) := Function.update (singletonStore (.inr 0) (ea a)) (.inr 1) (List.replicate n true)
  let v := sumStore (singletonStore r.input (ea a)) (singletonStore (1 : Fin 4) (List.replicate n true))
  have parse : Runs (unquoteMove (.inr 0) (.inr 1) (.inr 2) (.inr 3)) s u (7*n+6) := by
    have run := unquoteMove_runs (Sum.inr 0 : r.K ⊕ Fin 4) (.inr 1) (.inr 2) (.inr 3)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (List.replicate n true) (ea a) s
      (by simp [s,singletonStore,prodCode,pairBits,unaryCode]) (by simp [s,singletonStore]) (by simp [s,singletonStore])
    have h₁ : s (.inr 1) = [] := by simp [s,singletonStore]
    rw [h₁,List.append_nil,List.length_replicate] at run
    simpa only [s,u,singletonStore,Function.update_idem] using run
  have move : Runs (moveWord (.inr 0) (.inl r.input) (.inr 2)) u v (4*(ea a).length+2) := by
    have h := move_on_bank (Sum.inr 0 : r.K ⊕ Fin 4) (.inl r.input) (.inr 2) (by simp) (by simp) (by simp)
      u (by simp [u,singletonStore]) (by simp [u,singletonStore])
    have h₀ : u (.inr 0) = ea a := by simp [u,singletonStore]
    rw [h₀] at h
    convert h using 1
    funext j
    cases j with
    | inl k => by_cases hk : k=r.input <;> simp [v,u,singletonStore,Function.update,hk]
    | inr i => fin_cases i <;> simp [v,u,singletonStore,Function.update]
  have hb (i : ℕ) (hi : i < n) : r.cost ((f^[i]) a) ≤ C+8*L+4 := by
    apply (cost_inplace p _).trans
    have h₀ := hL i hi.le
    have h₁ := hL (i+1) hi
    rw [Function.iterate_succ_apply'] at h₁
    have := hC i hi
    omega
  obtain ⟨cl,hcl,loop⟩ := loop_clock r rfl (1 : Fin 4) n a _ hb (singletonStore 1 (List.replicate n true)) (by simp [singletonStore])
  have final : sumStore (singletonStore r.input (ea ((f^[n]) a)))
      (Function.update (singletonStore (1 : Fin 4) (List.replicate n true)) 1 []) =
      singletonStore (Sum.inl r.input) (ea ((f^[n]) a)) := by
    rw [sumStore_singleton_left]
    congr 1
    funext k
    fin_cases k <;> simp [singletonStore,Function.update]
  rw [final] at loop
  apply ((p.iterate q growth).cost_le_of_ticks (a := (n,a)) (Runs.seq parse (Runs.seq move loop))).trans
  rw [show C+8*L+4+1 = C+8*L+5 by omega] at hcl
  omega

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  cost_inplace
  cost_iterate)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
