import OAI.Computability.BorderVNP.PackedDirectoryISA
import OAI.Computability.BorderVNP.DiagonalResidueRAMFrame

/-! # Native stores for the seven-word placement directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory.ISA

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open DiagonalResidueRAM (word word_val word_add)

variable {w : ℕ}

/-- Chronological stores at consecutive natural addresses. -/
def putWords (m : Memory w) (atWord : ℕ) : List (Word w) → Memory w
  | [] => m
  | x::xs => putWords (Function.update m atWord x) (atWord+1) xs

/-- The seven-word writer fills just the declared interval. -/
theorem putWords_outside (m : Memory w) (a j : ℕ) (xs : List (Word w))
    (outside : j < a ∨ a + xs.length ≤ j) : putWords m a xs j = m j := by
  induction xs generalizing a m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at outside
    rw [putWords, ih (Function.update m a x) (a+1) (by omega), Function.update_of_ne (by omega : j ≠ a)]

/-- The output directory can be appended by emitting successive record intervals. -/
theorem putWords_append (m : Memory w) (a : ℕ) (xs ys : List (Word w)) :
    putWords m a (xs++ys) = putWords (putWords m a xs) (a+xs.length) ys := by
  induction xs generalizing m a with
  | nil => simp [putWords]
  | cons x xs ih => simp only [List.cons_append, List.length_cons, putWords, ih]; congr 1; omega

/-- The word at any written address is the matching source-list element. -/
theorem putWords_read (m : Memory w) (a : ℕ) (xs : List (Word w)) (i : Fin xs.length) :
    putWords m a xs (a+i) = xs[i] := by
  induction xs generalizing m a with
  | nil => exact i.elim0
  | cons x xs ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.val_zero, Nat.add_zero, putWords]
      rw [putWords_outside _ _ _ _ (Or.inl (by omega)), Function.update_self]
      rfl
    · simp only [Fin.val_succ, putWords]
      simpa [Nat.add_assoc, Nat.add_comm 1] using ih (Function.update m a x) (a+1) k

/-- A list of store/increment instructions copies exactly the requested registers into
memory, preserving their values and advancing the cursor once per word. -/
theorem pushWords_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (rs : List Reg)
    (s : Bank w) (m : Memory w) (a : ℕ) (hc : s 20 = word w a) (hu : s 1 = 1)
    (hfit : a + rs.length < 2^w) (hreg : ∀ r ∈ rs, r ≠ 20) :
    ∃ es, Runs pub macros (pushWords rs) s m es
      (Function.update s 20 (word w (a+rs.length))) (putWords m a (rs.map s)) ∧
      traceCost es = 2*rs.length+1 := by
  induction rs generalizing s m a with
  | nil =>
    simp only [List.length_nil, Nat.add_zero, List.map_nil, putWords, pushWords, ← hc, Function.update_eq_self]
    exact ⟨_, Runs.localStep m rfl rfl, rfl⟩
  | cons r rs ih =>
    simp only [List.length_cons] at hfit
    have ha : (s 20).val = a := hc ▸ word_val w a (by omega)
    let m' := Function.update m a (s r)
    let s' := Function.update s 20 (word w (a+1))
    have store := Runs.store pub macros 20 r s m
    rw [ha] at store
    have add : Runs pub macros (.binary .add 20 20 1) s m' [tick w] s' m' := by
      apply Runs.localStep _ rfl
      simp only [s',Code.atom,BinaryOp.eval,hc,hu,word_add,DiagonalResidueRAM.word_one]
      rfl
    have hs' : s' 1 = 1 := by simpa [s'] using hu
    obtain ⟨es,h,ct⟩ := ih s' m' (a+1) (Function.update_self ..) hs' (by omega)
      (fun v hv => hreg v (List.mem_cons_of_mem _ hv))
    have map_eq : rs.map s' = rs.map s := by
      apply List.map_congr_left
      intro v hv
      exact Function.update_of_ne (hreg v (List.mem_cons_of_mem _ hv)) ..
    have rend : Function.update s' 20 (word w (a+1+rs.length)) =
        Function.update s 20 (word w (a+(rs.length+1))) := by
      dsimp only [s']; rw [Function.update_idem]; congr 2; omega
    rw [rend, map_eq] at h
    exact ⟨_, .seq store (.seq add h), by
      change 1+(1+traceCost es) = 2*(rs.length+1)+1
      omega⟩

end Packing.Directory.ISA

end BorderVNP
end Computability
end OAI
