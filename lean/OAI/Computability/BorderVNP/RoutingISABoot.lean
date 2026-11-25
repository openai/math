import OAI.Computability.BorderVNP.RoutingISALink
import OAI.Computability.BorderVNP.RoutingISANatural

/-!
# Initializing the evaluator's shared-memory frame

Initially only the prescribed literal, exterior and pin words occupy RAM.
Public operand zero names the scratch frame. The remaining 31 public words
are read from the pinned processor parameters and stored by actual RAM
instructions. Fields counting dynamic records can initially be zero and are
written by the descriptor stages after reconstruction from the common header.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Install one public operand at the corresponding scratch-frame index. -/
def bootStep (i : Fin 31) : Code := .block [
  .publicWord 59 ⟨i.val + 1, by omega⟩, .constant 63 (Fin.ofNat _ i.val),
  .binary .add 62 60 63, .store 62 59]

/-- The initializer is a statically unrolled sequence of genuine stores. -/
def bootRows : (n : ℕ) → n ≤ 31 → Code
  | 0, _ => .nop
  | n+1, h => .seq (bootRows n (by omega)) (bootStep ⟨n, by omega⟩)

/-- Copy the finite parameter tuple into previously uninitialized shared RAM. -/
def bootFrame : Code := .seq (.publicWord 60 0) (bootRows 31 le_rfl)

/-- The initialization image at an intermediate program boundary. -/
def bootMemory {w : ℕ} (pub : Arg → Word w) (initial : Memory w) (count addr : ℕ) : Word w :=
  if h : (pub 0).val ≤ addr ∧ addr - (pub 0).val < count ∧ addr - (pub 0).val < 31 then
    pub ⟨addr - (pub 0).val + 1, by omega⟩
  else initial addr

private theorem bootMemory_zero {w : ℕ} (pub : Arg → Word w) (initial : Memory w) :
    bootMemory pub initial 0 = initial := by funext a; simp [bootMemory]

private theorem bootMemory_succ {w : ℕ} (pub : Arg → Word w) (initial : Memory w) (i : Fin 31) :
    Function.update (bootMemory pub initial i.val) ((pub 0).val + i.val)
      (pub ⟨i.val + 1, by omega⟩) = bootMemory pub initial (i.val+1) := by
  funext a
  by_cases ha : a = (pub 0).val+i.val
  · subst a
    simp [bootMemory, i.isLt]
  · rw [Function.update_of_ne ha]
    unfold bootMemory
    split_ifs with h₁ h₂ <;> first | rfl | omega

private theorem bootStep_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (i : Fin 31) (hs : s 60 = pub 0)
    (fits : (pub 0).val+31 ≤ 2^w) :
    ∃ es t, Runs pub macros (bootStep i) s m es t
      (Function.update m ((pub 0).val+i.val) (pub ⟨i.val+1, by omega⟩)) ∧
      t 60 = pub 0 ∧ traceCost es = 4 := by
  let r₁ : Bank w := Function.update s 59 (pub ⟨i.val+1, by omega⟩)
  let imm : Word 8 := Fin.ofNat _ i.val
  let v : Word w := Fin.ofNat _ imm.val
  let r₂ : Bank w := Function.update r₁ 63 v
  let r₃ : Bank w := Function.update r₂ 62 (BinaryOp.add.eval (r₂ 60) (r₂ 63))
  have a : Runs pub macros (.publicWord 59 ⟨i.val+1,by omega⟩) s m [tick w] r₁ m :=
    Runs.localStep m rfl rfl
  have b : Runs pub macros (.constant 63 imm) r₁ m [tick w] r₂ m := Runs.localStep m rfl rfl
  have c : Runs pub macros (.binary .add 62 60 63) r₂ m [tick w] r₃ m := Runs.localStep m rfl rfl
  have d := Runs.store pub macros 62 59 r₃ m
  have addr : (r₃ 62).val = (pub 0).val + i.val := by
    have hi := i.isLt
    simp only [r₃, Function.update_self, BinaryOp.eval, r₂, Function.update_of_ne (by decide : (60:Reg) ≠ 63),
      r₁, Function.update_of_ne (by decide : (60:Reg) ≠ 59), hs, Fin.val_add,
      v, imm, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : i.val < 2^8),
      Nat.mod_eq_of_lt (by omega : i.val < 2^w), Nat.mod_eq_of_lt (by omega : (pub 0).val+i.val < 2^w)]
  have val : r₃ 59 = pub ⟨i.val+1,by omega⟩ := by simp [r₃,r₂,r₁,Function.update]
  have final := a.seq (b.seq (c.seq d))
  rw [addr, val] at final
  refine ⟨_,r₃,final,?_,?_⟩
  · simp [r₃,r₂,r₁,Function.update,hs]
  · rfl

private theorem bootRows_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hs : s 60 = pub 0) (fits : (pub 0).val+31 ≤ 2^w)
    (n : ℕ) (hn : n ≤ 31) :
    ∃ es t, Runs pub macros (bootRows n hn) s m es t (bootMemory pub m n) ∧
      t 60 = pub 0 ∧ traceCost es = 1+4*n := by
  induction n with
  | zero =>
    rw [bootMemory_zero]
    exact ⟨_,s,Runs.localStep m rfl rfl,hs,rfl⟩
  | succ j ih =>
    obtain ⟨es,t,r,ht,he⟩ := ih (by omega)
    let i : Fin 31 := ⟨j,by omega⟩
    obtain ⟨fs,z,r',hz,hf⟩ := bootStep_run pub macros t (bootMemory pub m j) i ht fits
    rw [bootMemory_succ pub m i] at r'
    refine ⟨_,z,r.seq r',hz,?_⟩
    change VPVNP.RAMBuckets.cost _ (es++fs) = _
    rw [VPVNP.RAMBuckets.cost_append]
    change traceCost es + traceCost fs = _
    omega

/-- On true shared memory the fixed initializer writes exactly the declared
31 words, preserves every outside address, and uses 126 logical ticks. -/
theorem bootFrame_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (fits : (pub 0).val+31 ≤ 2^w) :
    ∃ es t, Runs pub macros bootFrame s m es t (bootMemory pub m 31) ∧ traceCost es = 126 := by
  let t := Function.update s 60 (pub 0)
  have first : Runs pub macros (.publicWord 60 0) s m [tick w] t m := Runs.localStep m rfl rfl
  obtain ⟨es,z,next,_,hcost⟩ := bootRows_run pub macros t m (Function.update_self ..) fits 31 le_rfl
  refine ⟨_,z,first.seq next,?_⟩
  change 1 + traceCost es = 126
  omega

end RoutingISA

end BorderVNP
end Computability
end OAI
