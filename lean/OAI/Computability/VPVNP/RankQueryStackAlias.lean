import OAI.Computability.VPVNP.RankQueryStackEngineSpec
import OAI.Computability.VPVNP.RankQueryStackPhysical

/-!
# Register aliases between the determinant engine and its arithmetic bank

Schur instructions read the six live query fields directly. Child instructions
also read the saved loop index. Output registers and temporary word stacks
belong to the auxiliary bank. The routine preserves the entire live frame and
history, as well as every auxiliary port outside the register bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.EngineAlias

open Dispatch Engine BurstRAM RAMTape

/-- Register count for the aliased dispatcher, including eight input words, six outputs and the
scratch bank. -/
abbrev R := 14+Dispatch.capacity
/-- Register-machine ports for the dispatcher with no public-word inputs. -/
abbrev Small := ISA.Port R 0
/-- Indices of the dispatcher's physical registers. -/
abbrev Reg := Fin R

/-- Identify the six query inputs and, when enabled, the count input with their corresponding
live-frame slots. -/
def liveSlot (countLive : Bool) : Small → Option (Fin 10)
  | .reg i => if h : i.val < 6 ∨ countLive = true ∧ i.val = 6 then
      some ⟨i.val+1, by omega⟩ else none
  | _ => none

private theorem liveSlot_info {flag : Bool} {port : Small} {j : Fin 10} (he : liveSlot flag port = some j) :
    ∃ i : Reg, port = .reg i ∧ j.val = i.val+1 ∧ (i.val < 6 ∨ flag = true ∧ i.val = 6) := by
  cases port with
  | reg i =>
    simp only [liveSlot] at he
    split_ifs at he with h
    cases he
    exact ⟨i,rfl,rfl,h⟩
  | pub | persistent | work | logPort => contradiction

variable {K : Type}

/-- Route aliased inputs to the live frame and the remaining dispatcher ports through the
supplied auxiliary bank. -/
def ports (bank : Small ↪ K) (countLive : Bool) (port : Small) : Engine.Port K :=
  match liveSlot countLive port with
  | some j => .frame (.inl j)
  | none => .aux (bank port)

theorem ports_injective (bank : Small ↪ K) (countLive : Bool) : Function.Injective (ports bank countLive) := by
  intro a b h
  unfold ports at h
  cases ha : liveSlot countLive a <;> cases hb : liveSlot countLive b <;> rw [ha,hb] at h
  · exact bank.injective (Engine.Port.aux.inj h)
  · contradiction
  · contradiction
  · obtain ⟨i,rfl,hi,_⟩ := liveSlot_info ha
    obtain ⟨j,rfl,hj,_⟩ := liveSlot_info hb
    have eq := Sum.inl.inj (Engine.Port.frame.inj h)
    have eq' := congrArg Fin.val eq
    congr 1
    apply Fin.ext
    omega

/-- Empty public-word bank of the aliased dispatcher. -/
abbrev pub {w : ℕ} : Fin 0 → Word w := Fin.elim0

/-- Width-sized auxiliary register words, including a zero dummy counter and
the row dimension. The scratch registers may contain arbitrary words. -/
def Ready (bank : Small ↪ K) (w n : ℕ) (aux : Stacks K) : Prop :=
  ∃ (base : Regs R w) (persist : Word w),
    (base (Code.inReg capacity 6)).val = 0 ∧ (base (Code.inReg capacity 7)).val = n ∧
    ∀ i, aux (bank i) = ISA.bank pub persist base [] i

/-- Install one compiled dispatch operation with its query registers aliased to the live frame. -/
def routine (bank : Small ↪ K) (countLive : Bool) (a : Operation) : FiniteRoutine (Engine.Port K) :=
  a.machine.onPorts (ports bank countLive)

/-- The fields actually read from the caller's frame. -/
def LiveInput (w : ℕ) (countLive : Bool) (data : Engine.Data) (env : Fin 8 → ℕ) : Prop :=
  ∀ i j, liveSlot countLive (.reg i) = some j → ∀ ix : Fin 8, ix.val = i.val →
    data j = UniversalCountStack.digits w (env ix)

private def replaceInputs {w : ℕ} (rs : Regs R w) (env : Fin 8 → ℕ) (i : Reg) : Word w :=
  if hi : i.val < 8 then Fin.ofNat _ (env ⟨i.val,hi⟩) else rs i

private def keepInputs {w : ℕ} (base out : Regs R w) (i : Reg) : Word w :=
  if i.val < 8 then base i else out i

private theorem replace_at {w : ℕ} (rs : Regs R w) (env : Fin 8 → ℕ) (i : Fin 8) :
    replaceInputs rs env (Code.inReg capacity i) = Fin.ofNat _ (env i) := by
  simp only [replaceInputs, Code.inReg]
  exact dite_eq_left i.isLt

private theorem keep_at {w : ℕ} (base out : Regs R w) (i : Fin 8) :
    keepInputs base out (Code.inReg capacity i) = base (Code.inReg capacity i) := by
  simp only [keepInputs, Code.inReg]
  exact ite_eq_left i.isLt

/-- Execute the dispatcher directly on the engine's frame. Replacing the
auxiliary scratch state never changes the live query, history, or result. -/
theorem run [DecidableEq K] {w p n : ℕ} (bank : Small ↪ K) (flag : Bool) (a : Operation)
    (env : Fin 8 → ℕ) (live saved : Engine.Data) (signal result : List Bool) (aux : Stacks K)
    (hready : Ready bank w n aux) (hlive : LiveInput w flag live env)
    (h6 : flag = false → env 6 = 0) (h7 : env 7 = n)
    (he : ∀ i, env i < 2^p) (hp : p ≤ w) (hw : (p+1)*widthFactor ≤ w) :
    ∃ t ≤ a.clock w, ∃ out, Ready bank w n out ∧
      (routine bank flag a).Runs t (store live saved signal result aux) (store live saved signal result out) ∧
      (∀ i, out (bank (.reg (Code.outReg capacity i))) = UniversalCountStack.digits w (a.tree.eval env i)) ∧
      ∀ j, (∀ i, bank i ≠ j) → out j = aux j := by
  obtain ⟨base,persist,hzero,hrows,hbase⟩ := hready
  let rs := replaceInputs base env
  have hr (i : Fin 8) : (rs (Code.inReg capacity i)).val = env i := by
    rw [show rs (Code.inReg capacity i) = _ from replace_at base env i]
    exact Nat.mod_eq_of_lt ((he i).trans_le (Nat.pow_le_pow_right (by decide) hp))
  have hsame (i : Reg) (hn : liveSlot flag (.reg i) = none) : rs i = base i := by
    by_cases hi : i.val < 8
    · let ix : Fin 8 := ⟨i.val,hi⟩
      have hei : i = Code.inReg capacity ix := Fin.ext rfl
      have hn' : ¬(i.val < 6 ∨ flag = true ∧ i.val = 6) := by
        intro hv
        simp [liveSlot, hv] at hn
      have hcases : ix = 6 ∨ ix = 7 := by
        by_cases hh : i.val = 6
        · exact .inl (Fin.ext hh)
        · exact .inr (Fin.ext (by dsimp [ix]; omega))
      rcases hcases with hh | hh
      · have hi6 : i.val = 6 := congrArg Fin.val hh
        have hf : flag = false := by
          cases flag with
          | false => rfl
          | true => exact (hn' (.inr ⟨rfl,hi6⟩)).elim
        rw [hei,hh]
        exact Fin.ext ((hr 6).trans ((h6 hf).trans hzero.symm))
      · rw [hei,hh]
        exact Fin.ext ((hr 7).trans (h7.trans hrows.symm))
    · exact dite_eq_right hi
  obtain ⟨t,ht,out,hrun,hkeep,hval⟩ := a.run env rs hw he hr pub persist
  let cleaned := keepInputs base out
  let final := installStacks bank aux (ISA.bank pub persist cleaned [])
  have hfinal (i : Small) : final (bank i) = ISA.bank pub persist cleaned [] i := installStacks_at bank.injective ..
  have hin (i : Small) : store live saved signal result aux (ports bank flag i) = ISA.bank pub persist rs [] i := by
    cases h : liveSlot flag i with
    | none =>
      simp only [ports,h,store,hbase]
      cases i with
      | reg j => exact congrArg wordBits (hsame j h).symm
      | pub | persistent | work | logPort => rfl
    | some j =>
      obtain ⟨i,rfl,hj,hsmall⟩ := liveSlot_info h
      let ix : Fin 8 := ⟨i.val,by omega⟩
      rw [ports,h]
      change live j = wordBits (rs i)
      rw [hlive i j h ix rfl, show i = Code.inReg capacity ix from Fin.ext rfl]
      exact congrArg wordBits (replace_at base env ix).symm
  have hout (i : Small) : store live saved signal result final (ports bank flag i) = ISA.bank pub persist out [] i := by
    cases h : liveSlot flag i with
    | none =>
      simp only [ports,h,store,hfinal]
      cases i with
      | reg j =>
        apply congrArg wordBits
        by_cases hi : j.val < 8
        · let ix : Fin 8 := ⟨j.val,hi⟩
          have hj : j = Code.inReg capacity ix := Fin.ext rfl
          rw [show cleaned j = base j from ite_eq_left hi, ← hsame j h, hj, hkeep ix]
        · exact ite_eq_right hi
      | pub | persistent | work | logPort => rfl
    | some j =>
      obtain ⟨i,rfl,hj,hsmall⟩ := liveSlot_info h
      let ix : Fin 8 := ⟨i.val,by omega⟩
      have eq : i = Code.inReg capacity ix := Fin.ext rfl
      have hv := hin (.reg i)
      simp only [ports,h,store,ISA.bank] at hv ⊢
      rw [eq, hkeep ix, ← eq, ← hv]
  refine ⟨t,ht,final,⟨cleaned,persist,?_,?_,hfinal⟩,?_,?_,?_,⟩
  · rw [show cleaned (Code.inReg capacity 6) = _ from keep_at base out 6, hzero]
  · rw [show cleaned (Code.inReg capacity 7) = _ from keep_at base out 7, hrows]
  · apply FiniteRoutine.runs_onPorts_framed _ (ports_injective bank flag) hrun hin hout
    intro l hl
    cases l with
    | frame f => cases f <;> rfl
    | condition | result => rfl
    | aux k =>
      change final k = aux k
      by_cases h : ∃ i, bank i = k
      · obtain ⟨i,rfl⟩ := h
        cases ha : liveSlot flag i with
        | none => exact (hl i (by simp [ports, ha])).elim
        | some j =>
          obtain ⟨i,rfl,hj,hsmall⟩ := liveSlot_info ha
          rw [hfinal,hbase]
          apply congrArg wordBits
          exact ite_eq_left (by omega)
      · exact installStacks_outside _ _ (not_exists.mp h)
  · intro i
    rw [hfinal]
    change wordBits (cleaned (Code.outReg capacity i)) = wordBits _
    apply congrArg wordBits
    have ho : ¬(Code.outReg capacity i).val < 8 := by simp [Code.outReg]
    rw [show cleaned (Code.outReg capacity i) = _ from ite_eq_right ho]
    apply Fin.ext
    rw [Fin.val_ofNat, ← hval, Nat.mod_eq_of_lt (out _).isLt]
  · exact fun _ hj => installStacks_outside _ _ hj

end RankQuery.Stack.EngineAlias

end VPVNP
end Computability
end OAI
