import OAI.ThreeFlat.Diagonal.TickChronology
import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Branching to the seven native tick continuations -/

namespace ThreeFlat.RAM.TickDispatch

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology
open scoped Fin.NatCast

variable {w p r k : ℕ}

private def which : Fin 6 → Phase
  | 0 => .idle | 1 => .opening | 2 => .closing | 3 => .propose | 4 => .scan | 5 => .evaluate

private theorem tag_which (j : Fin 6) : (which j).tag = j.val := by fin_cases j <;> rfl

private theorem tag_inj : Function.Injective Phase.tag := by
  intro x y h
  cases x <;> cases y <;> simp_all [Phase.tag]

private theorem tag_le (ph : Phase) : ph.tag ≤ 6 := by cases ph <;> decide

private def after (loc : Fin 6 × Bool → Fin p) (out : Phase → Fin p) (j : Fin 6) :=
  if h : j.val+1 < 6 then loc (⟨j.val+1,h⟩,false) else out .clear

/-- A literal and an equality branch test each tag from zero through five.
Tag six falls through to the clearing continuation. -/
def code (loc : Fin 6 × Bool → Fin p) (out : Phase → Fin p) (tag tmp : Fin r) :
    Fin 6 × Bool → Instr w p r k
  | (j,false) => .constant tmp (j.val : Word w) (loc (j,true))
  | (j,true) => .jumpEq tag tmp (out (which j)) (after loc out j)

private def target (loc : Fin 6 × Bool → Fin p) (out : Phase → Fin p) (ph : Phase) (j : Fin 6) :=
  if ph.tag = j.val then out (which j) else after loc out j

private theorem pair (M : Machine w p r k) (loc : Fin 6 × Bool → Fin p) (out : Phase → Fin p)
    (tag tmp : Fin r) (ne : tag ≠ tmp) (rom : ∀ j, M.code (loc j) = code loc out tag tmp j)
    (wide : 6 < 2^w) (ph : Phase) (j : Fin 6) (c : Config w p r) (m : Memory w)
    (start : c.pc = loc (j,false)) (h : c.reg tag = (ph.tag : Word w)) :
    advance M.program 2 c m = some (c.put (target loc out ph j) tmp (j.val : Word w),m) := by
  have eq : ((ph.tag : Word w) = (j.val : Word w)) ↔ ph.tag = j.val := by
    rw [Fin.ext_iff, Fin.val_cast_of_lt ((tag_le ph).trans_lt wide),
      Fin.val_cast_of_lt (j.isLt.trans wide)]
  simp [advance,Machine.program,start,rom,code,Instr.run,Config.put,
    Function.update_of_ne ne,h,eq,target]

private theorem suffix (M : Machine w p r k) (loc : Fin 6 × Bool → Fin p) (out : Phase → Fin p)
    (tag tmp : Fin r) (ne : tag ≠ tmp) (rom : ∀ j, M.code (loc j) = code loc out tag tmp j)
    (wide : 6 < 2^w) (ph : Phase) (m : Memory w) (rem : ℕ) (j : Fin 6) (c : Config w p r)
    (room : j.val+rem = 6) (later : j.val ≤ ph.tag) (start : c.pc = loc (j,false))
    (h : c.reg tag = (ph.tag : Word w)) :
    ∃ n ≤ 2*rem, ∃ d, advance M.program n c m = some (d,m) ∧ d.pc = out ph ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
      ∀ i, i ≠ tmp → d.reg i = c.reg i := by
  induction rem generalizing c j with
  | zero => have := j.isLt; omega
  | succ rem ih =>
    let t := target loc out ph j
    let c' := c.put t tmp (j.val : Word w)
    have step : advance M.program 2 c m = some (c',m) := pair M loc out tag tmp ne rom wide ph j c m start h
    have done (ht : t = out ph) : ∃ n ≤ 2*(rem+1), ∃ d,
        advance M.program n c m = some (d,m) ∧ d.pc = out ph ∧ d.persistent = c.persistent ∧
        d.privateMem = c.privateMem ∧ ∀ i, i ≠ tmp → d.reg i = c.reg i :=
      ⟨2, by omega, c', step, ht, rfl, rfl, fun i hi => Function.update_of_ne hi ..⟩
    by_cases hit : ph.tag = j.val
    · apply done
      have same : which j = ph := tag_inj ((tag_which j).trans hit.symm)
      simp [t,target,hit,same]
    · by_cases more : j.val+1 < 6
      · let next : Fin 6 := ⟨j.val+1,more⟩
        have hnext : c'.pc = loc (next,false) := by simp [c',t,target,hit,after,more,next,Config.put]
        obtain ⟨n,hn,d,run,pc,hp,hm,regs⟩ := ih next c' (by dsimp [next]; omega)
          (by dsimp [next]; omega) hnext ((Function.update_of_ne ne ..).trans h)
        exact ⟨2+n,by omega,d, advance_trans step run,pc,hp,hm,
          fun i hi => (regs i hi).trans (Function.update_of_ne hi ..)⟩
      · have final : ph = .clear := by
          apply tag_inj
          have := tag_le ph
          change ph.tag = 6
          have := j.isLt
          omega
        apply done
        change (if ph.tag = j.val then _ else after loc out j) = out ph
        rw [ite_eq_right hit]
        simp only [after,dite_eq_right more,final]

/-- At most twelve deterministic instructions suffice. Only the scratch
register changes, and the external memory is returned unchanged. -/
theorem advance_dispatch (M : Machine w p r k) (loc : Fin 6 × Bool → Fin p)
    (out : Phase → Fin p) (tag tmp : Fin r) (ne : tag ≠ tmp)
    (rom : ∀ i, M.code (loc i) = code loc out tag tmp i)
    (wide : 6 < 2^w) (ph : Phase) (c : Config w p r) (m : Memory w)
    (start : c.pc = loc (0,false)) (h : c.reg tag = (ph.tag : Word w)) :
    ∃ n ≤ 12, ∃ d, advance M.program n c m = some (d,m) ∧ d.pc = out ph ∧
      d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
      ∀ i, i ≠ tmp → d.reg i = c.reg i :=
  suffix M loc out tag tmp ne rom wide ph m 6 0 c rfl (Nat.zero_le _) start h

end ThreeFlat.RAM.TickDispatch

end OAI
