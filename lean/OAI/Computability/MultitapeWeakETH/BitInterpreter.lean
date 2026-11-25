import OAI.Computability.MultitapeWeakETH.StackInterpreter
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-! # Calling bounded disjoint-sparsification routines on tree-encoded stacks -/

namespace OAI.Computability.MultitapeWeakETH.BitInterpreter

open IntegerMultiplication.Code StackInterpreter Algorithms.SubexponentialSAT BitProgram
open private top_easy size_modify ordinal pop_easy popBits from OAI.Computability.MultitapeWeakETH.StackInterpreter
open scoped Classical
noncomputable section

variable {r s l : ℕ}

abbrev Control (r l : ℕ) := Option (Fin l) × (Fin r → Bool)
abbrev Image (r l : ℕ) := Snapshot (Control r l)

def image (c : Cfg r s l) : Image r l := (⟨c.pc,c.regs⟩,pack c.stacks)

/-- The finite register logic looks only at the indicated stack top. -/
private def next (i : Instr r s l) (bits : Fin r → Bool) (top : Option Bool) : Label (Control r l) :=
  let c := execInstr i ⟨none,bits,fun _ => top.toList⟩
  ⟨c.pc,c.regs⟩

private def dispatch (i : Instr r s l) (bits : Fin r → Bool) (b : Bank) : Image r l :=
  match i with
  | .push k src _ => (next i bits none,modify k (bits src :: ·) b)
  | .peek k .. => (next i bits (get k b).head?,b)
  | .pop k .. => (next i bits (get k b).head?,modify k popBits b)
  | _ => (next i bits none,b)

private theorem dispatch_poly (i : Instr r s l) (bits : Fin r → Bool) : Poly (dispatch i bits) := by
  have top (j : Instr r s l) (k : Fin s) := ((get_easy k).compose top_easy).compose (Easy.finite (next j bits))
  cases i with
  | push k src t => exact ((Easy.const _).pair (modify_easy k _ (((Easy.const _).pair Easy.identity).compose Easy.cons))).poly
  | peek k v p t => exact ((top _ k).pair Easy.identity).poly
  | pop k v p t => exact ((top _ k).pair (modify_easy k _ pop_easy)).poly
  | _ => exact ((Easy.const _).pair Easy.identity).poly

private def act (P : Program r s l) (x : Image r l) : Image r l :=
  x.1.val.1.elim x (fun j => dispatch (P.code j) x.1.val.2 x.2)

private theorem act_poly (P : Program r s l) : Poly (act P) := by
  apply select_poly Prod.fst Easy.fst.poly
    (fun (q : Control r l) x => q.1.elim x (fun j => dispatch (P.code j) q.2 x.2)) _ id Poly.identity
  rintro ⟨pc,bits⟩
  cases pc with
  | none => exact Poly.identity
  | some j => exact Easy.snd.poly.compose (dispatch_poly _ _)

private theorem dispatch_bank (i : Instr r s l) (bits : Fin r → Bool) (b : Bank) :
    size (dispatch i bits b).2 ≤ size b+2 := by
  cases i with
  | push k src t => exact size_modify _ (fun x => by simp; omega) b (ordinal _ k).val
  | pop k v p t =>
    apply size_modify
    intro x
    cases x <;> simp [popBits]
    omega
  | _ => simp [dispatch]

private theorem act_size (P : Program r s l) (x : Image r l) :
    size (act P x) ≤ size x+(2*Fintype.card (Control r l)+3) := by
  cases h : x.1.val.1 with
  | none => simp [act,h]
  | some j =>
    simp only [act,h,Option.elim_some,size_prod]
    have bank := dispatch_bank (P.code j) x.1.val.2 x.2
    have label := label_size (dispatch (P.code j) x.1.val.2 x.2).1.val
    change size (dispatch (P.code j) x.1.val.2 x.2).1 ≤ _ at label
    omega

private theorem dispatch_eq (i : Instr r s l) (c : Cfg r s l) :
    dispatch i c.regs (pack c.stacks) = image (execInstr i c) := by
  cases i <;> simp [dispatch,image,next,execInstr,get_pack,modify_pack,popBits]

private theorem act_eq (P : Program r s l) (c e : Cfg r s l) (h : step P c = some e) :
    act P (image c) = image e := by
  cases hc : c.pc with
  | none => simp [BitProgram.step,hc] at h
  | some j =>
    simp only [BitProgram.step,hc,Option.map_some,Option.some.injEq] at h
    subst e
    simpa only [act,image,hc,Option.elim_some] using dispatch_eq (P.code j) c

def run (P : Program r s l) := ride (act P)

theorem run_poly (P : Program r s l) : Poly (run P) :=
  Poly.rider _ (act_poly P) _ (act_size P)

theorem run_eq (P : Program r s l) {t : ℕ} {a b : Cfg r s l} (trace : BitProgram.Trace P t a b)
    (halt : b.pc = none) (fuel : ℕ) (enough : t ≤ fuel) :
    run P (tally fuel,image a) = image b := by
  simp only [run,ride_t,tally_length]
  induction trace generalizing fuel with
  | refl =>
    apply Function.iterate_fixed
    simp [act,image,halt]
  | cons h _ ih =>
    cases fuel with
    | zero => omega
    | succ k => rw [Function.iterate_succ_apply,act_eq P _ _ h]; exact ih halt _ (by omega)

abbrev StateImage (r : ℕ) := Label (Fin r → Bool) × Bank

def stateImage (a : StructuredProgram.State r s) : StateImage r := (⟨a.regs⟩,pack a.stacks)

/-- Compilation is done once for the fixed subroutine. Its caller can reuse a
polynomial clock which bounds every legal invocation. -/
def call (c : StructuredCalls.Cmd r s) (port : Fin s) (q : Tally × StateImage r) : StateImage r :=
  let P := StructuredCalls.compiled c port port
  let result := run P (q.1,(⟨some P.entry,q.2.1.val⟩,q.2.2))
  (⟨result.1.val.2⟩,result.2)

theorem call_poly (c : StructuredCalls.Cmd r s) (port : Fin s) : Poly (call c port) := by
  let P := StructuredCalls.compiled c port port
  have enter := Easy.finite (fun x : Label (Fin r → Bool) => Label.mk (some P.entry,x.val))
  have leave := Easy.finite (fun x : Label (Control r (StructuredCalls.size c+1)) => Label.mk x.val.2)
  exact ((Easy.fst.pair (((Easy.snd.compose Easy.fst).compose enter).pair (Easy.snd.compose Easy.snd))).poly.compose
    (run_poly P)).compose (((Easy.fst.compose leave).pair Easy.snd).poly)

theorem call_eq (c : StructuredCalls.Cmd r s) (port : Fin s) {t : ℕ} {a b : StructuredProgram.State r s}
    (eval : StructuredCalls.Eval c t a b) (fuel : ℕ) (enough : t+1 ≤ fuel) :
    call c port (tally fuel,stateImage a) = stateImage b := by
  have result := run_eq _ (StructuredCalls.compiled_halt_trace eval port port) rfl fuel enough
  exact congrArg (fun x => (Label.mk x.1.val.2,x.2)) result

end
end OAI.Computability.MultitapeWeakETH.BitInterpreter
