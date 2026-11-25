import OAI.Computability.MultitapeWeakETH.CallExecution
import OAI.Computability.MultitapeWeakETH.BoundedIteration
import OAI.Computability.VPVNP.RAMPrivateLogRun

/-! # Uniform bounds on every reachable bit representation in native replay -/

namespace OAI.Computability.MultitapeWeakETH.CallProgram

open IntegerMultiplication Code VPVNP RAMTape BurstRAM PrivateRAM StackInterpreter NativeGrid
open private length_keys length_values from OAI.Computability.VPVNP.RAMTapeAddressLogLoad
open private advance live finish fail from OAI.Computability.MultitapeWeakETH.CallProgram
noncomputable section

variable {w p r k : ℕ}

def load : Model w p r → ℕ
  | .running c bits log => c.writes.length + bits.length + log.length
  | .finished _ log => log.length
  | .failed => 0

theorem load_step (T : Template p r k) (pub : Fin k → Word w) (base : Memory w) (x : Model w p r) :
    load (modelStep T pub base x) ≤ load x+2 := by
  cases x with
  | finished | failed => simp [modelStep]
  | running c bits log =>
    let M := T.instantiate w pub
    have grow (next : LogConfig w p r) (h : (M.logProgram.step c).continuesTo next) :
        next.writes.length ≤ c.writes.length+1 := by
      have e := Instr.runLogged_writes (i:=M.code c.pc) (pub:=pub) (l:=c) h
      rw [e]
      exact Instr.nextLog_length_le ..
    change load (advance base bits log (M.logProgram.step c)) ≤ c.writes.length+bits.length+log.length+2
    cases he : M.logProgram.step c with
    | localStep z =>
      have := grow z (by rw [he]; rfl)
      simp only [advance,load]; omega
    | branch next =>
      cases bits with
      | nil => simp [advance,load]
      | cons b bs =>
        have := grow (next b) (by rw [he]; exact ⟨b,rfl⟩)
        simp only [advance,load,List.length_cons]; omega
    | read a next =>
      have := grow (next (memory base log a.val)) (by rw [he]; exact ⟨_,rfl⟩)
      simp only [advance,load]; omega
    | write a v z =>
      have := grow z (by rw [he]; rfl)
      simp only [advance,load,List.length_cons]; omega
    | finish => cases bits <;> simp [advance,load]; omega
    | reject => simp [advance,load]

theorem load_iterate (T : Template p r k) (pub : Fin k → Word w) (base : Memory w) (x : Model w p r) (j : ℕ) :
    load ((modelStep T pub base)^[j] x) ≤ load x+2*j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have := load_step T pub base ((modelStep T pub base)^[j] x)
    omega

private theorem store_size (log : Stores w) : size (writes log) = (4*w+4)*log.length+1 := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    change size ((wordBits e.1,wordBits e.2)::writes log) = _
    simp only [size_cons,size_prod,Bits.size_word,length_wordBits,ih,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

private theorem bank_size (pub : Fin k → Word w) (c : LogConfig w p r) (m : ℕ) (le : c.writes.length ≤ m) :
    size (pack (ISA.configBank pub c)) ≤ (2*((w+1)*(m+1))+2)*Fintype.card (ISA.Port r k)+1 := by
  apply size_pack
  intro i
  have prod : c.writes.length*w ≤ m*w := Nat.mul_le_mul_right _ le
  cases i with
  | reg | pub | persistent | work => simp [ISA.configBank,ISA.bank] <;> nlinarith
  | logPort i => cases i <;> simp [ISA.configBank,ISA.bank,ISA.logStacks,length_keys,length_values] <;> nlinarith

def capacity (p r k w m : ℕ) :=
  2*Fintype.card (Phase p) + (2*((w+1)*(m+1))+2)*Fintype.card (ISA.Port r k) +
    2*m + (4*w+4)*m + 2*w + 20

theorem capacity_dom {I : Type} (p r k : ℕ) {budget w m : I → ℕ} (hw : Dom budget w) (hm : Dom budget m) :
    Dom budget (fun i => capacity p r k (w i) (m i)) := by
  let c := Dom.const budget
  let portSize := ((c 2).mul ((hw.add (c 1)).mul (hm.add (c 1)))).add (c 2)
  let encodedBank := portSize.mul (c (Fintype.card (ISA.Port r k)))
  let control := (c (2*Fintype.card (Phase p))).add encodedBank
  let payload := (control.add ((c 2).mul hm)).add ((((c 4).mul hw).add (c 4)).mul hm)
  exact (payload.add ((c 2).mul hw)).add (c 20)

theorem encode_size (pub : Fin k → Word w) (x : Model w p r) (m : ℕ) (le : load x ≤ m) :
    size (encode pub x) ≤ capacity p r k w m := by
  unfold capacity
  cases x with
  | running c bits log =>
    change c.writes.length+bits.length+log.length ≤ m at le
    have a := bank_size pub c m (by omega)
    have b := Nat.mul_le_mul_left (4*w+4) (show log.length ≤ m by omega)
    have := label_size (Phase.running c.pc)
    simp only [encode,live,size_prod,Bits.size_word,store_size,List.length_nil]
    omega
  | finished n log =>
    change log.length ≤ m at le
    have a := Nat.mul_le_mul_left (4*w+4) le
    cases n <;> simp only [encode,finish,Bool.cond_true,Bool.cond_false,size_prod,store_size,size_nil,Bits.size_word,length_wordBits]
    · have := label_size (Phase.accepted (p:=p)); omega
    · have := label_size (Phase.returned (p:=p)); omega
  | failed =>
    have := label_size (Phase.failed (p:=p))
    simp only [encode,fail,size_prod,size_nil]
    omega

end
end OAI.Computability.MultitapeWeakETH.CallProgram
