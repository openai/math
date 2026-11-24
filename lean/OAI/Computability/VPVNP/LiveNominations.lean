import OAI.Computability.VPVNP.RAMChoicePrefix
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.PrimedInputRAMFlowComplete
import OAI.Computability.VPVNP.PrimedCounterGuessWord
import OAI.Computability.VPVNP.RAMRecords

/-!
# Native binary nominations in a first-half live group

Section 14.1 guesses exactly `2r` little-endian bits per production label.
This fixed RAM call takes the bit count and destination base as public words.
Its persistent state indexes the component. It writes one word and returns
the next component index. The same control works for any nomination width
that fits a RAM word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveNominations

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

private def setup : Flow 8 2 :=
  .seq (.line (.constant 0 0)) <| .seq (.line (.constant 1 1)) <| .seq (.line (.constant 2 0)) <|
  .seq (.line (.publicWord 3 0)) (.line (.constant 4 1))

private def bitBody : Flow 8 2 :=
  .seq (.branch (.line (.binary .add 0 0 1)) (.line (.copy 0 0))) <|
  .seq (.line (.binary .add 1 1 1)) (.line (.binary .add 2 2 4))

private def loop : Flow 8 2 := .whileLt 2 3 bitBody

private def finish : Flow 8 2 :=
  .seq (.line (.stateWord 5)) <| .seq (.line (.publicWord 6 1)) <|
  .seq (.line (.binary .add 6 6 5)) <| .seq (.line (.write 6 0)) (.line (.binary .add 7 5 4))

/-- Registers 0, 1 and 2 accumulate the value, bit weight and iteration count. -/
def flow : Flow 8 2 := .seq setup (.seq loop finish)

variable {w b : ℕ}

/-- The nomination worker's public bit count and base address for the per-label output words. -/
def data (b : ℕ) (base : Word w) : Fin 2 → Word w := ![Fin.ofNat _ b, base]

/-- The instantiated burst program that guesses a label's bits, stores the nominated word, and
returns the next label cursor. -/
def program (b : ℕ) (base : Word w) :=
  ((flow.template (some 7)).instantiate w (data b base)).program

private def regsAfterSetup (pub : Fin 2 → Word w) (s : Regs w 8) :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update s (0 : Fin 8) 0) 1 1) 2 0) 3 (pub 0)) 4 1

private def advance (s : Regs w 8) (v : Bool) :=
  Function.update (Function.update (Function.update s (0 : Fin 8)
    (if v then s 0 + s 1 else s 0)) 1 (s 1 + s 1)) 2 (s 2 + s 4)

private def regsAfterFinish (s : Regs w 8) (st base : Word w) :=
  Function.update (Function.update (Function.update s (5 : Fin 8) st) 6 (base+st)) 7 (st+s 4)

private def bitEvents (v : Bool) : List (Event w) := [.choice v, .tick, .tick, .tick]

private def loopEvents : List Bool → List (Event w)
  | [] => [.tick]
  | v :: vs => .tick :: (bitEvents v ++ loopEvents vs)

private theorem setup_exec (pub : Fin 2 → Word w) (st : Word w) (s : Regs w 8) (m : Memory w) :
    Flow.Exec pub st setup s m (List.replicate 5 .tick) (regsAfterSetup pub s) m :=
  (Flow.once_sound pub st false setup s m rfl).1

private theorem body_exec (pub : Fin 2 → Word w) (st : Word w) (s : Regs w 8) (m : Memory w)
    (v : Bool) : Flow.Exec pub st bitBody s m (bitEvents v) (advance s v) m := by
  apply (Flow.once_sound pub st v bitBody s m ?_).1
  cases v <;> rfl

private theorem finish_exec (pub : Fin 2 → Word w) (st : Word w) (s : Regs w 8) (m : Memory w) :
    Flow.Exec pub st finish s m [.tick,.tick,.tick,.write (pub 1 + st) (s 0),.tick]
      (regsAfterFinish s st (pub 1)) (writeMemory m (pub 1 + st) (s 0)) := by
  apply (Flow.once_sound pub st false finish s m ?_).1
  simp (config := { decide := true }) [finish, Flow.once, Op.effect, Function.update,
    regsAfterFinish, show BinaryOp.add.eval = (· + · : Word w → Word w → Word w) from rfl]

private theorem loop_exec (pub : Fin 2 → Word w) (st : Word w) (m : Memory w) (vs : List Bool)
    (s : Regs w 8) (hone : s 4 = 1) (hlen : (s 2).val + vs.length = (s 3).val) :
    ∃ out, Flow.Exec pub st loop s m (loopEvents vs) out m ∧
      out 0 = s 0 + s 1 * (PrimedCounter.GuessWord.value vs : Word w) ∧ out 4 = 1 := by
  induction vs generalizing s with
  | nil =>
    refine ⟨s, Flow.Exec.whileDone ?_, ?_, hone⟩
    · change ¬ (s 2).val < (s 3).val
      simp only [List.length_nil, Nat.add_zero] at hlen
      omega
    · simp [PrimedCounter.GuessWord.value]
  | cons v vs ih =>
    let s' := advance s v
    have h₂ : (s' 2).val = (s 2).val+1 := by
      change (s 2 + s 4).val = _
      rw [hone]
      apply Fin.val_add_one_of_lt'
      have := (s 3).isLt
      simp only [List.length_cons] at hlen
      omega
    have h₃ : s' 3 = s 3 := rfl
    have h₄ : s' 4 = 1 := hone
    obtain ⟨u, hu, hv, hlast⟩ := ih s' h₄ (by rw [h₂, h₃]; simpa [Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hlen)
    have ht : s 2 < s 3 := by change (s 2).val < (s 3).val; simp only [List.length_cons] at hlen; omega
    refine ⟨u, Flow.Exec.whileStep ht (body_exec pub st s m v) hu, ?_, hlast⟩
    rw [hv]
    cases v <;> simp [s', advance, PrimedCounter.GuessWord.value, Function.update] <;> ring

private def resultEvents (base st v : Word w) (bits : List Bool) : List (Event w) :=
  List.replicate 5 .tick ++ (loopEvents bits ++ [.tick,.tick,.tick,.write (base+st) v,.tick])

private theorem loop_cost (vs : List Bool) :
    (loopEvents (w := w) vs).length = 5 * vs.length + 1 ∧
    choiceBits (loopEvents (w := w) vs) = vs ∧ countProbes (loopEvents (w := w) vs) = 0 := by
  induction vs with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons v vs ih =>
    simp only [loopEvents, bitEvents, List.cons_append, List.nil_append, List.length_cons,
      choiceBits, countProbes, ih.1, ih.2.1, ih.2.2, Nat.mul_succ]
    exact ⟨trivial, trivial, trivial⟩

private theorem loop_after (vs : List Bool) (m : Memory w) : after m (loopEvents vs) = m := by
  induction vs with
  | nil => rfl
  | cons v vs ih => exact ih

private theorem probe_append (xs ys : List (Event w)) :
    countProbes (xs ++ ys) = countProbes xs + countProbes ys := by
  induction xs with
  | nil => simp [countProbes]
  | cons e xs ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

private theorem result_cost (base st v : Word w) (bs : List Bool) :
    (resultEvents base st v bs).length = 5 * bs.length + 11 ∧
    countProbes (resultEvents base st v bs) = 1 ∧ choiceBits (resultEvents base st v bs) = bs := by
  obtain ⟨hl,hb,hp⟩ := loop_cost (w := w) bs
  simp only [resultEvents, List.length_append, List.length_replicate, hl, List.length_cons,
    List.length_nil, probe_append, Flow.choiceBits_append, hp, hb]
  exact ⟨by omega, rfl, by simp [choiceBits, List.replicate_succ]⟩

private theorem result_after (base st v : Word w) (bs : List Bool) (m : Memory w) :
    after m (resultEvents base st v bs) = writeMemory m (base+st) v := by
  change after m (loopEvents bs ++ [.tick,.tick,.tick,.write (base+st) v,.tick]) = _
  rw [after, List.foldl_append, show (loopEvents bs).foldl update m = m from loop_after bs m]
  rfl

/-- The native microcall has exactly one write. Its binary choices are precisely
the bits of the nominated component, even when it has leading zeros. -/
theorem component_native (hb : b ≤ w) (base state : Word w) (m : Memory w) (v : Word b) :
    ∃ es, execute (program b base) (5*b+12) ((program b base).start state) m (wordBits v) =
        some ⟨es, some (state+1)⟩ ∧
      after m es = writeMemory m (base+state) (Fin.ofNat (2^w) v.val) ∧
      es.length = 5*b+11 ∧ countProbes es = 1 ∧ choiceBits es = wordBits v := by
  let pub := data b base
  let rs := regsAfterSetup pub (fun _ => 0)
  have hfit : b < 2^w := hb.trans_lt (Nat.lt_pow_self (by decide))
  have hlen : (rs 2).val + (wordBits v).length = (rs 3).val := by
    change 0 + (wordBits v).length = b % 2^w
    rw [Nat.mod_eq_of_lt hfit, length_wordBits, Nat.zero_add]
  obtain ⟨out, hloop, hval, hone⟩ := loop_exec pub state m (wordBits v) rs rfl hlen
  have hv : out 0 = Fin.ofNat (2^w) v.val := by
    rw [hval, PrimedCounter.GuessWord.value_wordBits]
    change 0 + 1 * (v.val : Word w) = _
    simp
  let es := resultEvents base state (Fin.ofNat _ v.val) (wordBits v)
  obtain ⟨hl, hp, hc⟩ := result_cost base state (Fin.ofNat _ v.val) (wordBits v)
  rw [length_wordBits] at hl
  refine ⟨es, ?_, result_after .., hl, hp, hc⟩
  apply (Flow.template_execute_iff flow (some 7) pub state (fun _ => 0) (fun _ => 0) m _ _ _).2
  refine ⟨regsAfterFinish out state base, writeMemory m (base+state) (Fin.ofNat _ v.val),
    ?_, ?_, ?_, hc⟩
  · have exec := Flow.Exec.seq (setup_exec pub state (fun _ => 0) m)
      (Flow.Exec.seq hloop (finish_exec pub state out m))
    simpa only [hv, es, resultEvents, flow, show pub 1 = base from rfl] using exec
  · change some (state + 1) = some (state + out 4)
    rw [hone]
  · change es.length < 5*b+12
    change es.length = _ at hl
    omega

private theorem word_of_bits (bs : List Bool) (h : bs.length = b) : ∃ v : Word b, bs = wordBits v := by
  subst b
  refine ⟨(RAMSerialization.wordBits bs.length).symm bs.get, ?_⟩
  simp [wordBits]

/-- Every successful call consumes exactly one fixed-width component and has
its specified memory effect, for any amount of interpreter fuel. -/
theorem component_only (hb : b ≤ w) (base state : Word w) (m : Memory w) {fuel : ℕ}
    {bs : List Bool} {r : Report w}
    (hr : execute (program b base) fuel ((program b base).start state) m bs = some r) :
    ∃ v : Word b, bs = wordBits v ∧ r.result = some (state+1) ∧
      after m r.events = writeMemory m (base+state) (Fin.ofNat (2^w) v.val) ∧
      r.events.length = 5*b+11 ∧ countProbes r.events = 1 ∧ choiceBits r.events = bs := by
  have hfull (xs : List Bool) (hx : xs.length = b) : ∃ f t,
      execute (program b base) f ((program b base).start state) m xs = some t := by
    obtain ⟨v, rfl⟩ := word_of_bits xs hx
    obtain ⟨es, h, _⟩ := component_native hb base state m v
    exact ⟨_, _, h⟩
  obtain ⟨v, rfl⟩ := word_of_bits bs (execute_length_of_complete hfull hr)
  obtain ⟨es, h, hm, hl, hp, hc⟩ := component_native hb base state m v
  have he := (execute_prefix_unique hr (suffix := []) (by simpa using h)).2
  subst r
  exact ⟨v, rfl, rfl, hm, hl, hp, hc⟩

end LiveNominations

end VPVNP
end Computability
end OAI
