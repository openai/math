import OAI.Computability.BorderVNP.DiagonalResidueRAMLoad

/-!
# Native indirect gather of the public residue query

The advised source list contains one physical address per public query bit.
The source address is fetched before the bit at that address is read. Only
the constant bits and the consecutive query destination words are changed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA

/-- Initialize the valuation bank with its two constants and calculate the address
of the gather list immediately following the gate records. -/
def gatherSetup : Code := .block [
  .constant 38 1, .constant 39 0, .copy 40 35, .store 40 39,
  .binary .add 40 40 38, .store 40 38, .binary .add 40 40 38,
  .constant 42 3, .binary .mul 42 32 42, .binary .add 42 34 42, .copy 41 39]

/-- Gather a bit from the indicated actual shared address. -/
def gatherBody : Code := .block [
  .load 43 42, .load 44 43, .store 40 44,
  .binary .add 40 40 38, .binary .add 42 42 38, .binary .add 41 41 38]

/-- Materialize the full query using the number of bits in the installed frame. -/
def gather : Code := .seq gatherSetup (.whileLt 41 37 gatherBody)

variable {w : ℕ}

/-- Natural multiplication agrees with the machine's modular multiplication. -/
theorem word_mul (w i j : ℕ) : word w (i*j) = word w i * word w j := Fin.ext (Nat.mul_mod ..)

/-- The two constant writes at the start of the valuation bank. -/
def setConstants (m : Memory w) (base : ℕ) : Memory w :=
  Function.update (Function.update m base 0) (base+1) 1

/-- The input lists are an address stream and a canonical bit at each referenced
physical source. -/
def sourcesAt (m : Memory w) (ip : ℕ) : List (ℕ × Bool) → Prop
  | [] => True
  | (addr,b)::xs => m ip = word w addr ∧ addr < 2^w ∧ m addr = wordBit w b ∧ sourcesAt m (ip+1) xs

/-- A write outside the source and gather-list intervals preserves the input table. -/
theorem sourcesAt_update (m : Memory w) (ip : ℕ) (xs : List (ℕ × Bool)) (a : ℕ) (b : Word w)
    (h : sourcesAt m ip xs) (he : a < ip) (hs : ∀ t ∈ xs, t.1 ≠ a) :
    sourcesAt (Function.update m a b) ip xs := by
  induction xs generalizing ip with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨addr,bit⟩ := x
    obtain ⟨hh,hf,hb,ht⟩ := h
    have other := hs (addr,bit) (by simp)
    exact ⟨(Function.update_of_ne (by omega : ip ≠ a) ..).trans hh,hf,
      (Function.update_of_ne other ..).trans hb,ih _ ht (by omega) (fun t h => hs _ (by simp [h]))⟩

/-- Word effects of the gather initializer, including the actual two stores. -/
theorem gather_setup_effect (d : Frame) (s : Bank w) (m : Memory w) (hs : d.loaded s)
    (hb : d.base+1 < 2^w) :
    let e := effect false s m gatherSetup
    d.stable e.bank ∧ e.bank 40 = word w (d.base+2) ∧ e.bank 41 = 0 ∧
      e.bank 42 = word w (d.advice+3*d.gates) ∧ e.mem = setConstants m d.base ∧
      TraceOK e.trace [] 11 := by
  rcases hs with ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩
  have add1 (a : ℕ) : word w a + 1 = word w (a+1) := (word_add w a 1).symm
  have mul3 (a : ℕ) : word w a * Fin.ofNat (2^w) 3 = word w (3*a) := by
    rw [Nat.mul_comm,word_mul]; rfl
  simp only [gatherSetup,Code.block,effect]
  simp [Frame.stable,Frame.loaded,Function.update, BinaryOp.eval, TraceOK,tick,setConstants,
    h₀,h₁,h₂,h₃,h₄,h₅,-word_add,word_val _ _ (show d.base<2^w by omega)]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change word w d.base + 1 + 1 = word w (d.base+2)
    rw [add1,add1]
  · rw [word_add,← mul3]
    rfl
  · change Function.update (Function.update m d.base 0) (word w d.base + 1).val 1 =
      Function.update (Function.update m d.base 0) (d.base+1) 1
    rw [add1,word_val _ _ hb]

/-- A complete indirect fetch, write and cursor advance takes six ticks and
leaves the six header operands and the two fixed constants unchanged. -/
theorem gather_body_effect (d : Frame) (s : Bank w) (m : Memory w) (hs : d.stable s)
    (start ip i a : ℕ) (b : Bool) (hstart : s 40 = word w start) (hi : s 41 = word w i)
    (hip : s 42 = word w ip) (hword : m ip = word w a) (hbit : m a = wordBit w b)
    (hsfit : start < 2^w) (hifit : ip < 2^w) (hafit : a < 2^w) :
    let e := effect false s m gatherBody
    d.stable e.bank ∧ e.bank 40 = word w (start+1) ∧ e.bank 41 = word w (i+1) ∧
      e.bank 42 = word w (ip+1) ∧ e.mem = Function.update m start (wordBit w b) ∧ TraceOK e.trace [] 6 := by
  rcases hs with ⟨⟨h₀,h₁,h₂,h₃,h₄,h₅⟩,h₆,h₇⟩
  simp [gatherBody,Code.block,effect,Frame.stable,Frame.loaded,Function.update,BinaryOp.eval,TraceOK,tick,
    h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,hstart,hi,hip,word_val _ _ hsfit,word_val _ _ hifit,word_val _ _ hafit,
    hword,hbit]

/-- Scan all query bits on true memory, maintaining the source addresses and
their values while earlier output words are written. -/
theorem gather_loop (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (d : Frame)
    (s : Bank w) (m : Memory w) (start ip i : ℕ) (xs : List (ℕ × Bool))
    (hs : d.stable s) (hstart : s 40 = word w start) (hi : s 41 = word w i) (hip : s 42 = word w ip)
    (hn : i+xs.length = d.query) (hq : d.query < 2^w) (hsrc : sourcesAt m ip xs)
    (hsep : start + xs.length ≤ ip) (hipFit : ip + xs.length < 2^w)
    (hdis : ∀ t ∈ xs, t.1 < start ∨ start+xs.length ≤ t.1) :
    ∃ t, Exact pub mac (.whileLt 41 37 gatherBody) s m [] (7*xs.length+1) t
      (putBits m start (xs.map Prod.snd)) ∧ d.stable t := by
  induction xs generalizing s m start ip i with
  | nil =>
    have he : i=d.query := by simpa using hn
    exact ⟨s,⟨[tick w],.whileDone (by simp [hi,hs.1.2.2.2.2.2,he]),by simp [TraceOK,tick]⟩,hs⟩
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    have hit : i<d.query := by simp at hn; omega
    have guard : s 41 < s 37 := by
      change (s 41).val < (s 37).val
      rw [hi,hs.1.2.2.2.2.2,word_val _ _ (hit.trans hq),word_val _ _ hq]; exact hit
    obtain ⟨ha,haf,hb,ht⟩ := hsrc
    let e := effect false s m gatherBody
    obtain ⟨hst,hst',hi',hip',hm',he⟩ := gather_body_effect d s m hs start ip i a b hstart hi hip
      ha hb (by simp at hsep hipFit; omega) (by simp at hipFit; omega) haf
    have hnext : sourcesAt e.mem (ip+1) xs := by
      rw [show e.mem = _ from hm']
      apply sourcesAt_update _ _ _ _ _ ht (by simp at hsep; omega)
      intro t ht
      have hd := hdis t (by simp [ht])
      simp only [List.length_cons] at hd; omega
    obtain ⟨t,⟨es,hr,tr⟩,hz⟩ := ih e.bank e.mem (start+1) (ip+1) (i+1) hst hst' hi' hip'
      (by simp at hn; omega) hnext (by simp at hsep; omega) (by simp at hipFit; omega)
      (fun t ht => by have hh := hdis t (by simp [ht]); simp only [List.length_cons] at hh; omega)
    have step := Runs.whileStep guard (effect_runs pub mac false s m gatherBody (by decide)) hr
    have tr' := (he.append tr).cons_tick
    refine ⟨t,⟨tick w :: (e.trace++es),?_,?_⟩,hz⟩
    · simpa only [List.map_cons,putBits,← hm'] using step
    · rw [show 7*((a,b)::xs).length+1 = 6+(7*xs.length+1)+1 by simp; omega]
      exact tr'

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
