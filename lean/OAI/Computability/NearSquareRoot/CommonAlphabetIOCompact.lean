import OAI.Computability.NearSquareRoot.CommonAlphabetIO
import OAI.Computability.NearSquareRoot.CommonAlphabetLoaded
import OAI.Computability.NearSquareRoot.ScheduleInterpreterCopy

/-! # Exact time and tape contents of output compaction

A complete blank code block terminates the forward pass. The return pass
counts the contiguous literal output bits, moving the encoded head back by
one block for each bit and for the terminating block.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Compact

open IntegerMultiplication TM
open NearSquareRoot.Uniform

variable {A B : Type} (c : Code A) (digit : B → Option Bool) (decode : A → Option Bool)
    (bit : Bool → B) (isBlank : B → Bool) (blank : B)

local notation "M" => rule c digit decode bit isBlank

private def address (c : Code A) (j : ℕ) : ℤ := (j : ℤ) * c.width

private theorem address_succ (k : ℕ) :
    address c (k+1) = address c k + c.width := by simp [address,add_mul]

private theorem emits (z : List Bool) (f : ℤ → B)
    (read : ∀ j : ℕ, decode (c.dec (fun d => digit (f (address c j + d.val)))) = z[j]?) :
    ∀ k ≤ z.length, Trace (advance M) (config (start c) f (fun _ => blank) 0 0)
      ((c.width+1)*k) (config (start c) f (Copy.written blank bit z k) (address c k) k) := by
  intro k hk
  induction k with
  | zero => simpa [Copy.written_zero,address] using
      (Trace.nil (step := advance M) (config (start c) f (fun _ => blank) 0 0))
  | succ k ih =>
    have hl : k < z.length := by omega
    let g := Copy.written blank bit z k
    have scan := readBlock c digit decode bit isBlank f g (address c k) k
      (fun d => digit (f (address c k + d.val))) (fun _ => rfl)
    rw [read k, List.getElem?_eq_getElem hl] at scan
    have put := emitBit c digit decode bit isBlank f g (address c k+c.width) k z[k]
    rw [show Function.update g (k:ℤ) (bit z[k]) = Copy.written blank bit z (k+1) from
      Copy.written_succ blank bit z k hl] at put
    have both := (ih (by omega)).trans (scan.trans (.single put))
    simpa only [Nat.mul_succ,address_succ,Nat.cast_add_one] using both

private theorem returns (z : List Bool) (f : ℤ → B)
    (hb : isBlank blank = true) (hbit : ∀ b, isBlank (bit b) = false) :
    ∀ k ≤ z.length, Trace (advance M)
      (config (.back (first c)) f (Copy.rendering blank bit z) (address c k+c.width) ((k:ℤ)-1))
      ((c.width+1)*(k+1)) (config .done f (Copy.rendering blank bit z) 0 0) := by
  intro k hk
  let g := Copy.rendering blank bit z
  induction k with
  | zero =>
    have scan := backBlock c digit decode bit isBlank f g 0 (-1)
    have turn := prevEnd c digit decode bit isBlank f g 0 (-1)
      (by exact hb)
    simpa [address] using scan.trans (.single turn)
  | succ k ih =>
    have hl : k < z.length := by omega
    have byte : isBlank (g (k:ℤ)) = false := by
      simpa [g,Copy.rendering,Tape.loaded,Tape.absolute,List.getElem?_eq_getElem hl] using hbit z[k]
    have scan := backBlock c digit decode bit isBlank f g (address c (k+1)) k
    have turn := prevBit c digit decode bit isBlank f g (address c (k+1)) k byte
    have rest := ih (by omega)
    rw [← address_succ] at rest
    have both := (scan.trans (.single turn)).trans rest
    simpa [Nat.mul_succ,add_comm (c.width+1),Nat.cast_add_one] using both

/-- Read the complete string and its end block, and return both heads to zero
without modifying the encoded source. No bit value indicates the end. -/
theorem run (z : List Bool) (f : ℤ → B) (hb : isBlank blank = true)
    (hbit : ∀ b, isBlank (bit b) = false)
    (read : ∀ j : ℕ, decode (c.dec (fun d => digit (f ((j:ℤ)*c.width + d.val)))) = z[j]?) :
    Trace (advance M) (config (start c) f (fun _ => blank) 0 0)
      (2*((c.width+1)*(z.length+1))) (config .done f (Copy.rendering blank bit z) 0 0) ∧
      advance M (config .done f (Copy.rendering blank bit z) 0 0) = none := by
  have all := emits c digit decode bit isBlank blank z f read z.length le_rfl
  rw [Copy.written_all] at all
  let g := Copy.rendering blank bit z
  have scan := readBlock c digit decode bit isBlank f g (address c z.length) z.length
    (fun d => digit (f (address c z.length + d.val))) (fun _ => rfl)
  rw [show decode (c.dec (fun d => digit (f (address c z.length + d.val)))) = none by
    simpa [address] using read z.length] at scan
  have endStep := emitEnd c digit decode bit isBlank f g (address c z.length+c.width) z.length
  have back := returns c digit decode bit isBlank blank z f hb hbit z.length le_rfl
  refine ⟨?_,rfl⟩
  convert ((all.trans scan).trans (.single endStep)).trans back using 1
  ring

private theorem map_loaded {D : Type} (emb : D → B) (base : D) (xs : List D) (p : ℤ) :
    (Tape.loaded (emb base) (xs.map emb)).absolute p =
      emb ((Tape.loaded base xs).absolute p) := by
  cases p with
  | ofNat k =>
    simp only [Tape.loaded,Tape.absolute,sub_zero,List.getElem?_map]
    cases xs[k]? <;> rfl
  | negSucc => rfl

/-- Whole encoded candidate output supplies the per-block decoding condition
even when the first output bits are zero or the word is empty. -/
theorem read_encoded (emb : Option Bool → B) (digit_emb : ∀ d, digit (emb d) = d)
    (srcBlank : A) (srcBit : Bool → A) (hblank : c.enc srcBlank = fun _ => none)
    (decodeBlank : decode srcBlank = none) (decodeBit : ∀ b, decode (srcBit b) = some b)
    (z : List Bool) (f : ℤ → B)
    (raw : f = (Tape.loaded (emb none) ((c.encodeList (z.map srcBit)).map emb)).absolute)
    (j : ℕ) :
    decode (c.dec (fun d => digit (f ((j:ℤ)*c.width + d.val)))) = z[j]? := by
  have codes : (fun d : Fin c.width => digit (f ((j:ℤ)*c.width + d.val))) =
      c.enc ((Tape.loaded srcBlank (z.map srcBit)).absolute j) := by
    funext d
    rw [raw,map_loaded,digit_emb,c.loaded_absolute_block srcBlank hblank]
  rw [codes,c.decode_encode]
  simp only [Tape.loaded,Tape.absolute,sub_zero,List.getElem?_map]
  cases z[j]? <;> simp [decodeBlank,decodeBit]

/-- Canonical invocation over two physical tapes, both with their heads at the
origin. Tape `false` holds the encoded word; tape `true` holds the literal bits. -/
theorem run_encoded (emb : Option Bool → B) (digit_emb : ∀ d, digit (emb d) = d)
    (srcBlank : A) (srcBit : Bool → A) (hblank : c.enc srcBlank = fun _ => none)
    (decodeBlank : decode srcBlank = none) (decodeBit : ∀ b, decode (srcBit b) = some b)
    (hb : isBlank blank = true) (hbit : ∀ b, isBlank (bit b) = false) (z : List Bool) :
    let src := Tape.loaded (emb none) ((c.encodeList (z.map srcBit)).map emb)
    let input : Bool → Tape B := fun i => if i then Tape.loaded blank [] else src
    let output : Bool → Tape B := fun i => if i then Tape.loaded blank (z.map bit) else src
    Trace (advance M) ⟨start c,input⟩ (2*((c.width+1)*(z.length+1))) ⟨.done,output⟩ ∧
      advance M ⟨.done,output⟩ = none := by
  let src := Tape.loaded (emb none) ((c.encodeList (z.map srcBit)).map emb)
  have hist := run c digit decode bit isBlank blank z src.absolute hb hbit
    (read_encoded c digit decode emb digit_emb srcBlank srcBit hblank decodeBlank decodeBit z _ rfl)
  have loaded_at {D : Type} (d : D) (xs : List D) :
      Reset.atHead 0 (Tape.loaded d xs).absolute = Tape.loaded d xs := by
    simp [Reset.atHead,Tape.absolute,Tape.loaded]
  have clean : Reset.atHead 0 (fun _ : ℤ => blank) = Tape.loaded blank [] := by
    unfold Reset.atHead Tape.loaded
    congr 1
    funext x
    cases x <;> simp
  have inputT : tapes src.absolute (fun _ => blank) 0 0 =
      (fun i : Bool => if i then Tape.loaded blank [] else src) := by
    funext i
    cases i <;> simp [tapes,src,loaded_at,clean]
  have outputT : tapes src.absolute (Copy.rendering blank bit z) 0 0 =
      (fun i : Bool => if i then Tape.loaded blank (z.map bit) else src) := by
    funext i
    cases i
    · exact loaded_at _ _
    · exact loaded_at _ _
  simpa only [config,inputT,outputT] using hist

end CommonAlphabet.Compact

end NearSquareRoot
end Computability
end OAI
