import OAI.Computability.IntegerMultiplication.Bits.Multiply
import OAI.Computability.IntegerMultiplication.Interface

namespace OAI
namespace Computability
namespace IntegerMultiplication

open Bits Interface Code
variable {X Y : Type*}

theorem endianness (l : List Bool) : bitValue l=value l.reverse := by
  suffices h : ∀ (l : Word) (n : ℕ),
    l.foldl (fun v b => 2*v + b.toNat) n = n*2^l.length+value l.reverse by simpa [bitValue] using h l 0
  intro l n
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    simp [ih,value_append,pow_succ]
    have he : digit a=a.toNat := by cases a <;> rfl
    rw [he]
    ring

/-- Domain of pairs with a common bit length (including zero). -/
abbrev Inputs := {i : Toom.IW // i.1.length=i.2.length}

def reversed (x : Toom.IW) : Toom.IW := (x.1.reverse,x.2.reverse)

def writeAns (x : Inputs) := (Toom.reply (reversed x.val)).reverse

-- Unfolding macro for budget proofs; mathlib's `clog` is ceiling.
theorem bits_length {n x : ℕ} (h : x<2^n) :
    ∃! l : Word, l.length=n ∧ bitValue l=x := by
  use (phrase n x).reverse
  constructor
  · simp [endianness,value_phrase h,phrase_length]
  intro y he
  apply List.reverse_injective
  rw [List.reverse_reverse]
  apply word_inject
  · simp [phrase_length,he.1]
  · rw [← endianness,value_phrase h,he.2]

/-- Checked partial result: exact product with time at most a constant times the
conservative short-operand multiplier budget, i.e. 2^j 8^floor(j/127) for
j = ceiling log2 n. Not the claimed n(log n) power bound. Includes tape and I/O.
-/
theorem tape_short :
    (Promise Inputs (fun i => i.val) writeAns (fun i => Toom.budget (Nat.clog 2 i.val.1.length))) ∧
    ∀ i : Inputs, (writeAns i).length=2*i.val.1.length ∧
      bitValue (writeAns i) = bitValue i.val.1 * bitValue i.val.2 := by
  let z (i : Inputs) := Nat.clog 2 i.val.1.length
  have hb (i : Inputs) : i.val.1.length ≤ 2^z i := Nat.le_pow_clog (by decide) _
  have hf (i : Inputs) : i.val.1.length ≤ Toom.budget (z i) := (hb i).trans (Toom.budget_ge _)
  have hs (i : Inputs) : (writeAns i).length=2*i.val.1.length := by
    simp [writeAns,reversed]; rw [← i.property]; omega
  constructor
  · have : NeZero (2^128 : ℕ) := ⟨(Nat.pow_pos (by decide)).ne'⟩
    have : Toom.Accord (2^128 : ℕ) := ⟨rfl⟩
    have h := (Toom.equal_mul (2^128)).on
      (fun i : Inputs => ⟨(reversed i.val,z i), by simp [reversed,i.property.symm]; exact hb i⟩)
    have he : Easy reversed := by unfold reversed; fun_prop
    have hw := Easy.reverse (X:=Bool)
    have hr := (((Task.on he fun i : Inputs => i.val).compose h).compose (Task.on hw (fun i : Inputs => Toom.reply (reversed i.val))))
    obtain ⟨A,Q,I,f,g,e,bt,Z,U,o,v,t,m,C,H1,H2,H3,H⟩ := Promise.stack
      (q:=fun i : Inputs => i.val) (w:=writeAns) hr
    refine ⟨A,Q,I,f,g,e,bt,Z,U,o,v,t,m,20*C,H1,H2,H3,fun y => ?_⟩
    obtain ⟨k,y',h₁,h₂,h',m'⟩ := H y
    refine ⟨_,_,h₁,h₂,h',m'.trans ?_⟩
    dsimp only
    rw [hs]
    rw [mul_comm 20, Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    simp only [size_prod,size_word,Toom.reply_len,reversed,List.length_reverse,y.property.symm]
    have := hf y
    have hh := y.property
    dsimp only [z] at *
    simp only [hh] at *
    omega
  · intro i
    refine ⟨hs i,?_⟩
    simp [writeAns,reversed,endianness]

end IntegerMultiplication
end Computability
end OAI
