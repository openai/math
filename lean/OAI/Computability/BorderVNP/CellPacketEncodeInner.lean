import OAI.Computability.BorderVNP.CellPacketEncodeDigit

/-! # Binary length and physical loop execution for one sparse integer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketEncode

open VPVNP.BurstRAM RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- A false native loop guard accounts for exactly one tick and preserves the state. -/
theorem loop_done {x y : Reg} {body : Code} {s : Bank w} {m : Memory w} {P : NatState → Prop}
    (guard : ¬ s x < s y) (h : P (.ofWords s m)) :
    BoundedRun pub macros (.whileLt x y body) s m 1 P :=
  ⟨_,s,m,Runs.whileDone guard,le_rfl,h⟩

/-- A true guard adds one tick to the body and remaining loop execution. -/
theorem loop_step {x y : Reg} {body : Code} {s : Bank w} {m : Memory w} {d f : ℕ}
    {P Q : NatState → Prop} (guard : s x < s y) (first : BoundedRun pub macros body s m d P)
    (rest : ∀ t mt, P (.ofWords t mt) → BoundedRun pub macros (.whileLt x y body) t mt f Q) :
    BoundedRun pub macros (.whileLt x y body) s m (1+d+f) Q := by
  obtain ⟨es,t,mt,r,hr,h⟩ := first
  obtain ⟨fs,u,mu,g,hg,k⟩ := rest t mt h
  refine ⟨_,u,mu,Runs.whileStep guard r g,?_,k⟩
  change 1+traceCost (es++fs) ≤ _
  rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
  omega

/-- Execution of the inner loop consumes precisely the canonical little-endian binary
expansion. In particular zero emits no digits. -/
theorem inner_run (e : Bool) (a : ℕ) (s : Bank w) (m : Memory w)
    (c : Constants (readings s)) (hv : readings s 16 = a)
    (fit : readings s 20 + (tags e (pairWord a.bits)).length < 2^w) :
    BoundedRun pub macros (.whileLt 0 16 (digit e)) s m (11*a.bits.length+1) (fun z =>
      (∀ j, j ≠ 16 → j ≠ 17 → j ≠ 20 → z.reg j = readings s j) ∧
      z.reg 20 = readings s 20 + (tags e (pairWord a.bits)).length ∧
      z.mem = putDigits (readings m) (readings s 20) (tags e (pairWord a.bits))) := by
  induction a using Nat.binaryRec' generalizing s m with
  | zero =>
    simp only [Nat.zero_bits, List.length_nil, Nat.mul_zero, Nat.zero_add,
      pairWord_nil, tags_nil, Nat.add_zero, putDigits]
    exact loop_done (show ¬readings s 0 < readings s 16 by rw [c.1,hv]; omega)
      ⟨fun _ _ _ _ => rfl,rfl,rfl⟩
  | bit b a normal ih =>
    let first := tags e [false,b]
    let tail := tags e (pairWord a.bits)
    have bits := Nat.bits_append_bit a b normal
    have split : tags e (pairWord (Nat.bit b a).bits) = first++tail := by
      rw [bits, pairWord_cons, show false :: b :: pairWord a.bits = [false,b] ++ pairWord a.bits by rfl,
        tags_append]
    have pos : 0 < Nat.bit b a := by
      cases b <;> simp [Nat.bit_val] at normal ⊢; omega
    have guard : s 0 < s 16 := show readings s 0 < readings s 16 by rw [c.1,hv]; exact pos
    rw [split, List.length_append] at fit
    have d := digit_run (pub := pub) (macros := macros) e s m (Nat.bit b a) c hv
      (by rw [Nat.bodd_bit]; change readings s 20+first.length < 2^w; omega)
    rw [Nat.bodd_bit, Nat.bit_div_two] at d
    have tailRun (t : Bank w) (mt : Memory w) (hq : readings t 16 = a)
        (hr : ∀ j, j ≠ 16 → j ≠ 17 → j ≠ 20 → readings t j = readings s j)
        (hc : readings t 20 = readings s 20+first.length)
        (hm : readings mt = putDigits (readings m) (readings s 20) first) :=
      ih t mt ((show Fixed (readings s) (readings t) from fun j _ => hr j).constants c) hq
        (by change readings t 20 + tail.length < 2^w; omega)
    apply (loop_step (f := 11*a.bits.length+1) guard d (Q := fun z =>
      (∀ j, j ≠ 16 → j ≠ 17 → j ≠ 20 → z.reg j = readings s j) ∧
      z.reg 20 = readings s 20 + (first++tail).length ∧
      z.mem = putDigits (readings m) (readings s 20) (first++tail)) ?_).mono
    · rw [bits,List.length_cons,Nat.mul_add]; omega
    · intro z h
      simpa only [split] using h
    · rintro t mt ⟨hq,hr,hc,hm⟩
      apply (tailRun t mt hq hr hc hm).mono le_rfl
      rintro z ⟨regs,cursor,mem⟩
      change readings t 20 = readings s 20+first.length at hc
      change readings mt = putDigits (readings m) (readings s 20) first at hm
      exact ⟨fun j a' b' c' => (regs j a' b' c').trans (hr j a' b' c'),
        by rw [cursor,hc,List.length_append,Nat.add_assoc],
        by rw [putDigits_append, ← hm, ← hc, mem]⟩

end RoutingISA.CellPacketEncode

end BorderVNP
end Computability
end OAI
