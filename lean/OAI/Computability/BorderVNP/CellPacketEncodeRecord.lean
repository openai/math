import OAI.Computability.BorderVNP.CellPacketEncodeInner

/-! # One physical source load and one complete generator record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketEncode

open VPVNP.BurstRAM RationalHitting.StackLanguage

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- Observable effect of consuming a number of source words and emitting their digits. -/
structure Effect (start : NatState) (count : ℕ) (bits : List Bool) (finish : NatState) : Prop where
  /-- Scratch and cursor registers alone can change. -/
  fixed : Fixed start.reg finish.reg
  /-- Number of source words consumed. -/
  source : finish.reg 14 = start.reg 14 + count
  /-- Output cursor after the encoded digits. -/
  destination : finish.reg 20 = start.reg 20 + bits.length
  /-- Full output memory image. -/
  memory : finish.mem = putDigits start.mem (start.reg 20) bits

/-- Word consumption and digit writes compose in their chronological order. -/
theorem Effect.append {s t z : NatState} {a b : ℕ} {xs ys : List Bool}
    (f : Effect s a xs t) (g : Effect t b ys z) : Effect s (a+b) (xs++ys) z :=
  ⟨f.fixed.trans g.fixed, by rw [g.source,f.source,Nat.add_assoc],
    by rw [g.destination,f.destination,List.length_append,Nat.add_assoc],
    by rw [putDigits_append, ← f.memory, ← f.destination, g.memory]⟩

/-- Writing a bit does not consume a source word. -/
theorem Written.effect {s t : NatState} {xs : List Bool} (h : Written s xs t) : Effect s 0 xs t :=
  ⟨fun j _ _ _ d => h.regs j d, (h.regs 14 (by decide)).trans (Nat.add_zero _).symm,
    h.cursor,h.mem⟩

private theorem load_run (s : Bank w) (m : Memory w) (a : ℕ)
    (src : readings m (readings s 14) = a) (c : Constants (readings s))
    (fit : readings s 14 + 1 < 2^w) :
    BoundedRun pub macros (.block [.load 16 14, .binary .add 14 14 1]) s m 2
      (fun z => Effect (.ofWords s m) 1 [] z ∧ z.reg 16 = a) := by
  let block := Code.block [.load 16 14, .binary .add 14 14 1]
  have safe : block.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [block, Code.block, Code.fixedSafe, Code.safeReadOnly,
      Code.fixedEval, Code.evalNat, addressOpFits, NatState.ofWords, c.2.1, fit]
  apply (block.runFixed pub macros s m safe).mono le_rfl
  rintro _ rfl
  constructor
  · constructor
    · intro j a' b' _ _
      simp [block, Code.block, Code.fixedEval, Code.evalNat, a',b']
    all_goals simp (config := {decide := true}) [block, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, NatState.ofWords, putDigits,c.2.1]
  · simp (config := {decide := true}) [block, Code.block, Code.fixedEval, Code.evalNat, NatState.ofWords, src]

/-- Exact output of a single record, including its iteration marker and scalar terminator. -/
def recordBits (e : Bool) (a : ℕ) := tags e [true] ++ tags e (pairWord a.bits) ++ tags e [true]

/-- The list scanner concatenates precisely the chunks emitted by this loop. -/
theorem packet_chunk (e : Bool) (a : ℕ) (xs : List ℕ) :
    tags e (packet (a::xs)) = recordBits e a ++ tags e (packet xs) := by
  simp only [packet_cons, tags_append, recordBits]

/-- The complete word body, including its shared-memory source load, fits the linear bit budget. -/
theorem record_run (e : Bool) (s : Bank w) (m : Memory w) (a : ℕ)
    (src : readings m (readings s 14) = a) (c : Constants (readings s))
    (srcFit : readings s 14 + 1 < 2^w)
    (dstFit : readings s 20 + (recordBits e a).length < 2^w) :
    BoundedRun pub macros (record e) s m (11*a.bits.length+11)
      (Effect (.ofWords s m) 1 (recordBits e a)) := by
  let marker := tags e [true]
  let body := tags e (pairWord a.bits)
  let count := 11*a.bits.length+1
  change readings s 20 + ((marker ++ body) ++ marker).length < 2^w at dstFit
  simp only [List.length_append] at dstFit
  have load := load_run (pub := pub) (macros := macros) s m a src c srcFit
  have run := load.seq (b := .seq (emit e 1) (.seq (.whileLt 0 16 (digit e)) (emit e 1)))
    (t := 4+(count+4)) (Q := Effect (.ofWords s m) 1 (recordBits e a)) (by
      rintro t mt ⟨f,hv⟩
      have ct := f.fixed.constants c
      have cur : readings t 20 = readings s 20 := by simpa [NatState.ofWords] using f.destination
      apply (emit_run (pub := pub) (macros := macros) e t mt 1 (by decide) true ct.2.1 ct
        (by change readings t 20 + marker.length < 2^w; omega)).seq
        (b := .seq (.whileLt 0 16 (digit e)) (emit e 1)) (t := count+4)
      intro u mu head
      have cu := head.effect.fixed.constants ct
      have cur' : readings u 20 = readings t 20+marker.length := head.cursor
      apply (inner_run (pub := pub) (macros := macros) e a u mu cu ((head.regs 16 (by decide)).trans hv)
        (by change readings u 20+body.length < 2^w; omega)).seq (b := emit e 1) (t := 4)
      rintro v mv ⟨regs,cv,memory⟩
      have inner : Effect (.ofWords u mu) 0 body (.ofWords v mv) :=
        ⟨fun j _ => regs j, (regs 14 (by decide) (by decide) (by decide)).trans (Nat.add_zero _).symm,cv,memory⟩
      have c' := inner.fixed.constants cu
      change readings v 20 = readings u 20 + body.length at cv
      apply (emit_run (pub := pub) (macros := macros) e v mv 1 (by decide) true c'.2.1 c'
        (by change readings v 20 + marker.length < 2^w; omega)).mono le_rfl
      intro z final
      simpa only [List.nil_append, Nat.add_zero, recordBits] using
        (((f.append head.effect).append inner).append final.effect))
  exact run.mono (by dsimp [count]; omega) (fun _ h => h)

end RoutingISA.CellPacketEncode

end BorderVNP
end Computability
end OAI
