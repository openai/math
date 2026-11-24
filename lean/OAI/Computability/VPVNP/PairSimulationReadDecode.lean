import OAI.Computability.VPVNP.PairSimulationFieldRead
import OAI.Computability.VPVNP.PairSimulationMapLookup

/-!
# Reading and decoding one selector inside a vertex call

The field loop exits directly at the selector table's first instruction.
Both fragments use the same accumulator for the raw tag and the same
temporary. The ordinal can replace the accumulator or be retained in a
separate register. Unused codes go to the rejecting exit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ReadDecode

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifEntry
open scoped Fin.CommRing

variable {X : Type*} {w p r k b len : ℕ}

/-- The code table for one selector uses the field reader's result and
temporary registers. -/
def selectorFlow (xs : List X) (key name : X → Fin k) (reg : Fin 6 ↪ Fin r)
    (out : Fin r) : Flow r k :=
  (MapLookup.table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ reg 0) (reg 5) out name

/-- The complete in-call result, including the raw tag when the output is
allocated separately. The cursor points at the low end of the field. -/
def Runs (M : Machine w p r k) (c : Config w p r) (reg : Fin 6 ↪ Fin r)
    (out : Fin r) (stop bad : Fin p) (name : X → Fin k) (raw : Word w)
    (low cap : ℕ) (result : Option X) : Prop :=
  ∃ n final, n ≤ cap ∧ Prefix M c (List.replicate n .tick) final ∧
    (match result with
     | none => final.pc = bad
     | some x => final.pc = stop ∧ final.reg out = M.publicData (name x)) ∧
    final.reg (reg 1) = (low : Word w) ∧
    (reg 0 ≠ out → final.reg (reg 0) = raw) ∧
    (∀ a, a ≠ reg 0 → a ≠ reg 1 → a ≠ reg 5 → a ≠ out → final.reg a = c.reg a) ∧
    final.privateMem = c.privateMem ∧ final.persistent = c.persistent

/-- A missing selector rejects even if the budget expires before the lookup. -/
theorem Runs.rejects {M : Machine w p r k} {c : Config w p r} {reg : Fin 6 ↪ Fin r}
    {out : Fin r} {stop bad : Fin p} {name : X → Fin k} {raw : Word w} {low cap : ℕ}
    (h : Runs M c reg out stop bad name raw low cap none) (hb : M.code bad = .reject)
    (fuel : ℕ) (mem : Memory w) (bits : List Bool) : execute M.program fuel c mem bits = none := by
  obtain ⟨n, d, _, pre, hd, _⟩ := h
  exact MapLookup.reject_after_ticks pre (fun e he ↦ List.eq_of_mem_replicate he)
    (hd ▸ hb) fuel mem bits

/-- From the field loop entry, read the actual private bits and compare the
result against the public code table. A field in the padded tail needs no
additional initialized cells. The two bounds are instruction dispatches. -/
theorem native (M : Machine w p r k) (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r)
    (out : Fin r) (hcur : reg 1 ≠ out) (xs : List X) (code : X ↪ Word b)
    (key name : X → Fin k) (fits : b ≤ w)
    (hkey : ∀ x, M.publicData (key x) = MapLookup.widen fits (code x))
    (label : (selectorFlow xs key name reg out).Label → Fin p) (stop bad : Fin p)
    (read : FieldRead.Linked M pc reg (label (selectorFlow xs key name reg out).entry))
    (lookup : Flow.Linked M (selectorFlow xs key name reg out) label stop bad)
    (bits : Fin len → Bool) (base off : ℕ) (c : Config w p r) (hc : c.pc = pc 0)
    (hf : base + off + b < 2 ^ w) (hd : base + len < 2 ^ w) (hzero : c.reg (reg 0) = 0)
    (hhigh : c.reg (reg 1) = ((base + off + b : ℕ) : Word w))
    (hlow : c.reg (reg 2) = ((base + off : ℕ) : Word w))
    (hend : c.reg (reg 3) = ((base + len : ℕ) : Word w)) (hone : c.reg (reg 4) = 1)
    (hdata : ∀ i : Fin len, c.privateMem ((base + i.val : ℕ) : Word w) = encodeBit w (bits i)) :
    Runs M c reg out stop bad name (MapLookup.widen fits (fieldIndex bits off b))
      (base + off) ((6 * b + 1) + (2 * xs.length + 1))
      (decode xs code (fieldIndex bits off b)) := by
  obtain ⟨mid, pre, hm, hv, hcursor, frame, hmem, hstate⟩ :=
    FieldRead.native_read read bits base off b c hc fits hf hd hzero hhigh hlow hend hone hdata
  rw [meteredField_spec] at pre
  have htag : mid.reg (reg 0) = MapLookup.widen fits (fieldIndex bits off b) := Fin.ext hv
  obtain ⟨n, final, bound, scan, exit, rest, mem, state⟩ :=
    MapLookup.native_selector fits xs code key name (reg 0) (reg 5) out
      (reg.injective.ne (by decide)) (fieldIndex bits off b) M hkey label stop bad
      lookup mid hm htag
  refine ⟨(6 * b + 1) + n, final, Nat.add_le_add_left bound _, ?_, exit, ?_, ?_, ?_,
    mem.trans hmem, state.trans hstate⟩
  · rw [List.replicate_add]
    exact pre.append scan
  · exact (rest _ (reg.injective.ne (by decide)) hcur).trans hcursor
  · intro ha
    exact (rest _ (reg.injective.ne (by decide)) ha).trans htag
  · intro a h₀ h₁ h₅ ha
    exact (rest _ h₅ ha).trans (frame a h₀ h₁ h₅)

/-- The selector read for copy i starts above the payload. Its two absolute
endpoints fit whenever the incident wire's exclusive end fits. -/
theorem tag_fits {u payload : ℕ} (base : ℕ) (i : Fin u)
    (fit : base + (payload + u * b) < 2 ^ w) :
    base + (payload + b * i.val) + b < 2 ^ w := by
  have h := Nat.mul_le_mul_left b i.isLt
  rw [Nat.mul_succ] at h
  rw [Nat.mul_comm u b] at fit
  omega

/-- Decode the exact selector used by the motif evaluator on an incident
wire. The program and its public code ports are fixed across copy indices. -/
theorem native_tag {u payload : ℕ} (M : Machine w p r k) (pc : Fin 7 → Fin p)
    (reg : Fin 6 ↪ Fin r) (out : Fin r) (hcur : reg 1 ≠ out) (xs : List X)
    (code : X ↪ Word b) (key name : X → Fin k) (fits : b ≤ w)
    (hkey : ∀ x, M.publicData (key x) = MapLookup.widen fits (code x))
    (label : (selectorFlow xs key name reg out).Label → Fin p) (stop bad : Fin p)
    (read : FieldRead.Linked M pc reg (label (selectorFlow xs key name reg out).entry))
    (lookup : Flow.Linked M (selectorFlow xs key name reg out) label stop bad)
    (bits : Fin (payload + u * b) → Bool) (base : ℕ) (i : Fin u) (c : Config w p r)
    (hc : c.pc = pc 0) (hd : base + (payload + u * b) < 2 ^ w) (hzero : c.reg (reg 0) = 0)
    (hhigh : c.reg (reg 1) = ((base + (payload + b * i.val) + b : ℕ) : Word w))
    (hlow : c.reg (reg 2) = ((base + (payload + b * i.val) : ℕ) : Word w))
    (hend : c.reg (reg 3) = ((base + (payload + u * b) : ℕ) : Word w))
    (hone : c.reg (reg 4) = 1)
    (hdata : ∀ j : Fin (payload + u * b),
      c.privateMem ((base + j.val : ℕ) : Word w) = encodeBit w (bits j)) :
    Runs M c reg out stop bad name (MapLookup.widen fits (readTag bits i))
      (base + (payload + b * i.val)) ((6 * b + 1) + (2 * xs.length + 1))
      (decode xs code (readTag bits i)) :=
  native M pc reg out hcur xs code key name fits hkey label stop bad read lookup bits base _
    c hc (tag_fits base i hd) hd hzero hhigh hlow hend hone hdata

end PairSimulation.ReadDecode

end VPVNP
end Computability
end OAI
