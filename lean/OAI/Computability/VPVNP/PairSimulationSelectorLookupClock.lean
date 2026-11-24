import OAI.Computability.VPVNP.PairSimulationReadDecode

/-!
# Exact instruction counts for one selector lookup

The fixed selector table compares a single field per row, stopping at its
first match. Its clock is determined by the raw selector word and the
ordered public code table, including on a missing code.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapLookup

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM
open scoped Fin.CommRing

variable {X : Type*} {w p r k b : ℕ}

/-- Each tested row uses a public load and a comparison. The last
instruction transfers to the rejecting or matching continuation. -/
def selectorTicks (code : X ↪ Word b) (tag : Word b) : List X → ℕ
  | [] => 1
  | x :: xs => 2 + if code x = tag then 1 else selectorTicks code tag xs

theorem selectorTicks_le (code : X ↪ Word b) (tag : Word b) (xs : List X) :
    selectorTicks code tag xs ≤ 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [selectorTicks]
  | cons x xs ih =>
    simp only [selectorTicks, List.length_cons, Nat.mul_succ]
    split <;> omega

/-- A successful table ordinal uses two instructions for each preceding
row and two for its own row, followed by the public ordinal load. -/
theorem selectorTicks_of_mem [DecidableEq X] (code : X ↪ Word b) (x : X) (xs : List X)
    (member : x ∈ xs) : selectorTicks code (code x) xs = 2 * (xs.idxOf x + 1) + 1 := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    by_cases eq : y = x
    · subst y
      simp [selectorTicks]
    · have miss := code.injective.ne eq
      have tail : x ∈ ys := (List.mem_cons.mp member).resolve_left (Ne.symm eq)
      rw [selectorTicks, ite_eq_right miss, ih tail, List.idxOf_cons_ne ys eq]
      omega

private theorem eval_selector (M : Machine w p r k) (fits : b ≤ w) (code : X ↪ Word b)
    (key : X → Fin k) (keys : ∀ x, M.publicData (key x) = widen fits (code x)) (tag : Word b)
    (xs : List X) :
    ((table [()] (fun x _ ↦ key x) xs).eval M.publicData (fun _ ↦ widen fits tag)).2 =
      selectorTicks code tag xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : code x = tag
    · simp [table, row, Tree.eval, selectorTicks, keys, h]
    · have miss := (widen fits).injective.ne (Ne.symm h)
      simpa only [table, row, Tree.eval, selectorTicks, keys, miss, h, ↓reduceIte,
        Nat.add_left_cancel_iff] using ih

/-- Run the linked selector lookup for its computed instruction count. -/
theorem native_selector_exact (fits : b ≤ w) (xs : List X) (code : X ↪ Word b)
    (key name : X → Fin k) (src tmp out : Fin r) (ht : src ≠ tmp) (tag : Word b)
    (M : Machine w p r k) (keys : ∀ x, M.publicData (key x) = widen fits (code x))
    (label : ((table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ src) tmp out name).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M
      ((table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ src) tmp out name) label stop bad)
    (c : Config w p r) (hc : c.pc = label
      ((table [()] (fun x _ ↦ key x) xs).flow (fun _ ↦ src) tmp out name).entry)
    (hs : c.reg src = widen fits tag) :
    ∃ d, Prefix M c (List.replicate (selectorTicks code tag xs) .tick) d ∧
      (match MotifEntry.decode xs code tag with
       | none => d.pc = bad
       | some x => d.pc = stop ∧ d.reg out = M.publicData (name x)) ∧
      (∀ j, j ≠ tmp → j ≠ out → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let tree := table [()] (fun x _ ↦ key x) xs
  obtain ⟨d, pre, exit, rest, mem, pers⟩ := tree.native (fun _ ↦ src) tmp out name
    (fun _ ↦ ht) M label stop bad hl c hc
  have value := (table_eval M.publicData (fun _ : Unit ↦ c.reg src) [()] (fun x _ ↦ key x) xs).1
  have clock := eval_selector M fits code key keys tag xs
  rw [hs] at pre
  refine ⟨d, ?_, ?_, rest, mem, pers⟩
  · exact clock ▸ pre
  · change (match (tree.eval M.publicData (fun _ ↦ c.reg src)).1 with
      | none => _ | some _ => _) at exit
    unfold tree at exit
    rw [value] at exit
    simpa [MotifEntry.decode, hs, keys, eq_comm] using exit

end PairSimulation.MapLookup

namespace PairSimulation.ReadDecode

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM MotifEntry
open scoped Fin.CommRing

variable {X : Type*} {w p r k b u payload : ℕ}

/-- A tag is read with exactly six instructions per bit and one final guard,
then looked up with the clock of its actual word. -/
theorem native_tag_exact (M : Machine w p r k) (pc : Fin 7 → Fin p)
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
    ∃ d, Prefix M c
      (List.replicate ((6*b+1) + MapLookup.selectorTicks code (readTag bits i) xs) .tick) d ∧
      (match decode xs code (readTag bits i) with
       | none => d.pc = bad
       | some x => d.pc = stop ∧ d.reg out = M.publicData (name x)) ∧
      d.reg (reg 1) = ((base + (payload + b * i.val) : ℕ) : Word w) ∧
      (∀ a, a ≠ reg 0 → a ≠ reg 1 → a ≠ reg 5 → a ≠ out → d.reg a = c.reg a) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨mid, pre, hm, hv, cur, frame, hmem, hpers⟩ :=
    FieldRead.native_read read bits base _ b c hc fits (tag_fits base i hd) hd hzero hhigh hlow
      hend hone hdata
  rw [meteredField_spec] at pre
  have htag : mid.reg (reg 0) = MapLookup.widen fits (readTag bits i) := Fin.ext hv
  obtain ⟨d, scan, exit, rest, mem, pers⟩ := MapLookup.native_selector_exact fits xs code key name
    (reg 0) (reg 5) out (reg.injective.ne (by decide)) (readTag bits i) M hkey label stop bad
    lookup mid hm htag
  rw [List.replicate_add]
  exact ⟨d, pre.append scan, exit, (rest _ (reg.injective.ne (by decide)) hcur).trans cur,
    fun a h₀ h₁ h₅ hOut ↦ (rest a h₅ hOut).trans (frame a h₀ h₁ h₅),
    mem.trans hmem, pers.trans hpers⟩

end PairSimulation.ReadDecode

end VPVNP
end Computability
end OAI
