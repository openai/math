import OAI.Computability.VPVNP.PrimedCounterAdmin
import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedCounterAdminFrame
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Logical memory effects of scheduled administrative calls

The enlarged public table embeds the parser's eleven public words and supplies
the root and the nomination base in its last three entries. The following
executions apply to any such embedding, including the scratch rectangle after
input assembly. All writes retain every word in the reserved prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Admin

open BurstRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing Classical

variable {w R n m H base : ℕ} {pub : Fin 14 → Word w}
variable (hp : pub ∘ stackPublic = publicData w base R n m H)
variable (hf : base + size R n m (labelCount n m H) ≤ 2^w)
variable (state : Word w) (regs : Regs w 16) (mem : Memory w)

include hp

private theorem stack_word (i : ℕ) (hi : i < 11 := by decide) :
    pub (OfNat.ofNat i) = publicData w base R n m H (OfNat.ofNat i) := by
  have he : (OfNat.ofNat i : Fin 14) = stackPublic (OfNat.ofNat i : Fin 11) := by
    apply Fin.ext
    change i % 14 = i % 11
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega : i < 14)]
  rw [he]
  exact congrFun hp _

include hf

/-- Clear one in-range mark and retain the entire prefix below the scratch base. -/
theorem clear_cell (j : Fin m) (hj : regs 2 = (j.val : Word w)) :
    let out := store base mem (markCell j : Locations R n m H) 0
    ∃ es rs, Flow.Exec pub state clear regs mem es rs out ∧
      countProbes es = 1 ∧ es.length = 6 ∧ choiceBits es = [] ∧ ∀ a < base, out a = mem a := by
  dsimp only
  have hm : m < 2^w := by unfold size at hf; omega
  have hj' : regs 2 < pub 6 := by
    rw [hj, stack_word hp 6]
    change (j.val : Word w).val < (m : Word w).val
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt (j.isLt.trans hm), Nat.mod_eq_of_lt hm] using j.isLt
  obtain ⟨es,rs,ht,hc,hl,hb⟩ := clear_trace pub state regs mem hj'
  rw [stack_word hp 2, hj, public_mark base j] at ht
  exact ⟨es,rs,(exec_lines_iff_trace _).mpr ht,hc,hl,hb,fun _ ha => store_below _ _ _ hf ha⟩

omit hf in
theorem rootMemory_eq (d : Fin n) (root : Fin H) (hd : pub 11 = (d.val : Word w))
    (hr : pub 12 = (root.val : Word w)) :
    rootMemory pub mem = rootStore base R m mem d root := by
  let slot : Fin n := ⟨0, (Nat.zero_le d.val).trans_lt d.isLt⟩
  have hdeg := public_degree (R := R) (m := m) (H := H) (w := w) base slot
  have hstate := public_state (R := R) (m := m) (H := H) (w := w) base slot
  simp only [slot, Nat.cast_zero, add_zero] at hdeg hstate
  rw [rootMemory, hd, hr, stack_word hp 0, stack_word hp 1, stack_word hp 4, hdeg, hstate, public_depth base]
  rfl

/-- Initialize the singleton pending stack. Every data cell and every word
below the scratch rectangle retain their prior values. -/
theorem init_cell (d : Fin n) (root : Fin H) (hd : pub 11 = (d.val : Word w))
    (hr : pub 12 = (root.val : Word w)) :
    let out := rootStore base R m mem d root
    ∃ es rs, Flow.Exec pub state init regs mem es rs out ∧
      countProbes es = 3 ∧ es.length = 9 ∧ choiceBits es = [] ∧
      Represents (R := R) (n := n) (m := m) (H := H) base out (frames w [(d,root)]) ∧
      DataEq base R n m H mem out ∧ ∀ a < base, out a = mem a := by
  obtain ⟨es,rs,ht,hc,hl,hb⟩ := init_trace pub state regs mem
  rw [rootMemory_eq hp mem d root hd hr] at ht
  refine ⟨es,rs,(exec_lines_iff_trace _).mpr ht,hc,hl,hb,root_rep mem d root hf,root_data mem d root hf,?_⟩
  intro a ha
  simp only [rootStore, store_below _ _ _ hf ha]

private theorem count_words (j : Fin (labelCount n m H)) (hj : regs 7 = (j.val : Word w))
    (L : Lengths) (hn : pub 13 = (Header.count L : Word w))
    (hprefix : Header.count L + labelCount n m H ≤ base) :
    regs 7 < pub 10 ∧
      mem (pub 3 + regs 7).val = view base mem (countCell j : Locations R n m H) ∧
      mem (pub 13 + regs 7).val = mem (Header.count L + j.val) := by
  have hT : labelCount n m H < 2^w := by unfold size at hf; omega
  have ha := Nat.add_lt_add_left j.isLt (Header.count L)
  have hnom : Header.count L + j.val < 2^w := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hj, stack_word hp 10]
    change (j.val : Word w).val < (labelCount n m H : Word w).val
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt (j.isLt.trans hT), Nat.mod_eq_of_lt hT] using j.isLt
  · rw [hj, stack_word hp 3, public_count base j, Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf (countCell j))]
    rfl
  · rw [hn, hj, ← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt hnom]

variable {x : Fin 2 → Fin R → Fin m → Bool} {st : VisitState n m H}

/-- The physical comparison succeeds with its two reads precisely when the
logical count equals the nominated unsigned word. A successful comparison leaves memory intact. -/
theorem compare_cell (held : Holds base x st mem) (j : Fin (labelCount n m H))
    (hj : regs 7 = (j.val : Word w)) (L : Lengths) (hn : pub 13 = (Header.count L : Word w))
    (hprefix : Header.count L + labelCount n m H ≤ base) :
    let agrees := st.counts ((labelIndex n m H).symm j) = (mem (Header.count L + j.val)).val
    (agrees → ∃ es rs, Flow.Exec pub state compare regs mem es rs mem ∧
      countProbes es = 2 ∧ es.length = 9 ∧ choiceBits es = []) ∧
    (¬ agrees → ∀ es rs out, ¬Flow.Exec pub state compare regs mem es rs out) := by
  obtain ⟨hbound,hcount,hnom⟩ := count_words hp hf regs mem j hj L hn hprefix
  have he : mem (pub 3 + regs 7).val = mem (pub 13 + regs 7).val ↔
      st.counts ((labelIndex n m H).symm j) = (mem (Header.count L + j.val)).val := by
    rw [hcount, hnom]
    exact compare_iff held j (mem (Header.count L + j.val))
  constructor
  · intro h
    obtain ⟨es,rs,ht,hc,hl,hb⟩ := compare_trace pub state regs mem hbound (he.mpr h)
    exact ⟨es,rs,(exec_lines_iff_trace _).mpr ht,hc,hl,hb⟩
  · intro h es rs out hx
    have ht := (exec_lines_iff_trace (ops := compareOps) (by decide)).mp hx
    rw [compare_reject pub state regs mem (Or.inr (fun hh => h (he.mp hh)))] at ht
    contradiction

end PrimedCounter.Admin

end VPVNP
end Computability
end OAI
