import OAI.Computability.VPVNP.PrimedStackRAMFrame
import OAI.Computability.VPVNP.PrimedStackRAMNodeRun

/-!
# Word-memory updates on a represented grammar visit

A location mark changes one bit. A production increment changes one dense
counter by one. Neither operation changes pending frames or input rows.
Popping a frame has the complementary effect on these regions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedCounter
open scoped Fin.CommRing Classical

variable {base R n m H w : ℕ} {x : Fin 2 → Fin R → Fin m → Bool}
variable {st : VisitState n m H} {mem : Memory w}

private theorem stack_store {stack : List (Word w × Word w)}
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack)
    (c : Locations R n m H) (v : Word w) (hc : dataCell c)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Represents (R := R) (n := n) (m := m) (H := H) base (store base mem c v) stack := by
  have he (a : Locations R n m H) (ha : dataCell a = false) :
      view base (store base mem c v) a = view base mem a := by
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by rintro rfl; simp [ha] at hc)]
  exact ⟨hr.fits, (congrArg Fin.val (he _ rfl)).trans hr.depth,
    fun i => (he _ rfl).trans (hr.degrees i), fun i => (he _ rfl).trans (hr.states i)⟩

/-- Set a location mark while preserving every other represented component. -/
theorem Holds.mark (hr : Holds base x st mem) (j : Fin m)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Holds base x {st with marked := insert j st.marked}
      (store base mem (markCell j : Locations R n m H) 1) := by
  refine ⟨stack_store hr.pending _ _ rfl hf, ?_, ?_, ?_⟩
  · intro g s i
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [markCell])]
    exact hr.input g s i
  · intro i
    rw [view_store_apply _ _ _ _ _ hf, hr.marked]
    by_cases hi : i = j <;> simp [markCell, hi]
  · intro a
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [countCell,markCell])]
    exact hr.counts a

/-- Increment exactly the logical Finsupp component selected by the dense label. -/
theorem Holds.increment (hr : Holds base x st mem) (a : Label n m (Fin H))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : st.counts a + 1 < 2^w) :
    let c := (countCell (labelIndex n m H a) : Locations R n m H)
    Holds base x {st with counts := st.counts + Finsupp.single a 1}
      (store base mem c (view base mem c + 1)) := by
  dsimp only
  refine ⟨stack_store hr.pending _ _ rfl hf, ?_, ?_, ?_⟩
  · intro g s i
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [countCell])]
    exact hr.input g s i
  · intro i
    rw [view_store_apply _ _ _ _ _ hf, ite_eq_right (by simp [countCell,markCell])]
    exact hr.marked i
  · intro b
    rw [view_store_apply _ _ _ _ _ hf]
    by_cases h : a = b
    · subst b
      have hh := Fin.val_add_one_of_lt' (i := view base mem
        (countCell (labelIndex n m H a) : Locations R n m H)) ((hr.counts a) ▸ hc)
      simp [hh, hr.counts a]
    · simp [countCell, Ne.symm h]
      exact hr.counts b

private theorem pop_zero {pub : Fin 11 → Word w} {state : Word w} {regs rs : Regs w 16}
    {m' : Memory w} {es} (ht : trace pub state pop regs mem = some (es, rs, m')) : rs 12 = 0 := by
  by_cases h : 0 < mem (pub 4).val
  · simp (config := { decide := true }) [pop, trace, Op.effect, Function.update, h] at ht
    rw [← ht.2.1]
    simp (config := { decide := true }) [Function.update]
  · simp (config := { decide := true }) [pop, trace, Op.effect, Function.update, h] at ht

/-- Pop the next logical frame. The row register survives, and the branch test
register is zero even when arbitrary temporaries were supplied on entry. -/
theorem pop_holds (hr : Holds base x st mem) {d : Fin n} {h : Fin H} {tail : List (Frame n (Fin H))}
    (hp : st.pending = (d,h)::tail) (hf : base + size R n m (labelCount n m H) ≤ 2^w)
    (state : Word w) (regs : Regs w 16) :
    ∃ es rs m', trace (publicData w base R n m H) state pop regs mem = some (es,rs,m') ∧
      Holds base x {st with pending := tail} m' ∧ rs 0 = (d.val : Word w) ∧
      rs 1 = (h.val : Word w) ∧ rs 5 = regs 5 ∧ rs 12 = 0 ∧ countProbes es = 4 := by
  have hs := hr.pending
  rw [hp] at hs
  change Represents base ((mem : Memory w)) ((↑d.val, ↑h.val)::frames w tail) at hs
  obtain ⟨es, rs, m', ht, hc, hm, hd, hh⟩ := pop_rep state regs hs hf
  refine ⟨es, rs, m', ht, hr.withStack tail (pop_data hs hf ht) hm, hd, hh, ?_, pop_zero ht, hc⟩
  exact trace_preserves (by decide) ht

/-- Zero pending frames reject immediately at the underflow guard. -/
theorem pop_holds_empty (hr : Holds base x st mem) (hp : st.pending = [])
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (state : Word w) (regs : Regs w 16) :
    trace (publicData w base R n m H) state pop regs mem = none := by
  apply pop_empty
  rw [public_depth_val base hf]
  have hh := len_word hr.pending
  rw [hp] at hh
  exact hh

/-- Read the assembled terminal bit from the physical row selected by the outer schedule. -/
theorem leafBit_cell (hr : Holds base x st mem) (g : Fin 2) (s : Fin R) (j : Fin m)
    (state : Word w) (regs : Regs w 16) (hpos : regs 2 = (j.val : Word w))
    (hrow : regs 5 = (↑((g.val * R + s.val)*m) : Word w))
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hw : 2 < 2^w) :
    ∃ es rs, trace (publicData w base R n m H) state leafBit regs mem = some (es,rs,mem) ∧
      rs 6 = (↑(x g s j).toNat : Word w) ∧ countProbes es = 1 := by
  let pub := publicData w base R n m H
  let c : Locations R n m H := .inl ((g,s),j)
  have haddr : pub 8 + regs 5 + regs 2 = (address base c : Word w) := by
    rw [hrow, hpos, show address base c = _ from address_input base g s j, Nat.cast_add, Nat.cast_add]
    rfl
  have hread : mem (pub 8 + regs 5 + regs 2).val = (↑(x g s j).toNat : Word w) := by
    rw [haddr, Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf c)]
    exact hr.input g s j
  have hm : m < 2^w := by unfold size at hf; omega
  have hj : regs 2 < pub 6 := by
    rw [hpos]
    change (j.val : Word w).val < (m : Word w).val
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt (j.isLt.trans hm), Nat.mod_eq_of_lt hm] using j.isLt
  have hb : mem (pub 8 + regs 5 + regs 2).val < 2 := by
    rw [hread]
    change (↑(x g s j).toNat : Word w).val < (2 : Word w).val
    rw [Fin.val_natCast, show (2 : Word w).val = 2 from Nat.mod_eq_of_lt hw]
    cases x g s j <;> simp [Nat.mod_eq_of_lt (by omega : 1 < 2^w)]
  obtain ⟨es,rs,ht,hc,_,hv⟩ := leafBit_spec pub state regs mem hj hb
  exact ⟨es,rs,ht,hv.trans hread,hc⟩

end PrimedStackRAM

end VPVNP
end Computability
end OAI
