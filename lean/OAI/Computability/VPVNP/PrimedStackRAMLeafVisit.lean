import OAI.Computability.VPVNP.PrimedStackRAMState

/-!
# Terminal visits of the primed counter

For a fresh chosen position, the native instructions set the location mark,
fetch the actual row bit and increment exactly that production. Repeated
and out-of-range choices fail before reaching the increment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedCounter
open scoped Fin.CommRing Classical

variable {base R n m H w : ℕ} {x : Fin 2 → Fin R → Fin m → Bool}
variable {st : VisitState n m H} {mem : Memory w}

theorem probes_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

theorem leafLines_valid (hr : Holds base x st mem) (g : Fin 2) (s : Fin R)
    (state : Word w) (regs : Regs w 16) (h : Fin H) (j : Fin m)
    (hh : regs 1 = (h.val : Word w)) (hj : regs 2 = (j.val : Word w))
    (hrow : regs 5 = (↑((g.val*R+s.val)*m) : Word w)) (hnew : j ∉ st.marked)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hw : 2 < 2^w)
    (hcount : st.counts (.inl (h,j,x g s j)) + 1 < 2^w) :
    let a : Label n m (Fin H) := .inl (h,j,x g s j)
    ∃ es rs m', trace (publicData w base R n m H) state leafLines regs mem = some (es,rs,m') ∧
      Holds base x {st with marked := insert j st.marked, counts := st.counts + Finsupp.single a 1} m' ∧
      countProbes es = 5 := by
  let pub := publicData w base R n m H
  let st₁ := {st with marked := insert j st.marked}
  let m₁ := store base mem (markCell j : Locations R n m H) 1
  let a : Label n m (Fin H) := .inl (h,j,x g s j)
  let ix := labelIndex n m H a
  have hzero : view base mem (markCell j : Locations R n m H) = 0 := by simp [hr.marked j, hnew]
  obtain ⟨es₀, rs₀, ht₀, hc₀⟩ := mark_cell mem state regs j hj hf hzero
  have h₁ : Holds base x st₁ m₁ := hr.mark j hf
  have hpos₁ : rs₀ 2 = regs 2 := trace_preserves (by decide) ht₀
  have hrow₁ : rs₀ 5 = regs 5 := trace_preserves (by decide) ht₀
  have hh₁ : rs₀ 1 = regs 1 := trace_preserves (by decide) ht₀
  obtain ⟨es₁, rs₁, ht₁, hv₁, hc₁⟩ := leafBit_cell h₁ g s j state rs₀ (hpos₁.trans hj) (hrow₁.trans hrow) hf hw
  have hpos₂ : rs₁ 2 = rs₀ 2 := trace_preserves (by decide) ht₁
  have hh₂ : rs₁ 1 = rs₀ 1 := trace_preserves (by decide) ht₁
  have hT : labelCount n m H ≤ 2^w := by unfold size at hf; omega
  obtain ⟨es₂, rs₂, ht₂, hc₂, _, he₂⟩ := terminalIndex_spec pub state rs₁ m₁ h j (x g s j)
    rfl (hh₂.trans (hh₁.trans hh)) (hpos₂.trans (hpos₁.trans hj)) hv₁ hT
  have hv : rs₂ 7 = (ix.val : Word w) := by
    change rs₂ 7 = (↑((labelIndex n m H (.inl (h,j,x g s j))).val) : Word w)
    rw [← he₂, Fin.cast_val_eq_self]
  have hinc : (view base m₁ (countCell ix : Locations R n m H)).val + 1 < 2^w :=
    (h₁.counts a) ▸ hcount
  obtain ⟨es₃, rs₃, ht₃, hc₃⟩ := increment_cell m₁ state rs₂ ix hv hf hinc
  refine ⟨((es₀ ++ es₁) ++ es₂) ++ es₃, rs₃, _, ?_, h₁.increment a hf hcount, ?_⟩
  · change trace pub state leafLines regs mem = _
    simp [leafLines, trace_append, ht₀, ht₁, ht₂, ht₃, pub, m₁]
    rfl
  · simp [probes_append, hc₀, hc₁, hc₂, hc₃]

theorem leafLines_outside (state : Word w) (regs : Regs w 16)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (ho : m ≤ (regs 2).val) :
    trace (publicData w base R n m H) state leafLines regs mem = none := by
  let pub := publicData w base R n m H
  have hm : m < 2^w := by unfold size at hf; omega
  have hg : ¬regs 2 < pub 6 := by
    change ¬(regs 2).val < (m : Word w).val
    simpa [Fin.val_natCast, Nat.mod_eq_of_lt hm] using Nat.not_lt.mpr ho
  have h := mark_reject pub state regs mem (Or.inl hg)
  change trace pub state leafLines regs mem = _
  rw [leafLines, trace_append, trace_append, trace_append, h]
  rfl

theorem leafLines_repeated (hr : Holds base x st mem) (state : Word w) (regs : Regs w 16) (j : Fin m)
    (hj : regs 2 = (j.val : Word w)) (hused : j ∈ st.marked)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hw : 2 < 2^w) :
    trace (publicData w base R n m H) state leafLines regs mem = none := by
  let pub := publicData w base R n m H
  have he : pub 2 + regs 2 = (address base (markCell j : Locations R n m H) : Word w) :=
    hj ▸ public_mark base j
  have hv : mem (pub 2 + regs 2).val ≠ 0 := by
    rw [he, Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf (markCell j))]
    change view base mem (markCell j : Locations R n m H) ≠ 0
    rw [hr.marked j, ite_eq_left hused]
    intro h
    have := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < 2^w)] at this
  have h := mark_reject pub state regs mem (Or.inr hv)
  change trace pub state leafLines regs mem = _
  rw [leafLines, trace_append, trace_append, trace_append, h]
  rfl

end PrimedStackRAM

end VPVNP
end Computability
end OAI
