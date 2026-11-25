import OAI.Computability.BorderVNP.RoutingISAOffsetMemory

/-! # Native cursor operations and the terminal store of an oriented leg -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {l : TableLayout} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

private theorem ready_update (st : NatState) (hd : l.ready st) {d : Reg} (h : 12 < d.val)
    (v : ℕ) (mem : ℕ → ℕ) : l.ready ⟨Function.update st.reg d v, mem⟩ := by
  intro j hj
  have hne : j ≠ d := fun he => by subst j; omega
  exact (Function.update_of_ne hne ..).trans (hd j hj)

/-- Reset a loop cursor using the protected zero register. -/
theorem reset_cursor (d : Reg) (hd : 12 < d.val) (s : Bank w) (m : Memory w)
    (h : l.ready (.ofWords s m)) :
    BoundedRun pub macros (.copy d 0) s m 1 (fun z =>
      l.ready z ∧ z.reg d = 0 ∧ (∀ i, i ≠ d → z.reg i = (readings s) i) ∧ z.mem = readings m) := by
  let st := NatState.ofWords s m
  have h₀ : st.reg 0 = 0 := h 0 (by decide)
  apply ((Code.copy d 0).runFixed pub macros s m trivial).mono le_rfl
  intro z hz
  rw [hz]
  exact ⟨ready_update st h hd _ _, (Function.update_self ..).trans h₀,
    fun i hi => Function.update_of_ne hi .., rfl⟩

/-- Increment a loop cursor using the protected one register. -/
theorem advance_cursor (d : Reg) (hd : 12 < d.val) (s : Bank w) (m : Memory w) (i : ℕ)
    (h : l.ready (.ofWords s m)) (hi : (readings s) d = i) (hfit : i+1 < 2^w) :
    BoundedRun pub macros (.binary .add d d 1) s m 1 (fun z =>
      l.ready z ∧ z.reg d = i+1 ∧ (∀ j, j ≠ d → z.reg j = (readings s) j) ∧ z.mem = readings m) := by
  let st := NatState.ofWords s m
  have h₁ : st.reg 1 = 1 := h 1 (by decide)
  have hreg : st.reg d = i := hi
  have val : addressOp .add (st.reg d) (st.reg 1) = i+1 := by rw [hreg,h₁]; rfl
  have safe : (Code.binary .add d d 1).fixedSafe w (readings pub) st := by
    change st.reg d + st.reg 1 < 2^w
    simpa only [hreg,h₁] using hfit
  apply ((Code.binary .add d d 1).runFixed pub macros s m safe).mono le_rfl
  intro z hz
  rw [hz]
  exact ⟨ready_update st h hd _ _, (Function.update_self ..).trans val,
    fun j hj => Function.update_of_ne hj .., rfl⟩

/-- Compute the pair address, write the terminal prefix, and advance the relay cursor. -/
def legTail : Code := .block [pairAddress 25 21 22 3 10, .store 25 20, .binary .add 22 22 1]

/-- The terminal pair store of one complete partner scan. -/
theorem legTail_image (s : Bank w) (m : Memory w) {u v sum : ℕ}
    (h : l.ready (.ofWords s m)) (alloc : l.Allocated w) (hu : u < l.teams) (hv : v < l.teams)
    (h21 : (readings s) 21 = u) (h22 : (readings s) 22 = v) (h20 : (readings s) 20 = sum) :
    BoundedRun pub macros legTail s m legTail.slots (fun z =>
      l.ready z ∧ z.reg 21 = u ∧ z.reg 22 = v+1 ∧
        z.mem = Function.update (readings m) (pairIndex l.used l.teams u v) sum) := by
  let st := NatState.ofWords s m
  have h3 : st.reg 3 = l.teams := h 3 (by decide)
  have h10 : st.reg 10 = l.used := h 10 (by decide)
  have h1 : st.reg 1 = 1 := h 1 (by decide)
  have h₂₁ : st.reg 21 = u := h21
  have h₂₂ : st.reg 22 = v := h22
  have h₂₀ : st.reg 20 = sum := h20
  have hp := alloc.address (used_contains hu hv)
  change u*l.teams+v+l.used < 2^w at hp
  have hs : v+1 < 2^w := (show v+1 ≤ l.teams from hv).trans_lt alloc.teamsFit
  have safe : legTail.fixedSafe w (readings pub) st := by
    simp (config := {decide := true}) [legTail, Code.block, pairAddress, Code.fixedSafe,
      Code.fixedEval, Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp,
      h₂₁,h₂₂,h3,h10,h1]
    omega
  apply (legTail.runFixed pub macros s m safe).mono le_rfl
  intro z hz
  rw [hz]
  constructor
  · intro j hj
    have h₂₅ : j ≠ 25 := fun he => by subst j; norm_num at hj
    have h₂₂' : j ≠ 22 := fun he => by subst j; norm_num at hj
    simpa (config := {decide := true}) only [legTail, Code.block, pairAddress, Code.fixedEval, Code.evalNat,
      Function.update_of_ne h₂₅, Function.update_of_ne h₂₂'] using h j hj
  · change (legTail.fixedEval (readings pub) st).reg 21 = _ ∧
      (legTail.fixedEval (readings pub) st).reg 22 = _ ∧ (legTail.fixedEval (readings pub) st).mem = _
    simp (config := {decide := true}) [legTail, Code.block, pairAddress, pairIndex, Code.fixedEval,
      Code.evalNat, addressOp, h₂₁,h₂₂,h₂₀,h3,h10,h1,st]
    rfl

end RoutingISA

end BorderVNP
end Computability
end OAI
