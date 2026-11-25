import OAI.ThreeFlat.Diagonal.TraceUniformCost
import OAI.Computability.VPVNP.RAMLayout

namespace OAI
/-! # Arithmetic gate and port budgets of the physical verifier -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open TraceProgram

def canonicalCost (w p r : ℕ) := 4*(p*(8*((5+r)*((w+1)*10+2)+2)+2)+1)
def firstCost (w p r : ℕ) := 4*(p*(10*w+1+((r+4)*((w+1)*10+2)+6)+2)+1)
def terminalCost (q w : ℕ) := 4*((q+1)*(34*(w+1)+4))

def checkCost (q w p r k d : ℕ) :=
  44000*(d+2)^2*(w+2)^2 + canonicalCost w p r + uniformBudget w p r k + firstCost w p r +
    terminalCost q w + 4*(p*(10*w+2)+1) + 36

end ThreeFlat.Diagonal.TraceUniformRow

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP TraceProgram TracePair TraceIssue

def packetBound (q w p r k d : ℕ) :=
  TraceUniformRow.checkCost q w p r k d + 90000*(d+2)^2*(w+2)^2 + 100

def cellsBound (q w p r k d : ℕ) :=
  ((1+2*(3+(q+1)))+(1+(1+6*p+k)*w*2))*(packetBound q w p r k d+1)

/-- All port names are local. Even the manually enumerated control values
have a polynomial-size index table and need no row-indexed lookup ROM. -/
def portCount (w p r k d : ℕ) :=
  (3*((5+r)*(w+1)) + (2*w + (RAMLayout.layerCount d*(2*(2*(7*(w+1)))) + 2*(7*(w+1))))) +
    (2*((1+6*p+k)*w)) +
    ((2*(2+2*(w+1)) + ((d+2)*2+1)) + (2+(2+(2+(1+6*p+k)*w))))

/-- A univariate row bound when the finite interpreter capacities and field
alphabet are all bounded by N. The degree and coefficient are absolute. -/
theorem cellsBound_of_le {q w p r k d N : ℕ} (hq : q ≤ N) (hw : w ≤ N) (hp : p ≤ N)
    (hr : r ≤ N) (hk : k ≤ N) (hd : d ≤ N) :
    cellsBound q w p r k d ≤ 10^26*(N+1)^14 := by
  let D (q w p r k d : ℕ) := cellsBound q w p r k d
  have hm : D q w p r k d ≤ D N N N N N N := by
    simp only [D,cellsBound,packetBound,TraceUniformRow.checkCost,TraceUniformRow.canonicalCost,
      TraceUniformRow.firstCost,TraceUniformRow.terminalCost,uniformBudget,pinBudget,shapeBudget,portBudget,
      controlBudget,slotBudget,instructionBudget_poly]
    gcongr
  apply hm.trans
  simp only [D,cellsBound,packetBound,TraceUniformRow.checkCost,TraceUniformRow.canonicalCost,
    TraceUniformRow.firstCost,TraceUniformRow.terminalCost,uniformBudget,pinBudget,shapeBudget,portBudget,
    controlBudget,slotBudget,instructionBudget_poly]
  ring_nf
  omega

theorem portCount_of_le {w p r k d N : ℕ} (hw : w ≤ N) (hp : p ≤ N) (hr : r ≤ N)
    (hk : k ≤ N) (hd : d ≤ N) :
    portCount w p r k d ≤ 400*(N+2)^3 := by
  have hl : RAMLayout.layerCount d ≤ (N+1)^2 := by
    rw [RAMLayout.layerCount,Nat.choose_two_right]
    apply (Nat.div_le_self _ _).trans
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  unfold portCount
  calc
    _ ≤ (3*((5+N)*(N+1)) + (2*N + ((N+1)^2*(2*(2*(7*(N+1)))) + 2*(7*(N+1))))) +
        (2*((1+6*N+N)*N)) +
        ((2*(2+2*(N+1)) + ((N+2)*2+1)) + (2+(2+(2+(1+6*N+N)*N)))) := by gcongr
    _ ≤ _ := by ring_nf; omega

/-- At physical word width 16u¹⁰, the gate table has degree at most 140
in u, with an absolute coefficient. Each of the three finite instruction
capacities is exactly u. -/
theorem diagonal_cells_bound {u q d : ℕ} (hu : 128 ≤ u) (hq : q ≤ u) (hd : d ≤ 15*u^10) :
    cellsBound q (16*u^10) u u u d ≤ (10^26*17^14)*u^140 := by
  have h10 := Nat.le_self_pow (by decide : 10 ≠ 0) u
  have h : u ≤ 16*u^10 := by omega
  have ht : 16*u^10+1 ≤ 17*u^10 := by omega
  exact (cellsBound_of_le (hq.trans h) le_rfl h h h (by omega)).trans <| calc
    _ ≤ 10^26*(17*u^10)^14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht _)
    _ = _ := by ring

/-- Each row's affine address ROM has degree at most 30 in u. -/
theorem diagonal_ports_bound {u d : ℕ} (hu : 128 ≤ u) (hd : d ≤ 15*u^10) :
    portCount (16*u^10) u u u d ≤ (400*18^3)*u^30 := by
  have h10 := Nat.le_self_pow (by decide : 10 ≠ 0) u
  have h : u ≤ 16*u^10 := by omega
  have ht : 16*u^10+2 ≤ 18*u^10 := by omega
  exact (portCount_of_le le_rfl h h h (by omega)).trans <| calc
    _ ≤ 400*(18*u^10)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht _)
    _ = _ := by ring

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
