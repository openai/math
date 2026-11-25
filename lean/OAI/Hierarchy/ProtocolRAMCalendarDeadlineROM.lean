import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Hierarchy.ProtocolRAMScalarROMTable
import OAI.Hierarchy.ProtocolRAMCalendarTime

namespace OAI
/-! # Scalar and score pages for every actual deadline in the finite mesh -/
namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

namespace DeadlineROM

def rows (c : Mesh) := c.inject+c.cool+1
def levels (c : Mesh) := c.reserveSteps+2
def count (c : Mesh) := rows c*levels c

def outerRow (c : Mesh) (p : ℕ) : Fin (rows c) :=
  ⟨p%rows c,Nat.mod_lt _ (Nat.succ_pos _)⟩

def innerLevel (c : Mesh) (j : ℕ) : Fin (levels c) :=
  ⟨j % (c.reserveSteps + 1) + 1, Nat.succ_lt_succ (Nat.mod_lt j (Nat.succ_pos c.reserveSteps))⟩

def index (c : Mesh) : Attempt→Fin (count c)
  | .outer p _ => finProdFinEquiv (outerRow c p,⟨0,Nat.succ_pos _⟩)
  | .inner p _ j _ => finProdFinEquiv (outerRow c p,innerLevel c j)

def prices (c : Mesh) (finish : ℝ) (base : PhasePrice) (i : Fin (count c)) : PhasePrice :=
  let a : Fin (rows c)×Fin (levels c) := finProdFinEquiv.symm i
  if a.2.val=0 then deadline c finish base (.outer a.1.val 0)
  else deadline c finish base (.inner a.1.val 0 (a.2.val-1) 0)

theorem outer_price (c : Mesh) (finish : ℝ) (base : PhasePrice) (p a : ℕ)
    (hp : p≤c.inject+c.cool) :
    prices c finish base (index c (.outer p a))=deadline c finish base (.outer p a) := by
  simp [prices,index,outerRow,Nat.mod_eq_of_lt (show p<rows c from Nat.lt_succ_of_le hp),deadline,time]

theorem inner_price (c : Mesh) (finish : ℝ) (base : PhasePrice) (p a j b : ℕ)
    (hp : p≤c.inject+c.cool) (hj : j≤c.reserveSteps) :
    prices c finish base (index c (.inner p a j b))=deadline c finish base (.inner p a j b) := by
  simp [prices,index,outerRow,innerLevel,Nat.mod_eq_of_lt (show p<rows c from Nat.lt_succ_of_le hp),
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hj),deadline,time]

def table (c : Mesh) (finish : ℝ) (base : PhasePrice) (start kinds stride : ℕ) : ScalarROM.Table (count c) :=
  ⟨start,kinds,stride,prices c finish base⟩

theorem read_outer {w : ℕ} (c : Mesh) (finish : ℝ) (base : PhasePrice) (start kinds stride p a : ℕ)
    (m : Memory w) (resident : (table c finish base start kinds stride).Resident m)
    (hp : p≤c.inject+c.cool) (i : Fin kinds) (val : Fin stride) :
    ((table c finish base start kinds stride).bank (index c (.outer p a))).read m
      ((i.val*stride+val.val:ℕ):Word w)=((deadline c finish base (.outer p a)).word i.val val.val:Word w) := by
  rw [←outer_price c finish base p a hp]
  exact resident _ i val

theorem read_inner {w : ℕ} (c : Mesh) (finish : ℝ) (base : PhasePrice) (start kinds stride p a j b : ℕ)
    (m : Memory w) (resident : (table c finish base start kinds stride).Resident m)
    (hp : p≤c.inject+c.cool) (hj : j≤c.reserveSteps) (i : Fin kinds) (val : Fin stride) :
    ((table c finish base start kinds stride).bank (index c (.inner p a j b))).read m
      ((i.val*stride+val.val:ℕ):Word w)=((deadline c finish base (.inner p a j b)).word i.val val.val:Word w) := by
  rw [←inner_price c finish base p a j b hp hj]
  exact resident _ i val

end DeadlineROM
end
end Hierarchy.ProtocolRAM.Calendar

end OAI
