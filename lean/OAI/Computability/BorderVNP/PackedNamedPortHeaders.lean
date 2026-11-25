import OAI.Computability.BorderVNP.PackedInheritedWorkPortPath
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows
import OAI.Computability.BorderVNP.DiagonalEnrichedOriginalRowOuter

/-! # Grouped exterior-port headers in the named replay

The private program uses the nested public port injection at each combining
stage. Its numerical header is the work-width compiler's static port path.
The formulas below connect the exact same public names to the original
port row and the successive site-rectangle offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Shortening.Adaptive Diagonal.ExternalSew.RowTrace
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open scoped Classical

variable {P : Type} {np : ℕ} (p : Ports np) (leaf : P ↪ Fin np) (k : ℕ) (V : ℕ → ℕ)

/-- The stage's grouped headers indexed by the very same copy-and-port
rectangle used to replay the persistent site programs. -/
def Ports.nested {np : ℕ} (p : Ports np) (k : ℕ) (V : ℕ → ℕ) : (j : ℕ) → Ports (Parallel.nestedCapacity k np j)
  | 0 => p
  | j+1 => (p.nested k V j).parallel k (V j)

/-- The work compiler and the private tape emitter enumerate identical slots. -/
theorem Ports.nested_table (j : ℕ) :
    (PortTable.mk np leaf p).path k V j =
      ⟨Parallel.nestedCapacity k np j,Parallel.nestedPorts k leaf j,p.nested k V j⟩ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [PortTable.path,ih]; rfl

/-- One actual attachment pointer, expressed solely in terms of its original
group and the rectangle displacements along its copy address. -/
theorem Ports.nested_host (j : ℕ) (z : Port k P j) :
    (p.nested k V j).host (Parallel.nestedPorts k leaf j z) =
      flatOffset (fun i a => a.val*V i) j (portEquiv k P j z).1 + p.host (leaf (portEquiv k P j z).2) := by
  induction j with
  | zero => exact (Nat.zero_add _).symm
  | succ j ih =>
    rcases z with ⟨a,z⟩
    have pair := finProdFinEquiv.symm_apply_apply (a,Parallel.nestedPorts k leaf j z)
    rw [portEquiv_succ,flatOffset_succ]
    change (finProdFinEquiv.symm (finProdFinEquiv (a,Parallel.nestedPorts k leaf j z))).1.val * V j +
      (p.nested k V j).host (finProdFinEquiv.symm (finProdFinEquiv (a,Parallel.nestedPorts k leaf j z))).2 = _
    rw [pair,ih,Nat.add_assoc]

/-- The occupied port widths, hole widths and width-word fits all propagate
through a path of the actual nested private-program rows. -/
theorem Ports.nested_widths {bits : P → ℕ} {w : ℕ}
    (small : (PortTable.mk np leaf p).Widths bits w) (j : ℕ) :
    (PortTable.mk _ (Parallel.nestedPorts k leaf j) (p.nested k V j)).Widths (Shortening.Adaptive.width bits k j) w := by
  rw [← p.nested_table leaf k V]
  exact small.path k V j

/-- There is one header per grouped argument slot in each leaf. -/
theorem nested_count (k np j : ℕ) : Parallel.nestedCapacity k np j = k^j*np := by
  induction j with
  | zero => simp [Parallel.nestedCapacity]
  | succ j ih => rw [Parallel.nestedCapacity,ih,pow_succ]; ac_rfl

open Crossing Epoch Epoch.Round Cover Packing
open scoped BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
variable (S : SiteSchedule e) (start : ℕ)

/-- Grouped port header on the public boundary of each outer epoch. The
terminal flattening relabels ports, retaining their compiled numerical slots. -/
noncomputable def Ports.outer {np : ℕ} (p : Ports np) (S : SiteSchedule e) (start : ℕ) : (t : ℕ) → Ports (SelectedSchedule.portCapacity S np t)
  | 0 => p
  | t+1 => (p.outer S start t).nested S.fanIn (fun j => (SelectedSchedule.before S start t j).sites) S.rounds

/-- Physical row of an original argument at the outer boundary. -/
theorem Ports.outer_host (t : ℕ) (z : Port (fan S) P t) :
    (p.outer S start t).host (SelectedSchedule.privatePorts S leaf t z) =
      flatOffset (compiledOffset S start) t (portEquiv (fan S) P t z).1 +
        p.host (leaf (portEquiv (fan S) P t z).2) := by
  induction t with
  | zero => exact (Nat.zero_add _).symm
  | succ t ih =>
    rcases z with ⟨i,z⟩
    let pr := SelectedSchedule.privatePorts S leaf t
    let a := (portEquiv S.fanIn (Port (fan S) P t) S.rounds).symm (i,z)
    have ha := (portEquiv S.fanIn (Port (fan S) P t) S.rounds).apply_symm_apply (i,z)
    have h := (p.outer S start t).nested_host pr S.fanIn
      (fun j => (SelectedSchedule.before S start t j).sites) S.rounds a
    rw [show portEquiv S.fanIn (Port (fan S) P t) S.rounds a = (i,z) from ha] at h
    rw [portEquiv_succ,flatOffset_succ]
    exact h.trans ((congrArg (compiledOffset S start t i + ·) (ih z)).trans (Nat.add_assoc ..).symm)

/-- Complete width receipt at every outer boundary. -/
theorem Ports.outer_widths {bits : P → ℕ} {w : ℕ}
    (small : (PortTable.mk np leaf p).Widths bits w) (t : ℕ) :
    (PortTable.mk _ (SelectedSchedule.privatePorts S leaf t) (p.outer S start t)).Widths (Shortening.Adaptive.width bits (fan S) t) w := by
  induction t with
  | zero => exact small
  | succ t ih =>
    exact ((p.outer S start t).nested_widths (SelectedSchedule.privatePorts S leaf t) S.fanIn
      (fun j => (SelectedSchedule.before S start t j).sites) ih S.rounds).flatten

/-- Count grouped headers in an entire outer tree and an additional partial inner tree. -/
theorem path_count (t j : ℕ) :
    Parallel.nestedCapacity S.fanIn (SelectedSchedule.portCapacity S np t) j = S.fanIn^j * ((fan S)^t*np) := by
  have total (u : ℕ) : SelectedSchedule.portCapacity S np u = (fan S)^u*np := by
    induction u with
    | zero => simp [SelectedSchedule.portCapacity]
    | succ u ih => rw [SelectedSchedule.portCapacity,nested_count,ih,pow_succ]; dsimp only [fan]; ac_rfl
  rw [nested_count,total]

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
