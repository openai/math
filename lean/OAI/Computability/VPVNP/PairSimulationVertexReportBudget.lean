import OAI.Computability.VPVNP.PairTraversalTraffic
import OAI.Computability.VPVNP.PairTraversalCost
import OAI.Computability.VPVNP.CursorBranchCommunication

/-!
# Charging a final vertex's actual report against its transcript caps

The report starts with bootstrap and geometry, loads the final incident bits,
visits the stored DFS row and flushes the private histogram. The local calls
may use a bounded number of header scans per occurrence; this is the only
polylogarithmic factor in their external communication allowance.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexReportBudget

open NetworkKernel Compression BurstRAM CursorNetwork Filter

variable {A : Type*} {N : Network} {a g w : ℕ} (Y : State a g)
  (chain : TermChain A N Y.network) (v : Y.network.Site)

/-- `setup` bounds the geometry stage, `scan` bounds prologue and directory
traffic per occurrence, and `fields` and `maps` bound the actual probe costs
of field jobs and map-argument writers. All four constants are fixed. -/
def coefficient (degree labels setup scan fields maps : ℕ) : ℕ :=
  32 + 5 * degree + 2 * labels + setup + scan + fields + maps

/-- The report decomposition uses the real DFS visit proof and the actual
bit incidence at the chosen output position. A role-dispatch probe and
one original leaf header probe are both charged even when a leaf is a transit site. -/
theorem probes_le (n q degree labels setup scan fields maps : ℕ) (mem : Memory w)
    (root : Word w) (top : ℕ) (nodes : List (Word w)) (control : List (Event w))
    (visited : DFS.Visits mem top [root] nodes control)
    (hnodes : nodes.length ≤ chain.occurrences (fun _ ↦ 1) v)
    (geometry hook fieldReads mapReads : ℕ) (rep : Report w) (hgeom : geometry ≤ setup)
    (hfield : fieldReads ≤ chain.occurrences (fun _ ↦ 1) v * fields)
    (hmap : mapReads ≤ chain.occurrences (fun _ ↦ 1) v * maps)
    (hhook : hook ≤ 2 * nodes.length + fieldReads + mapReads +
      scan * (chain.occurrences (fun _ ↦ 1) v * (n.log2 + 1) ^ q))
    (hrep : rep.probes ≤ 9 + geometry + (5 * degree + incidentBits Y v) + countProbes control +
      hook + 2 * labels) :
    1 + rep.probes ≤
      siteAccesses Y chain (coefficient degree labels setup scan fields maps) q n v := by
  let o := chain.occurrences (fun _ ↦ 1) v
  let big := o * (n.log2 + 1) ^ q
  let den := 1 + incidentBits Y v + big
  let C := coefficient degree labels setup scan fields maps
  have h₁ : 1 ≤ (n.log2 + 1) ^ q := Nat.one_le_pow q _ (by omega)
  have hob : o ≤ big := Nat.le_mul_of_pos_right _ h₁
  have hd : big ≤ den := Nat.le_add_left ..
  have hi : incidentBits Y v ≤ den := by dsimp [den]; omega
  have hn : nodes.length ≤ den := hnodes.trans (hob.trans hd)
  have ho : o ≤ den := hob.trans hd
  have hc : countProbes control ≤ 3 * den := by
    have h := visited.cost.1
    have hmul := Nat.mul_le_mul_left 3 hn
    omega
  have hden : 1 ≤ den := by dsimp [den]; omega
  have hfix : 10 + setup + 5 * degree + 2 * labels ≤ (10 + setup + 5 * degree + 2 * labels) * den :=
    Nat.le_mul_of_pos_right _ hden
  have hf := hfield.trans ((Nat.mul_le_mul_right _ ho).trans_eq (Nat.mul_comm den fields))
  have hm := hmap.trans ((Nat.mul_le_mul_right _ ho).trans_eq (Nat.mul_comm den maps))
  have hs := Nat.mul_le_mul_left scan hd
  change hook ≤ 2 * nodes.length + fieldReads + mapReads + scan * big at hhook
  change 1 + rep.probes ≤ C * den
  dsimp [C, coefficient]
  ring_nf at hfix hf hm hs ⊢
  omega

set_option exponentiation.threshold 10000 in
-- This is the explicit live private exponent in Section 13.
/-- The native report contains the exact DFS control and local visit events.
The other terms count the bootstrap, final-bit gather, histogram and finish.
The 107-tick margin is available to the enclosing live call. -/
theorem steps_le_45 {n degree labels geometry hook : ℕ} (hn : 2048 ≤ n)
    (hdeg : degree ≤ n) (hlab : labels ≤ n) (hgeom : geometry ≤ n ^ 3)
    (hinc : incidentBits Y v ≤ 2 * degree * n) (hvisits : chain.occurrences (fun _ ↦ 1) v ≤ n)
    (mem : Memory w) (root : Word w) (top : ℕ) (nodes : List (Word w)) (control : List (Event w))
    (visited : DFS.Visits mem top [root] nodes control)
    (hnodes : nodes.length ≤ chain.occurrences (fun _ ↦ 1) v)
    (hhook : hook ≤ n ^ 44) (rep : Report w)
    (hrep : rep.events.length ≤ 44 + geometry + (15 + 21 * degree + 5 * incidentBits Y v) +
      control.length + hook + 7 * labels + 14) : rep.events.length + 107 ≤ n ^ 45 := by
  have h₁ : 1 ≤ n ^ 44 := Nat.one_le_pow _ _ (by omega)
  have hₙ : n ≤ n ^ 44 := Nat.le_self_pow (by decide) n
  have h₂ : n ^ 2 ≤ n ^ 44 := Nat.pow_le_pow_right (by omega) (by decide)
  have h₃ : n ^ 3 ≤ n ^ 44 := Nat.pow_le_pow_right (by omega) (by decide)
  have hi := hinc.trans (Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 hdeg))
  rw [show 2 * n * n = 2 * n ^ 2 by ring] at hi
  have hctrl := visited.cost.2
  have hnode := hnodes.trans hvisits
  have hfit : rep.events.length + 107 ≤ 300 * n ^ 44 := by omega
  have hwide : 300 * n ^ 44 ≤ n ^ 45 := by
    rw [pow_succ' n 44]; exact Nat.mul_le_mul_right _ (by omega)
  exact hfit.trans hwide

set_option exponentiation.threshold 10000 in
-- This is the explicit live private exponent in Section 13.
/-- Section 13's private clock follows from the stronger polynomial report bound. -/
theorem steps_le {n degree labels geometry hook : ℕ} (hn : 2048 ≤ n)
    (hdeg : degree ≤ n) (hlab : labels ≤ n) (hgeom : geometry ≤ n ^ 3)
    (hinc : incidentBits Y v ≤ 2 * degree * n) (hvisits : chain.occurrences (fun _ ↦ 1) v ≤ n)
    (mem : Memory w) (root : Word w) (top : ℕ) (nodes : List (Word w)) (control : List (Event w))
    (visited : DFS.Visits mem top [root] nodes control)
    (hnodes : nodes.length ≤ chain.occurrences (fun _ ↦ 1) v)
    (hhook : hook ≤ n ^ 44) (rep : Report w)
    (hrep : rep.events.length ≤ 44 + geometry + (15 + 21 * degree + 5 * incidentBits Y v) +
      control.length + hook + 7 * labels + 14) : rep.events.length + 107 ≤ n ^ 10000 := by
  exact (steps_le_45 Y chain v hn hdeg hlab hgeom hinc hvisits mem root top nodes control visited
    hnodes hhook rep hrep).trans (Nat.pow_le_pow_right (by omega) (by decide))

end PairSimulation.VertexReportBudget

end VPVNP
end Computability
end OAI
