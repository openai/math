import OAI.Computability.VPVNP.PairSimulationStackSpace
import OAI.Computability.VPVNP.PairNodeArguments

/-! # Private addresses of the cursor-leaf verifier -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafArena

open NodeArguments StackMachine Filter BurstRAM

/-- The node arguments occupy their full stride even at the last genuine
descriptor. The histogram and further reserved scratch precede the cache
of 38 virtual operands. Each verifier stack starts beyond the entire cache. -/
structure Regions where
  /-- The start and stride of the private argument frames indexed by descriptor node addresses. -/
  arguments : Arena
  /-- Exclusive upper bound on node indices with reserved argument frames. -/
  nodes : ℕ
  /-- Number of private words reserved for the histogram immediately after the node frames. -/
  histWords : ℕ
  /-- Number of additional scratch words reserved between the histogram and the operand cache. -/
  otherWords : ℕ

/-- First private histogram address, immediately following the last reserved node frame. -/
def Regions.histBase (R : Regions) := R.arguments.base R.nodes
/-- First private address for the cached auxiliary operands, after the histogram and its
neighboring scratch interval. -/
def Regions.cacheBase (R : Regions) := R.histBase + R.histWords + R.otherWords
/-- First available private address for verifier stacks, immediately after the 38 cached
operand words. -/
def Regions.stackBase (R : Regions) := R.cacheBase + 38

theorem Regions.node_before {R : Regions} {node : ℕ} (h : node < R.nodes) :
    R.arguments.base node + R.arguments.stride ≤ R.histBase := R.arguments.before h

theorem Regions.hist_before (R : Regions) : R.histBase + R.histWords ≤ R.cacheBase :=
  Nat.le_add_right _ _

theorem Regions.cache_before (R : Regions) (i : Fin 38) : R.cacheBase + i.val < R.stackBase := by
  unfold stackBase; omega

/-- Consecutive pointer slots of the actual virtual verifier's named-port
table. All address widths and counts are runtime parameters. -/
def Regions.layout {w ports : ℕ} {K : Type} (R : Regions) (order : K ↪ Fin ports) (capacity : ℕ)
    (fits : R.stackBase + ports*capacity < 2^w) : Layout K w :=
  Layout.consecutive order R.stackBase capacity fits

theorem Regions.stack_above {w ports : ℕ} {K : Type} (R : Regions) (order : K ↪ Fin ports)
    (capacity : ℕ) (fits : R.stackBase + ports*capacity < 2^w) (j : K) :
    R.stackBase ≤ (R.layout order capacity fits).base j := Nat.le_add_right _ _

theorem Regions.stack_above_dfs {w ports endAddr : ℕ} {K : Type} (R : Regions) (order : K ↪ Fin ports)
    (capacity : ℕ) (fits : R.stackBase + ports*capacity < 2^w) (before : endAddr ≤ R.arguments.start)
    (j : K) : endAddr ≤ (R.layout order capacity fits).base j := by
  apply (le_trans _ (R.stack_above order capacity fits j))
  unfold Regions.stackBase Regions.cacheBase Regions.histBase Arena.base
  omega

/-- Any fixed polynomial bound on the public descriptor addresses and
stride gives a single threshold for the histogram, the operand cache,
and all stacks with their verified capacity `n^40`. -/
theorem eventually_fit {B : ℕ} (hB : 1 ≤ B) (ports offsetExp nodeExp strideExp histExp otherExp : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ R : Regions, R.arguments.start ≤ n^offsetExp → R.nodes ≤ n^nodeExp →
      R.arguments.stride ≤ n^strideExp → R.histWords ≤ n^histExp → R.otherWords ≤ n^otherExp →
      R.stackBase + ports*n^40 < 2^CursorBounds.wordBits B n := by
  let e := max offsetExp (max (nodeExp+strideExp) (max histExp otherExp))
  filter_upwards [eventually_ge_atTop 42,eventually_port_space hB ports (e+1) 40] with n hn space
  intro R hs hnodes hstride hh ho
  have hn₁ : 1 ≤ n := by omega
  have mono {i : ℕ} (h : i ≤ e) := Nat.pow_le_pow_right hn₁ h
  have start := hs.trans (mono (le_max_left ..))
  have prod : R.nodes*R.arguments.stride ≤ n^e := calc
    _ ≤ n^nodeExp*n^strideExp := Nat.mul_le_mul hnodes hstride
    _ = n^(nodeExp+strideExp) := (Nat.pow_add ..).symm
    _ ≤ _ := mono ((le_max_left ..).trans (le_max_right ..))
  have hH := hh.trans (mono ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))))
  have hO := ho.trans (mono ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))))
  apply space R.stackBase (n^40) _ le_rfl
  unfold Regions.stackBase Regions.cacheBase Regions.histBase Arena.base
  have hp := Nat.one_le_pow e n hn₁
  have hb : 42*n^e ≤ n^(e+1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ hn
  omega

end PairSimulation.LeafArena

end VPVNP
end Computability
end OAI
