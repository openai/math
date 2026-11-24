import OAI.Computability.VPVNP.PairSimulationEndpointBits
import OAI.Computability.VPVNP.PairSimulationCounters
import OAI.Computability.VPVNP.CursorBranchCommunication

/-!
# Native traffic for the shared bits and final history visits

The final-arc writer, the two incidence readers, the DFS control code,
and the component-counter updates have concrete reports. Their costs
are compared here with the same selected branch used in the energy
estimate. A descriptor address and an empty field each retain their
own native loop tests.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM BurstRAM.PrivateRAM Compression NetworkKernel CursorNetwork

variable {a g w : ℕ}

/-- All final incidence read events of one vertex, in outgoing then
incoming slot order. -/
def incidenceEvents (Y : State a g) (v : Y.network.Site) (mem : Memory w)
    (src : Bool → Fin (2 ^ a) → ℕ) : List (Event w) :=
  (List.ofFn fun j => EndpointBits.events mem (src false j) (Y.halfWidth v false j)).flatten ++
    (List.ofFn fun j => EndpointBits.events mem (src true j) (Y.halfWidth v true j)).flatten

private theorem append_probes (xs ys : List (Event w)) :
    countProbes (xs ++ ys) = countProbes xs + countProbes ys := by
  induction xs with
  | nil => simp [countProbes]
  | cons x xs ih => cases x <;> simp [countProbes, ih, Nat.add_comm, Nat.add_left_comm]

private theorem ofFn_probes {n : ℕ} (f : Fin n → List (Event w)) :
    countProbes (List.ofFn f).flatten = ∑ i, countProbes (f i) := by
  induction n with
  | zero => simp [countProbes]
  | succ n ih => rw [List.ofFn_succ, List.flatten_cons, append_probes, Fin.sum_univ_succ, ih]

theorem incidenceEvents_probes (Y : State a g) (v : Y.network.Site) (mem : Memory w)
    (src : Bool → Fin (2 ^ a) → ℕ) :
    countProbes (incidenceEvents Y v mem src) = CursorNetwork.incidentBits Y v := by
  simp only [incidenceEvents, append_probes, ofFn_probes, EndpointBits.probes,
    CursorNetwork.incidentBits, Fintype.sum_bool]
  omega

theorem incidenceEvents_length (Y : State a g) (v : Y.network.Site) (mem : Memory w)
    (src : Bool → Fin (2 ^ a) → ℕ) :
    (incidenceEvents Y v mem src).length = 5 * CursorNetwork.incidentBits Y v + 2 * 2 ^ a := by
  have len (s n : ℕ) : (EndpointBits.events mem s n).length = 5*n+1 := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih => simp [EndpointBits.events, ih]; omega
  simp only [incidenceEvents, List.length_append, List.length_flatten, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, len, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    CursorNetwork.incidentBits, Fintype.sum_bool]
  norm_cast
  ring

/-- Native logs of the endpoint reads, ordered DFS control and fixed
componentwise flush. Other private computations occur at the DFS hook. -/
def finalControlEvents (Y : State a g) (v : Y.network.Site) (m : Memory w)
    (src : Bool → Fin (2 ^ a) → ℕ) (dfsLog : List (Event w))
    (priv : Word w → Word w) (privateBase counterBase labels : ℕ) : List (Event w) :=
  incidenceEvents Y v m src ++ dfsLog ++ Counters.events priv m privateBase counterBase labels

theorem finalControlEvents_cost (Y : State a g) (v : Y.network.Site) (m : Memory w)
    (src : Bool → Fin (2 ^ a) → ℕ) (dfsLog : List (Event w))
    (priv : Word w → Word w) (privateBase counterBase labels : ℕ) :
    let es := finalControlEvents Y v m src dfsLog priv privateBase counterBase labels
    countProbes es = CursorNetwork.incidentBits Y v + countProbes dfsLog + 2 * labels ∧
      es.length =
        5 * CursorNetwork.incidentBits Y v + 2 * 2 ^ a + dfsLog.length + 7 * labels + 1 := by
  simp only [finalControlEvents, append_probes, incidenceEvents_probes, List.length_append,
    incidenceEvents_length, (Counters.events_cost priv m privateBase counterBase labels).1,
    (Counters.events_cost priv m privateBase counterBase labels).2.1, Nat.add_assoc, and_self]

/-- Count the startup of each final burst, its actual control log, and
every binary write in the genuine final-bit writer's reports. -/
theorem finalControl_cost_le {A : Type*} {a₀ g₀ : ℕ}
    (X : State a₀ g₀) (Y : State a g) (chain : TermChain A X.network Y.network)
    (n labels : ℕ) (m : Memory w) (src : Y.network.Site → Bool → Fin (2 ^ a) → ℕ)
    (logs : Y.network.Site → List (Event w))
    (hdfs : ∀ v, countProbes (logs v) ≤ 3 * chain.occurrences (fun _ => 1) v)
    (priv : Y.network.Site → Word w → Word w) (privateBase counterBase low : ℕ)
    (bits : Fin Y.totalWidth → Bool) :
    let C := 2 * labels + 4
    let charge v := 1 + countProbes
      (finalControlEvents Y v m (src v) (logs v) (priv v) privateBase counterBase labels)
    (∀ v, charge v ≤ siteAccesses Y chain C 0 n v) ∧
      RAMBuckets.cost Report.probes (FinalBits.reports w low bits) + ∑ v, charge v ≤
        branchAccesses X Y chain C 0 n := by
  intro C charge
  have hc v : charge v ≤ siteAccesses Y chain C 0 n v := by
    dsimp only [charge, C, siteAccesses, pow_zero, Nat.mul_one]
    rw [(finalControlEvents_cost ..).1]
    have h := hdfs v
    nlinarith only [h, Nat.zero_le (CursorNetwork.incidentBits Y v),
      Nat.zero_le (labels * CursorNetwork.incidentBits Y v),
      Nat.zero_le (labels * chain.occurrences (fun _ => 1) v)]
  refine ⟨hc, ?_⟩
  rw [(FinalBits.scan_cost low Y.totalWidth bits).2]
  apply Nat.add_le_add _ (Finset.sum_le_sum fun v _ => hc v)
  simp only [pow_zero, Nat.mul_one]
  dsimp [C]
  nlinarith only [Nat.zero_le (labels * X.positions), Nat.zero_le (labels * Y.totalWidth)]

end PairSimulation

end VPVNP
end Computability
end OAI
