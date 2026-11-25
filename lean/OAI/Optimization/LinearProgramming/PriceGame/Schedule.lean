import OAI.Optimization.LinearProgramming.PriceGame.Computation
import OAI.Optimization.LinearProgramming.PriceGame.Experts
import OAI.Optimization.LinearProgramming.PriceGame.FixedShare
import OAI.Optimization.LinearProgramming.PriceGame.Majority

/-! Executable outer fixed-share schedule. Every trial uses the retained probe history and
the weights and expert identifiers produced by the preceding trial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

open Finset

structure Population (N : ℕ) where
  experts : List (Expert N)
  weights : Vector ℚ experts.length
  nonnegative : ∀ i : Fin experts.length, 0 ≤ weights[i]
  probes : List (Probe N)

structure RoundResult (N : ℕ) where
  prices : Fin N → ℚ
  scores : ℕ → ℕ
  observations : List (Probe N)

namespace Population

variable {N : ℕ}

def ids (p : Population N) : Finset ℕ := range p.experts.length

/-- Numeric IDs outside a materialized weight vector have weight zero. -/
def lookup {n : ℕ} (v : Vector ℚ n) (j : ℕ) : ℚ :=
  if h : j < n then v[j] else 0

def weight (p : Population N) : ℕ → ℚ := lookup p.weights

def start (candidates : List (Probe N) → List (Expert N)) : Population N :=
  let first := candidates []
  ⟨first, Vector.replicate first.length (first.length : ℚ)⁻¹, by
    intro i
    simp [inv_nonneg], []⟩

theorem start_weight (candidates : List (Probe N) → List (Expert N)) :
    (start candidates).weight = initialWeight (start candidates).ids := by
  funext j
  simp [weight, lookup, start, ids, initialWeight]

def scaled (p : Population N) (out : RoundResult N) : Vector ℚ p.experts.length :=
  Vector.ofFn fun e : Fin p.experts.length => 2 ^ out.scores e * p.weights[e]

theorem lookup_scaled (p : Population N) (out : RoundResult N) (j : ℕ) :
    lookup (p.scaled out) j = scaledWeight p.ids p.weight out.scores j := by
  by_cases h : j < p.experts.length <;> simp [lookup, scaledWeight, ids, scaled, weight, h]

/-- Materialize the scaled weight vector and its total once, then build all next weights.
The preceding generation is never recomputed when a later trial looks up an expert. -/
def advanceVector (p : Population N) (out : RoundResult N) (size : ℕ) : Vector ℚ size :=
  let v := p.scaled out
  let total := ∑ j ∈ range size, lookup v j
  let share := ((1/64 : ℚ) / size) * total
  Vector.ofFn fun i : Fin size => (1 - 1/64) * lookup v i + share

theorem advanceVector_eq (p : Population N) (out : RoundResult N) (size i : ℕ) :
    lookup (p.advanceVector out size) i = rootUpdate p.ids (range size) p.weight out.scores i := by
  by_cases hi : i < size
  · simp [lookup, advanceVector, rootUpdate, fixedShare, hi, ← lookup_scaled]
  · simp [lookup, rootUpdate, fixedShare, hi]

theorem advanceVector_nonneg (p : Population N) (out : RoundResult N) (size : ℕ)
    (i : Fin size) : 0 ≤ (p.advanceVector out size)[i] := by
  have hs (j : ℕ) : 0 ≤ lookup (p.scaled out) j := by
    by_cases h : j < p.experts.length
    · simp only [lookup, h, dite_true, scaled, Vector.getElem_ofFn]
      exact mul_nonneg (by positivity) (p.nonnegative ⟨j,h⟩)
    · simp [lookup,h]
  have hval : (p.advanceVector out size)[i] = rootUpdate p.ids (range size) p.weight out.scores i :=
    by simpa [lookup, i.isLt] using p.advanceVector_eq out size i.val
  rw [hval, rootUpdate, fixedShare, ite_eq_left (mem_range.mpr i.isLt)]
  have hz (j : ℕ) : 0 ≤ scaledWeight p.ids p.weight out.scores j := by
    rw [← p.lookup_scaled out j]
    exact hs j
  exact add_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 1-1/64) (hz i))
    (mul_nonneg (by positivity) (sum_nonneg (fun j _ => hz j)))

/-- The new expert IDs are appended without reusing the identifiers of old experts. -/
def advance (candidates : List (Probe N) → List (Expert N)) (p : Population N) (result : RoundResult N) :
    Population N :=
  let history := p.probes ++ result.observations
  let experts := p.experts ++ candidates history
  ⟨experts, p.advanceVector result experts.length, p.advanceVector_nonneg result experts.length, history⟩

theorem advance_weight (candidates : List (Probe N) → List (Expert N))
    (p : Population N) (out : RoundResult N) :
    (advance candidates p out).weight = rootUpdate p.ids (advance candidates p out).ids p.weight out.scores :=
  funext (p.advanceVector_eq out _)

theorem ids_advance (candidates : List (Probe N) → List (Expert N)) (p : Population N)
    (out : RoundResult N) : p.ids ⊆ (advance candidates p out).ids := by
  intro i hi
  simpa [ids, advance] using Nat.lt_of_lt_of_le (Finset.mem_range.mp hi)
    (Nat.le_add_right p.experts.length (candidates (p.probes ++ out.observations)).length)

theorem advance_preserves_weight (candidates : List (Probe N) → List (Expert N))
    (p : Population N) (out : RoundResult N) :
    ∑ i ∈ (advance candidates p out).ids, (advance candidates p out).weight i =
      ∑ i ∈ p.ids, 2 ^ out.scores i * p.weight i :=
  by
  rw [advance_weight]
  exact sum_rootUpdate _ _ (ids_advance candidates p out) _ _

theorem start_weight_total (candidates : List (Probe N) → List (Expert N))
    (h : (candidates []).length ≠ 0) :
    ∑ e ∈ (start candidates).ids, (start candidates).weight e = 1 :=
  by
  rw [start_weight]
  exact sum_initialWeight _ ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero h)⟩

end Population

section Schedule

variable {N R : ℕ} {anchor : Fin N}
variable (candidates : List (Probe N) → List (Expert N))
variable (trial : Population N → Computation N (RoundResult N))

/-- The entire sequence, as rational trial outputs. The result type carries its exact length. -/
def trialLoop : (T : ℕ) → Population N → Computation N (Fin T → RoundResult N)
  | 0, _ => .pure Fin.elim0
  | t + 1, p => (trial p).bind fun out =>
      (trialLoop t (p.advance candidates out)).map (fun tail => Fin.cons (α := fun _ : Fin (t+1) => RoundResult N) out tail)

/-- Each logged trial was actually executed with the predecessor's own history and weights. -/
def ValidRun (h : Hidden N R anchor) : (T : ℕ) → Population N → (Fin T → RoundResult N) → Prop
  | 0, _, _ => True
  | t + 1, p, out =>
    Computation.Reaches h (trial p) (out 0) ∧
      ValidRun h t (p.advance candidates (out 0)) (Fin.tail out)

theorem reaches_trialLoop_iff (h : Hidden N R anchor) (T : ℕ) (p : Population N)
    (out : Fin T → RoundResult N) :
    Computation.Reaches h (trialLoop candidates trial T p) out ↔
      ValidRun candidates trial h T p out := by
  induction T generalizing p with
  | zero =>
    constructor
    · intro _; exact True.intro
    · intro _
      have h0 : out = Fin.elim0 := funext fun i => i.elim0
      rw [h0]
      exact .pure _
  | succ t ih =>
    rw [trialLoop, Computation.reaches_bind_iff]
    constructor
    · rintro ⟨a, ha, rest⟩
      obtain ⟨tail, htail, rfl⟩ := (Computation.reaches_map_iff ..).mp rest
      simp only [ValidRun, Fin.cons_zero, Fin.tail_cons]
      exact ⟨ha, (ih _ _).mp htail⟩
    · rintro ⟨hhead, htail⟩
      refine ⟨out 0, hhead, (Computation.reaches_map_iff ..).mpr ?_⟩
      exact ⟨Fin.tail out, (ih _ _).mpr htail, Fin.cons_self_tail out⟩

theorem trialLoop_height (K : ℕ) (hcost : ∀ p, (trial p).height ≤ K)
    (T : ℕ) (p : Population N) : (trialLoop candidates trial T p).height ≤ T * K := by
  induction T generalizing p with
  | zero => simp [trialLoop, Computation.height]
  | succ t ih =>
    simp only [trialLoop]
    apply le_trans (Computation.height_bind_le _ _ (t*K) (fun a => by
      rw [Computation.height_map]
      exact ih _))
    rw [Nat.succ_mul]
    have := hcost p
    omega

/-- Return the strict majority of signs of actual root prices at the supplied anchor. -/
def trialStrategy (T : ℕ) (anchor : Fin N) : Tree N :=
  ((trialLoop candidates trial T (Population.start candidates)).map
    (fun out => priceMajority (fun i => (out i).prices anchor))).toTree

theorem trialStrategy_height (T : ℕ) (K : ℕ) (hcost : ∀ p, (trial p).height ≤ K)
    (anchor : Fin N) : (trialStrategy candidates trial T anchor).height ≤ T * K := by
  simpa [trialStrategy] using trialLoop_height candidates trial K hcost T (Population.start candidates)

theorem trialStrategy_correct_of_runs (T : ℕ) (h : Hidden N R anchor)
    (hcorrect : ∀ out, ValidRun candidates trial h T (Population.start candidates) out →
      priceMajority (fun i => (out i).prices anchor) = h.positive) :
    Tree.Correct h (trialStrategy candidates trial T anchor) := by
  intro answer ha
  obtain ⟨out, hrun, rfl⟩ := (Computation.reaches_map_iff ..).mp
    ((Computation.reaches_toTree_iff ..).mp ha)
  exact hcorrect out ((reaches_trialLoop_iff ..).mp hrun)

/-- The exact population before the `t`-th trial of a fixed transcript. This function
also permits extending a finite transcript arbitrarily after its actual end. -/
def replay (p : Population N) (out : ℕ → RoundResult N) : ℕ → Population N
  | 0 => p
  | t+1 => (replay p out t).advance candidates (out t)

theorem replay_succ_first (p : Population N) (out : ℕ → RoundResult N) (t : ℕ) :
    replay candidates p out (t+1) =
      replay candidates (p.advance candidates (out 0)) (fun k => out (k+1)) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [replay]; rw [← ih]; rfl

theorem validRun_iff_steps (h : Hidden N R anchor) (T : ℕ) (p : Population N)
    (out : ℕ → RoundResult N) :
    ValidRun candidates trial h T p (fun i => out i.val) ↔
      ∀ t < T, Computation.Reaches h (trial (replay candidates p out t)) (out t) := by
  induction T generalizing p out with
  | zero => simp [ValidRun]
  | succ T ih =>
    constructor
    · rintro ⟨head, tail⟩ t ht
      cases t with
      | zero => exact head
      | succ t =>
        rw [replay_succ_first]
        exact (ih _ (fun j => out (j+1))).mp tail t (by omega)
    · intro hh
      refine ⟨hh 0 (by omega), (ih _ (fun j => out (j+1))).mpr ?_⟩
      intro t ht
      exact replay_succ_first candidates p out t ▸ hh (t+1) (by omega)

theorem replay_weight_eq (out : ℕ → RoundResult N) (t : ℕ) :
    (replay candidates (Population.start candidates) out t).weight =
      rootWeights (fun j => (replay candidates (Population.start candidates) out j).ids)
        (fun j => (out j).scores) t := by
  induction t with
  | zero => exact Population.start_weight _
  | succ t ih =>
    rw [rootWeights, ← ih, replay, Population.advance_weight]

theorem replay_ids_grow (p : Population N) (out : ℕ → RoundResult N) (t : ℕ) :
    (replay candidates p out t).ids ⊆ (replay candidates p out (t+1)).ids :=
  Population.ids_advance candidates _ _

/-- All component leaf logs are retained, in the chronological order of the trials. -/
def seenProbes (out : ℕ → RoundResult N) : ℕ → List (Probe N)
  | 0 => []
  | t+1 => seenProbes out t ++ (out t).observations

theorem replay_probes (out : ℕ → RoundResult N) (t : ℕ) :
    (replay candidates (Population.start candidates) out t).probes = seenProbes out t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [replay, Population.advance, seenProbes, ih]

/-- The list includes exactly the candidate batches generated at times `0,...,t`. -/
def expectedEntries (out : ℕ → RoundResult N) : ℕ → List (Expert N)
  | 0 => candidates []
  | t+1 => expectedEntries out t ++ candidates (seenProbes out (t+1))

theorem replay_entries (out : ℕ → RoundResult N) (t : ℕ) :
    (replay candidates (Population.start candidates) out t).experts = expectedEntries candidates out t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [replay, Population.advance, expectedEntries, ih, replay_probes, seenProbes]

end Schedule
end PriceGame
end LinearProgramming
end Optimization
end OAI
