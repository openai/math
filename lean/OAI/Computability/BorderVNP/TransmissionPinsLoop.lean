import OAI.Computability.BorderVNP.TransmissionPinsStep
import Mathlib.Data.List.OfFn

/-! # Native pin preparation through the full physical array

The counted loop preserves the physical live bits whenever the scratch arrays are
disjoint from the inputs. Its only choices are the index bits in increasing order
on team zero, including when the index has width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Memory after the first `k` concrete write steps. -/
def preparedMemory (L : Layout) (guess : ℕ → Bool) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | k+1 => nextMemory L k (preparedMemory L guess m k) (guess k)

/-- Chronological choice list from the first `k` pin-preparation steps. -/
def preparedBits (L : Layout) (guess : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | k+1 => preparedBits L guess k ++ stepBits L k (guess k)

/-- Choices are exactly the genuine prefix on team zero. -/
theorem preparedBits_eq (L : Layout) (guess : ℕ → Bool) (k : ℕ) :
    preparedBits L guess k =
      List.ofFn (fun j : Fin (if L.team = 0 then min k L.width else 0) => guess j.val) := by
  induction k with
  | zero => simp [preparedBits]
  | succ k ih =>
    rw [preparedBits, ih]
    by_cases h : L.team = 0
    · by_cases hk : k < L.width
      · simp only [h, stepBits, Layout.active, hk, true_and, ite_true, Nat.min_eq_left hk.le,
          Nat.min_eq_left (Nat.succ_le_of_lt hk), Fin.val_cast, List.ofFn_succ',
          List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      · simp [h, stepBits, Layout.active, hk, Nat.min_eq_right (Nat.le_of_not_gt hk),
          Nat.min_eq_right (Nat.le_succ_of_le (Nat.le_of_not_gt hk))]
    · simp [h, stepBits, Layout.active]

/-- Bounds on each of the arithmetic addresses calculated by a pin-preparation step. -/
structure LoopFits (w : ℕ) (L : Layout) : Prop where
  /-- The processor bit width used as divisor is positive. -/
  literal : 0 < L.literal
  /-- Physical addresses of live inputs fit in a word. -/
  live : ∀ x < L.count, livePinAddress L.teams L.literal L.link x < 2^w
  /-- Every substituted position has an address in range. -/
  substitute : ∀ x < L.count, L.ibase+x < 2^w
  /-- Every active live-copy address fits in a word. -/
  copy : ∀ x < L.count, L.active x → L.hbase+x < 2^w

private theorem prepare_loop (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (guess : ℕ → Bool) (m : Memory w) (fits : LoopFits w L) (k x : ℕ)
    (he : x+k = L.count) (s : Bank w) (h : Ready L x s) :
    ∃ es t, Runs pub macros (.whileLt 6 7 preparePinStep) s (preparedMemory L guess m x) es t
        (preparedMemory L guess m L.count) ∧ traceCost es ≤ 17*k+1 ∧
      preparedBits L guess x ++ es.flatMap TeamRAM.Event.choices = preparedBits L guess L.count ∧
      Ready L L.count t := by
  induction k generalizing x s with
  | zero =>
    have hx : x = L.count := by omega
    subst x
    have hg : ¬ s 6 < s 7 := by
      change ¬ readings s 6 < readings s 7
      rw [h.cursor, h.count]
      omega
    refine ⟨_, s, Runs.whileDone hg, ?_, ?_, h⟩
    · exact le_rfl
    · simp [tick]
  | succ k ih =>
    have hx : x < L.count := by omega
    have hg : s 6 < s 7 := by
      change readings s 6 < readings s 7
      rwa [h.cursor, h.count]
    obtain ⟨es, u, r, cost, bits, hu⟩ := preparePinStep_run L x pub macros
      (preparedMemory L guess m x) s (guess x) h hx fits.literal (fits.live x hx)
      (fits.substitute x hx) (fits.copy x hx)
    obtain ⟨fs, t, r', cost', bits', ht⟩ := ih (x+1) (by omega) u hu
    refine ⟨_, t, Runs.whileStep hg r r', ?_, ?_, ht⟩
    · change 1 + traceCost (es ++ fs) ≤ _
      rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
      omega
    · simp only [tick, List.flatMap_cons, List.nil_append, List.flatMap_append, bits]
      simpa only [preparedBits, List.append_assoc] using bits'

/-- Running the actual preparation program produces the full scratch state, records precisely
the active guessed word, and costs at most seventeen ticks per physical slot plus setup. -/
theorem preparePins_run (L : Layout) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (m : Memory w) (s : Bank w) (guess : ℕ → Bool) (frame : Frame L (readings pub) (readings m))
    (hframe : readings pub 0 + 24 < 2^w) (ht : 0 < L.teams) (hs : L.stride < 2^w)
    (hc : L.count < 2^w) (hwidth : L.width ≤ L.count) (fits : LoopFits w L) :
    ∃ es t, Runs pub macros preparePins s m es t (preparedMemory L guess m L.count) ∧
      traceCost es ≤ pinSetup.slots + 17*L.count + 1 ∧
      es.flatMap TeamRAM.Event.choices =
        List.ofFn (fun j : Fin (if L.team = 0 then L.width else 0) => guess j.val) ∧
      Ready L L.count t := by
  obtain ⟨es,u,r,ct,hr⟩ := pinSetup_run L pub macros m s frame hframe ht hs hc
  obtain ⟨fs,t,r',ct',hb,hr'⟩ := prepare_loop L pub macros guess m fits L.count 0 (by omega) u hr
  refine ⟨_, t, r.seq r', ?_, ?_, hr'⟩
  · rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    omega
  · simp only [List.flatMap_append, noChoices r (by decide), List.nil_append]
    simpa only [preparedBits, List.nil_append, preparedBits_eq, Nat.min_eq_right hwidth, Fin.val_cast] using hb

private theorem nextMemory_other (L : Layout) (m : Memory w) (b : Bool) (x a : ℕ)
    (hi : a ≠ L.ibase+x) (hh : L.active x → a ≠ L.hbase+x) : nextMemory L x m b a = m a := by
  by_cases ha : L.active x <;> simp [nextMemory, ha, hi, hh]

/-- Any address outside the written prefix retains its initial value. -/
theorem preparedMemory_other (L : Layout) (guess : ℕ → Bool) (m : Memory w) (k a : ℕ)
    (hi : ∀ x < k, a ≠ L.ibase+x) (hh : ∀ x < k, L.active x → a ≠ L.hbase+x) :
    preparedMemory L guess m k a = m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [preparedMemory, nextMemory_other L _ _ k a (hi k (by omega)) (hh k (by omega))]
    exact ih (fun x hx => hi x (by omega)) (fun x hx => hh x (by omega))

/-- Distinct scratch arrays and a read-only physical input range for the native loop. -/
structure Separated (L : Layout) : Prop where
  /-- Every substituted cell is disjoint from every written live copy. -/
  scratch : ∀ x < L.count, ∀ y < L.count, L.active y → L.ibase+x ≠ L.hbase+y
  /-- No substituted cell overwrites a physical live bit that will be read. -/
  inputI : ∀ x < L.count, L.active x → ∀ y < L.count,
    livePinAddress L.teams L.literal L.link x ≠ L.ibase+y
  /-- No live-copy cell overwrites a physical live bit that will be read. -/
  inputH : ∀ x < L.count, L.active x → ∀ y < L.count, L.active y →
    livePinAddress L.teams L.literal L.link x ≠ L.hbase+y

/-- Placing both scratch intervals after the processor inputs, in either disjoint order,
suffices for preservation of every live input. -/
theorem Separated.of_intervals (L : Layout) (hi : L.processors * L.stride ≤ L.ibase)
    (hh : L.processors * L.stride ≤ L.hbase)
    (disjoint : L.ibase + L.count ≤ L.hbase ∨ L.hbase + L.width ≤ L.ibase) : Separated L := by
  constructor
  · intro x hx y _ hy
    have := hy.2
    omega
  · intro x hx _ y _
    have := livePinAddress_lt L hx
    omega
  · intro x hx _ y _ _
    have := livePinAddress_lt L hx
    omega

/-- All physical slots of the substituted array are initialized, including the zero padding. -/
theorem preparedMemory_substitute (L : Layout) (guess : ℕ → Bool) (m : Memory w)
    (sep : Separated L) {k x : ℕ} (hk : k ≤ L.count) (hx : x < k) :
    preparedMemory L guess m k (L.ibase+x) =
      (if L.active x then Fin.ofNat _ (guess x).toNat else 0) := by
  classical
  induction k with
  | zero => omega
  | succ k ih =>
    rw [preparedMemory]
    by_cases he : x=k
    · subst x
      by_cases h : L.active k <;> simp [nextMemory, h]
    · rw [nextMemory_other L _ _ k _ (by omega) (sep.scratch x (by omega) k (by omega))]
      exact ih (by omega) (by omega)

/-- Every active live-copy cell contains the original physical word of that position. -/
theorem preparedMemory_liveCopy (L : Layout) (guess : ℕ → Bool) (m : Memory w)
    (sep : Separated L) {k x : ℕ} (hk : k ≤ L.count) (hx : x < k) (ha : L.active x) :
    preparedMemory L guess m k (L.hbase+x) = m (livePinAddress L.teams L.literal L.link x) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [preparedMemory]
    by_cases he : x=k
    · subst x
      simp only [nextMemory, ha, ite_true,
        Function.update_of_ne (Ne.symm (sep.scratch k (by omega) k (by omega) ha)),
        Function.update_self]
      exact preparedMemory_other L guess m k _
        (fun y hy => sep.inputI k (by omega) ha y (by omega))
        (fun y hy => sep.inputH k (by omega) ha y (by omega))
    · rw [nextMemory_other L _ _ k _ (Ne.symm (sep.scratch k (by omega) x (by omega) ha))
        (fun _ => by omega)]
      exact ih (by omega) (by omega)

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
