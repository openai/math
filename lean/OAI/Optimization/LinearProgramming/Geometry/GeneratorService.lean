import OAI.Optimization.LinearProgramming.Geometry.OracleSimulation
import OAI.Optimization.LinearProgramming.Compression.Restart

/-! The minor request routine supplies the restartable geometric service of Section 2. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Compression PriceGame

variable {κ Q α : Type*}

/-- Within one label query the generator set is fixed. Relaying a rejection immediately
preserves the prefix guarantee of the compressor even for a partially answered label query. -/
def atGenerators (request : MinorRequest κ) (J : Finset κ) : MinorQuery κ α → Sum κ α
  | .done x => .inr x
  | .query key next => match request J key with
    | none => .inl key
    | some v => atGenerators request J (next v)

theorem atGenerators_reject (request : MinorRequest κ) (J : Finset κ) (p : MinorQuery κ α)
    {key : κ} (h : atGenerators request J p = .inl key) : request J key = none := by
  induction p with
  | done => cases h
  | query u next ih =>
    cases hu : request J u with
    | none =>
      have hkey : u = key := by simpa only [atGenerators, hu, Sum.inl.injEq] using h
      simpa only [← hkey] using hu
    | some v => exact ih v (by simpa only [atGenerators, hu] using h)

theorem atGenerators_eval (request : MinorRequest κ) (J : Finset κ) (p : MinorQuery κ α)
    (f : κ → ℚ) (hf : ∀ u v, request J u = some v → f u = v) {b : α}
    (h : atGenerators request J p = .inr b) : p.eval f = b := by
  induction p with
  | done => simpa only [atGenerators, MinorQuery.eval, Sum.inr.injEq] using h
  | query u next ih =>
    cases hu : request J u with
    | none => simp only [atGenerators, hu, reduceCtorEq] at h
    | some v => simpa only [MinorQuery.eval, hf u v hu] using ih v (by simpa only [atGenerators, hu] using h)

/-- The concrete service keeps only its generator set between label queries. -/
def generatorService [DecidableEq κ] (request : MinorRequest κ) (label : Q → MinorQuery κ Bool)
    (J : Finset κ) (q : Q) : Recovery.Reply (Finset κ) :=
  match atGenerators request J (label q) with
  | .inl u => .restart (insert u J)
  | .inr b => .answer b J

private theorem generatorService_answer [DecidableEq κ] (request : MinorRequest κ)
    (label : Q → MinorQuery κ Bool) {J J' : Finset κ} {q : Q} {b : Bool}
    (h : generatorService request label J q = .answer b J') :
    atGenerators request J (label q) = .inr b ∧ J' = J := by
  cases he : atGenerators request J (label q) with
  | inl => simp [generatorService, he] at h
  | inr v => simp [generatorService, he] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl,rfl⟩

private theorem generatorService_restart [DecidableEq κ] (request : MinorRequest κ)
    (label : Q → MinorQuery κ Bool) {J J' : Finset κ} {q : Q}
    (h : generatorService request label J q = .restart J') :
    ∃ u, request J u = none ∧ J' = insert u J := by
  cases he : atGenerators request J (label q) with
  | inl u =>
    refine ⟨u, atGenerators_reject _ _ _ he, ?_⟩
    simpa [generatorService, he, eq_comm] using h
  | inr => simp [generatorService, he] at h

/-- Every interruption adds a fresh generator, including interruptions deep inside a label query. -/
theorem generatorService_path_card [DecidableEq κ] (request : MinorRequest κ)
    (label : Q → MinorQuery κ Bool) (l : κ → ℝ) (test : RestartTest l request)
    {J J' : Finset κ} {log : List (Recovery.Event Q)}
    (path : Recovery.ServicePath (generatorService request label) J log J')
    (hJ : IsDissociated l J) :
    IsDissociated l J' ∧ J'.card = J.card + Recovery.restartCount log := by
  induction path with
  | nil => simpa using hJ
  | @answer s s' t q b log ans p ih =>
    obtain ⟨_, rfl⟩ := generatorService_answer _ _ ans
    simpa only [Recovery.restartCount_answer] using ih hJ
  | @restart s s' t q log rej p ih =>
    obtain ⟨u, hu, rfl⟩ := generatorService_restart _ _ rej
    have hnew := test.fresh _ _ hJ hu
    obtain ⟨hind, hcard⟩ := ih (test.independent _ _ hJ hu)
    refine ⟨hind, ?_⟩
    rw [hcard, Finset.card_insert_of_notMem hnew, Recovery.restartCount_restart]
    omega

/-- The same full assignment explains every price label in an uninterrupted epoch. -/
theorem generatorService_path_eval [DecidableEq κ] (request : MinorRequest κ)
    (label : Q → MinorQuery κ Bool) {J J' : Finset κ} {log : List (Recovery.Event Q)}
    (path : Recovery.ServicePath (generatorService request label) J log J')
    (noRestart : Recovery.restartCount log = 0) (f : κ → ℚ)
    (hf : ∀ u v, request J u = some v → f u = v) :
    ∀ q b, (q, some b) ∈ log → (label q).eval f = b := by
  induction path with
  | nil => simp
  | @answer s s' t q b log ans p ih =>
    obtain ⟨hans, rfl⟩ := generatorService_answer _ _ ans
    simp only [Recovery.restartCount_answer] at noRestart
    intro q' b' hmem
    rcases List.mem_cons.mp hmem with he | ht
    · cases he; exact atGenerators_eval request _ (label _) f hf hans
    · exact ih noRestart hf _ _ ht
  | restart => simp only [Recovery.restartCount_restart, Nat.add_one_ne_zero] at noRestart

/-- Starting from no generators, the compressor's simultaneous extension theorem explains
all labels in each fresh, adaptively queried epoch. The cardinality bound on dissociated
minors gives a cap on the number of restarts of this actual service. -/
theorem generatorService_recovers [DecidableEq κ] {N R : ℕ} (hR : 1 ≤ R) (anchor : Fin N)
    (p : PriceGame.Tree N) (maxQueries : ℕ) (hClock : p.height ≤ maxQueries)
    (correct : ∀ H : Hidden N R anchor, PriceGame.Tree.Correct H p)
    (request : MinorRequest κ) (label : Query N → MinorQuery κ Bool)
    (l : κ → ℝ) (test : RestartTest l request) (K : ℕ)
    (cap : ∀ J : Finset κ, IsDissociated l J → J.card ≤ K)
    (valid : (κ → ℚ) → Prop)
    (extend : ∀ J : Finset κ, IsDissociated l J →
      ∃ f : κ → ℚ, valid f ∧ ∀ u v, request J u = some v → f u = v)
    (flag : Bool) (C : (κ → ℚ) → Finset (Fin N → ℝ))
    (ha : ∀ f, valid f → 0 < circuitEnvelope (C f) anchor)
    (hb : ∀ f, valid f → ∀ i, 0 < circuitEnvelope (C f) i → circuitCost (C f) i ∈ Set.Icc 0 (R : ℝ))
    (hv : ∀ f, valid f → ∀ q, ValidNearLabel (C f) flag q ((label q).eval f)) :
    let result := Recovery.run States.Restart.step (generatorService request label) (maxQueries + 1) p (K + 1) ∅
    result.value = some flag ∧ result.log.length ≤ (K + 1) * (maxQueries + 1) := by
  have hstart : IsDissociated l (∅ : Finset κ) := by
    intro A hA B hB hAB
    exact (hAB ((Finset.subset_empty.mp hA).trans (Finset.subset_empty.mp hB).symm)).elim
  apply priceLearner_retry_correct hR anchor p maxQueries hClock correct (generatorService request label) _ flag K
    (fun f : {f // valid f} => C f.val) (fun f => ha f.val f.property)
    (fun f => hb f.val f.property)
  · intro s t past log prior epoch he
    have hds := (generatorService_path_card request label l test prior hstart).1
    obtain ⟨f, hf, ha⟩ := extend s hds
    refine ⟨⟨f, hf⟩, ?_⟩
    intro q b hqb
    rw [← generatorService_path_eval request label epoch he f ha q b hqb]
    exact hv f hf q
  · intro s log path
    obtain ⟨hd, hc⟩ := generatorService_path_card request label l test path hstart
    have hcard : s.card = Recovery.restartCount log := by simpa using hc
    rw [← hcard]
    exact cap s hd

/-- The generator budget supplied by the determinant counting argument, including its
integer rounding, for the actual nonzero minors of a complementary matrix pair. -/
theorem generatorCap_of_minor_proxy {r s N : ℕ} (D : Matrix (Fin r) (Fin N) ℚ)
    (E : Matrix (Fin s) (Fin N) ℚ) (hN : 1 ≤ N) (hrows : r + s = N)
    (l : NonzeroPairMinor D E → ℝ)
    (ha : ∀ i, |l i - Real.logb 2 (|((pairMinorValue D E i.val : ℚ) : ℝ)|)| ≤
      1 / 2 ^ (100 * (N + 1)^3 + 7 : ℕ)) (J : Finset (NonzeroPairMinor D E))
    (hd : IsDissociated l J) : J.card ≤ ⌈(7 * (N : ℝ)^2 + 8) * Real.logb 2 (N + 1)⌉₊ := by
  have h := dissociated_nonzeroPairMinor_card_le D E hN hrows (Rat.castHom ℝ)
    Rat.cast_injective J l (fun i _ => ha i) hd
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- Successful minor reads in one actual call, in their chronological order. -/
def atGeneratorsLog (request : MinorRequest κ) (J : Finset κ) : MinorQuery κ α → List (κ × ℚ)
  | .done _ => []
  | .query u next => match request J u with
    | none => []
    | some v => (u,v) :: atGeneratorsLog request J (next v)

theorem atGenerators_is_run (request : MinorRequest κ) (J : Finset κ) (p : MinorQuery κ α) :
    MinorQuery.Run p (atGeneratorsLog request J p) (atGenerators request J p) := by
  induction p with
  | done v => exact .done v
  | query u next ih =>
    cases h : request J u with
    | none => simpa only [atGenerators, atGeneratorsLog, h] using MinorQuery.Run.restart u next
    | some v => simpa only [atGenerators, atGeneratorsLog, h] using MinorQuery.Run.answer u next v (ih v)

/-- Count all minor requests made in a price-query log. The computation follows the same
state change as `generatorService`; the final rejected minor of a query costs one call. -/
def priceLogMinorCalls [DecidableEq κ] (request : MinorRequest κ) (label : Q → MinorQuery κ Bool) :
    Finset κ → List (Recovery.Event Q) → ℕ
  | _, [] => 0
  | J, e :: rest =>
    let out := atGenerators request J (label e.1)
    let next := match out with | .inl u => insert u J | .inr _ => J
    (atGeneratorsLog request J (label e.1)).length + MinorQuery.restartCost out +
      priceLogMinorCalls request label next rest

theorem priceLogMinorCalls_le [DecidableEq κ] (request : MinorRequest κ) (label : Q → MinorQuery κ Bool)
    {b : ℕ} (bound : ∀ q, (label q).Bounded b) (J : Finset κ) (log : List (Recovery.Event Q)) :
    priceLogMinorCalls request label J log ≤ log.length * b := by
  induction log generalizing J with
  | nil => simp [priceLogMinorCalls]
  | cons e log ih =>
    simp only [priceLogMinorCalls, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add ((atGenerators_is_run request J (label e.1)).call_bound (bound e.1))
      (ih _)).trans_eq (Nat.add_comm _ _)

end Geometry
end LinearProgramming
end Optimization
end OAI
