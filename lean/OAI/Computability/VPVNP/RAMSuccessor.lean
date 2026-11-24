import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Successor messages and local RAM call validation

In Lemma 10.1, a successor message carries the cumulative cost and either
the running state or a halt. The last processor checks acceptance locally.
The site predicate reads its own reports and its two incident cuts. Its
unique consistent assignments recover precisely the bounded accepting call
chains, with read values still to be checked by the sorting network.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

variable {w : ℕ} {C : Type*}

/-- The status and persistent state form a tagged option. A halted state has
one representation, independently of the last persistent word. -/
@[ext] structure Cut (w : ℕ) where
  /-- Cumulative cost of the computation up to this boundary between site segments. -/
  cost : ℕ
  /-- Persistent state at the cut while the computation is running, or the empty option after
  an accepting halt. -/
  state : Option (Word w)
  deriving DecidableEq

/-- Advance the cut through the given call reports by adding their call-and-probe costs and
taking the resulting persistent state. -/
def Cut.advance (c : Cut w) (xs : List (Report w)) : Cut w :=
  ⟨c.cost + RAMBuckets.cost Report.probes xs, endState c.state xs⟩

@[simp] theorem Cut.advance_nil (c : Cut w) : c.advance [] = c := by
  cases c
  simp [Cut.advance, RAMBuckets.cost, endState]

theorem Cut.advance_append (c : Cut w) (xs ys : List (Report w)) :
    c.advance (xs ++ ys) = (c.advance xs).advance ys := by
  simp [Cut.advance, endState_append, Nat.add_assoc]

/-- Local processing at site `v`. A running continuation must have reached
the next bucket. All reports are validated using the incident running state. -/
structure SiteRun (P : Program w C) (fuel S H v : ℕ) (c : Cut w)
    (xs : List (Report w)) : Prop where
  incoming : c.state.isSome → v * H ≤ c.cost ∧ c.cost < (v + 1) * H
  before : RAMBuckets.StartsBefore Report.probes ((v + 1) * H) c.cost xs
  calls : LocalSegment P fuel c.state xs
  call_cap : ∀ r ∈ xs, 1 + r.probes ≤ H
  total_cap : (c.advance xs).cost ≤ S * H
  crossing : (c.advance xs).state.isSome → (v + 1) * H ≤ (c.advance xs).cost

/-- At an internal cut the outgoing message must be exactly the local result.
At the last site the send is clamped and the actual local result must be halted. -/
def SiteCheck (P : Program w C) (fuel S H v : ℕ) (input : Cut w)
    (output : Option (Cut w)) (block : List (Report w)) : Prop :=
  SiteRun P fuel S H v input block ∧
    match output with
    | some d => d = input.advance block
    | none => (input.advance block).state = none

/-- Internal wires are indexed by the site that sends them. -/
def inputCut {S : ℕ} (first : Cut w) (wire : Fin (S - 1) → Cut w) (i : Fin S) : Cut w :=
  if h : i.val = 0 then first else wire ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Look up the successor message sent by this site if it has a successor, returning the empty
option at the final site. -/
def outputCut {S : ℕ} (wire : Fin (S - 1) → Cut w) (i : Fin S) : Option (Cut w) :=
  if h : i.val + 1 < S then some (wire ⟨i.val, by omega⟩) else none

/-- Only the initial site substitutes a fixed incoming status. -/
def SitesPass (P : Program w C) (fuel S H : ℕ) (initial : Word w)
    (blocks : Fin S → List (Report w)) (wire : Fin (S - 1) → Cut w) : Prop :=
  ∀ i, SiteCheck P fuel S H i.val (inputCut ⟨0, some initial⟩ wire i) (outputCut wire i) (blocks i)

/-- Accumulated cost and state determine all internal cuts, independently of
the accept/reject decision. -/
def canonicalCuts : (n : ℕ) → Cut w → (Fin n → List (Report w)) → Fin (n - 1) → Cut w
  | 0, _, _ => Fin.elim0
  | 1, _, _ => Fin.elim0
  | n + 2, c, blocks =>
    let d := c.advance (blocks 0)
    Fin.cons d (canonicalCuts (n + 1) d (Fin.tail blocks))

/-- Recursive semantics for proving the equivalence with the independent
site tests. The cost and state are recomputed at each boundary. -/
private def ChainChecks (P : Program w C) (fuel S H : ℕ) :
    ℕ → Cut w → List (List (Report w)) → Prop
  | _, c, [] => c.state = none ∧ c.cost ≤ S * H
  | v, c, block :: rest =>
    SiteRun P fuel S H v c block ∧ ChainChecks P fuel S H (v + 1) (c.advance block) rest

private theorem cut_succ {n : ℕ} (c : Cut w) (wire : Fin (n + 1) → Cut w) (i : Fin (n + 1)) :
    inputCut c wire i.succ = inputCut (S := n + 1) (wire 0) (Fin.tail wire) i ∧
    outputCut wire i.succ = outputCut (S := n + 1) (Fin.tail wire) i := by
  rcases i with ⟨i, hi⟩
  cases i <;> simp [inputCut, outputCut, Fin.tail, Nat.succ_lt_succ_iff]

private theorem indexed_checks (P : Program w C) (fuel S H v n : ℕ) (c : Cut w)
    (blocks : Fin (n + 1) → List (Report w)) (wire : Fin n → Cut w) :
    (∀ i : Fin (n + 1), SiteCheck P fuel S H (v + i.val) (inputCut (S := n + 1) c wire i)
      (outputCut (S := n + 1) wire i) (blocks i)) ↔
      ChainChecks P fuel S H v c (List.ofFn blocks) ∧ wire = canonicalCuts (n + 1) c blocks := by
  induction n generalizing v c with
  | zero =>
    rw [Fin.forall_fin_succ]
    have he : wire = canonicalCuts 1 c blocks := Subsingleton.elim ..
    simp [inputCut, outputCut, SiteCheck, ChainChecks, he]
    exact fun hr _ => hr.total_cap
  | succ n ih =>
    rw [Fin.forall_fin_succ, List.ofFn_succ]
    have hrest : (∀ i : Fin (n + 1), SiteCheck P fuel S H (v + i.succ.val)
        (inputCut c wire i.succ) (outputCut wire i.succ) (blocks i.succ)) ↔
        ChainChecks P fuel S H (v + 1) (wire 0) (List.ofFn (Fin.tail blocks)) ∧
        Fin.tail wire = canonicalCuts (n + 1) (wire 0) (Fin.tail blocks) := by
      refine Iff.trans ?_ (ih (v + 1) (wire 0) (Fin.tail blocks) (Fin.tail wire))
      apply forall_congr'
      intro i
      obtain ⟨h1, h2⟩ := cut_succ c wire i
      rw [h1, h2]
      simp [Nat.add_comm, Nat.add_left_comm, Fin.tail]
    rw [hrest]
    simp only [Fin.val_zero, Nat.add_zero, inputCut, ↓reduceDIte, outputCut, Nat.zero_add,
      Nat.succ_lt_succ_iff, Nat.zero_lt_succ, SiteCheck, ChainChecks]
    constructor
    · rintro ⟨⟨hsite, he⟩, hchecks, htail⟩
      change wire 0 = c.advance (blocks 0) at he
      rw [he] at hchecks htail
      refine ⟨⟨hsite, hchecks⟩, ?_⟩
      rw [← Fin.cons_self_tail wire, canonicalCuts, he, htail]
    · rintro ⟨⟨hsite, ht⟩, rfl⟩
      simp only [canonicalCuts, Fin.cons_zero, Fin.tail_cons]
      exact ⟨⟨hsite, rfl⟩, ht, trivial⟩

private theorem local_some_of_ne_nil {P : Program w C} {fuel : ℕ} {s : Option (Word w)}
    {xs : List (Report w)} (hc : LocalSegment P fuel s xs) (hx : xs ≠ []) : s.isSome := by
  cases xs with
  | nil => contradiction
  | cons r rs => cases s with
    | none => contradiction
    | some _ => rfl

theorem SiteRun.input_cap {P : Program w C} {fuel S H v : ℕ} {c : Cut w}
    {block : List (Report w)} (h : SiteRun P fuel S H v c block) : c.cost ≤ S * H :=
  Nat.le_trans (Nat.le_add_right ..) h.total_cap

theorem SiteRun.cost_lt {P : Program w C} {fuel S H v : ℕ} {c : Cut w}
    {block : List (Report w)} (h : SiteRun P fuel S H v c block) (hH : 0 < H) :
    RAMBuckets.cost Report.probes block < 2 * H :=
  RAMBuckets.site_cost_lt hH (fun hn => (h.incoming (local_some_of_ne_nil h.calls hn)).1)
    h.before h.call_cap

/-- The cumulative cost sent on each internal edge is representable whenever
the global cap fits in a word. -/
theorem sitesPass_wire_cost {P : Program w C} {fuel S H : ℕ} {initial : Word w}
    {blocks : Fin S → List (Report w)} {wire : Fin (S - 1) → Cut w}
    (h : SitesPass P fuel S H initial blocks wire) (j : Fin (S - 1)) :
    (wire j).cost ≤ S * H := by
  have hj := j.isLt
  let i : Fin S := ⟨j.val, by omega⟩
  obtain ⟨hr, hs⟩ := h i
  have he : outputCut wire i = some (wire j) := by
    simp [outputCut, i, show j.val + 1 < S by omega]
  rw [he] at hs
  rw [hs]
  exact hr.total_cap

private theorem checks_sound {P : Program w C} {fuel S H v : ℕ} {c : Cut w}
    {blocks : List (List (Report w))} (hv : ChainChecks P fuel S H v c blocks) :
    RAMBuckets.Valid Report.probes H v c.cost blocks ∧ LocalSegment P fuel c.state blocks.flatten ∧
    (c.advance blocks.flatten).state = none ∧ (c.advance blocks.flatten).cost ≤ S * H ∧
    ∀ r ∈ blocks.flatten, 1 + r.probes ≤ H := by
  induction blocks generalizing v c with
  | nil => simpa [List.flatten_nil, Cut.advance_nil, LocalSegment, RAMBuckets.Valid, ChainChecks] using hv
  | cons block blocks ih =>
    obtain ⟨hr, ht⟩ := hv
    obtain ⟨hvalid, hseg, hend, hcap, hcalls⟩ := ih ht
    simp only [List.flatten_cons, Cut.advance_append, localSegment_append]
    refine ⟨⟨fun hn => (hr.incoming (local_some_of_ne_nil hr.calls hn)).1,
      hr.before, fun hn => hr.crossing (local_some_of_ne_nil hseg hn), hvalid⟩,
      ⟨hr.calls, hseg⟩, hend, hcap, ?_⟩
    exact fun r h => (List.mem_append.mp h).elim (hr.call_cap r) (hcalls r)

private theorem checks_complete {P : Program w C} {fuel S H v : ℕ} {c : Cut w}
    {blocks : List (List (Report w))} (hi : c.state.isSome → v * H ≤ c.cost ∧ c.cost < (v + 1) * H)
    (hv : RAMBuckets.Valid Report.probes H v c.cost blocks)
    (hseg : LocalSegment P fuel c.state blocks.flatten)
    (hend : (c.advance blocks.flatten).state = none)
    (hcap : (c.advance blocks.flatten).cost ≤ S * H)
    (hcalls : ∀ r ∈ blocks.flatten, 1 + r.probes ≤ H) : ChainChecks P fuel S H v c blocks := by
  induction blocks generalizing v c with
  | nil => simpa [ChainChecks] using And.intro hend hcap
  | cons block rest ih =>
    obtain ⟨_, hbefore, hstop, hvalid⟩ := hv
    simp only [List.flatten_cons, Cut.advance_append, localSegment_append] at hseg hend hcap
    have hbcap : ∀ r ∈ block, 1 + r.probes ≤ H := fun r hr => hcalls r (by simp [hr])
    have hc : (c.advance block).cost ≤ S * H := Nat.le_trans (Nat.le_add_right ..) hcap
    have hcross (h : (c.advance block).state.isSome) : (v + 1) * H ≤ (c.advance block).cost := by
      apply hstop
      intro he
      rw [he, Cut.advance_nil] at hend
      simp [hend] at h
    refine ⟨⟨hi, hbefore, hseg.1, hbcap, hc, hcross⟩,
      ih ?_ hvalid hseg.2 hend hcap (fun r hr => hcalls r (by simp [hr]))⟩
    intro h
    refine ⟨hcross h, ?_⟩
    by_cases hn : block = []
    · subst block
      rw [Cut.advance_nil] at h ⊢
      have hu := (hi h).2
      rw [Nat.succ_mul]
      omega
    · have hu := hbefore.finish_lt hn hbcap
      rw [Nat.succ_mul (v + 1)]
      exact hu

/-- The bounds used for accepted paths in Lemma 10.1. -/
def withinCaps (S H : ℕ) (rs : List (Report w)) : Prop :=
  RAMBuckets.cost Report.probes rs ≤ S * H ∧ ∀ r ∈ rs, 1 + r.probes ≤ H

private theorem sitesPass_iff {P : Program w C} {fuel S H : ℕ} {initial : Word w}
    {blocks : Fin S → List (Report w)} {wire : Fin (S - 1) → Cut w} (hS : 0 < S) :
    SitesPass P fuel S H initial blocks wire ↔
      ChainChecks P fuel S H 0 ⟨0, some initial⟩ (List.ofFn blocks) ∧
      wire = canonicalCuts S ⟨0, some initial⟩ blocks := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  simpa [SitesPass] using indexed_checks P fuel (n + 1) H 0 n ⟨0, some initial⟩ blocks wire

theorem successor_sound {P : Program w C} {fuel S H : ℕ} {initial : Word w}
    {blocks : Fin S → List (Report w)} {wire : Fin (S - 1) → Cut w} (hS : 0 < S)
    (h : SitesPass P fuel S H initial blocks wire) :
    LocalSegment P fuel (some initial) (List.ofFn blocks).flatten ∧
      endState (some initial) (List.ofFn blocks).flatten = none ∧
      withinCaps S H (List.ofFn blocks).flatten := by
  obtain ⟨_, hs, he, hc, ha⟩ := checks_sound ((sitesPass_iff hS).mp h).1
  exact ⟨hs, he, by simpa [Cut.advance] using hc, ha⟩

theorem sitesPass_eq_partition {P : Program w C} {fuel S H : ℕ} {initial : Word w}
    {blocks : Fin S → List (Report w)} {wire : Fin (S - 1) → Cut w} (hS : 0 < S)
    (h : SitesPass P fuel S H initial blocks wire) :
    List.ofFn blocks = RAMBuckets.partition Report.probes H 0 S 0 (List.ofFn blocks).flatten := by
  obtain ⟨hv, _⟩ := checks_sound ((sitesPass_iff hS).mp h).1
  simpa using hv.eq_partition.symm

private theorem canonical_input (S : ℕ) (c : Cut w) (blocks : Fin S → List (Report w)) (i : Fin S) :
    inputCut c (canonicalCuts S c blocks) i =
      c.advance ((List.ofFn blocks).take i.val).flatten := by
  cases S with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction n generalizing c with
    | zero =>
      have hi : i = 0 := Fin.ext (by simp)
      subst i
      simp [inputCut]
    | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [inputCut]
      · rw [(cut_succ c (canonicalCuts (n + 2) c blocks) j).1]
        simp only [canonicalCuts, Fin.cons_zero, Fin.tail_cons]
        rw [ih, List.ofFn_succ (f := blocks), Fin.val_succ, List.take_succ_cons, List.flatten_cons,
          Cut.advance_append]
        rfl

theorem sitesPass_input_cost {P : Program w C} {fuel S H : ℕ} {initial : Word w}
    {blocks : Fin S → List (Report w)} {wire : Fin (S - 1) → Cut w} (hS : 0 < S)
    (h : SitesPass P fuel S H initial blocks wire) (i : Fin S) :
    (inputCut ⟨0, some initial⟩ wire i).cost =
      RAMBuckets.cost Report.probes ((List.ofFn blocks).take i.val).flatten := by
  rw [((sitesPass_iff hS).mp h).2, canonical_input]
  simp [Cut.advance]

/-- Every bounded accepting call chain has a unique grouping and assignment
of the internal successor wires. Read consistency can be imposed independently. -/
theorem successor_unique (P : Program w C) (fuel S H : ℕ) (initial : Word w) (rs : List (Report w))
    (hS : 0 < S) (hH : 0 < H) (hseg : LocalSegment P fuel (some initial) rs)
    (hend : endState (some initial) rs = none) (hc : withinCaps S H rs) :
    ∃! p : (Fin S → List (Report w)) × (Fin (S - 1) → Cut w),
      (List.ofFn p.1).flatten = rs ∧ SitesPass P fuel S H initial p.1 p.2 := by
  obtain ⟨bs, ⟨hlen, hflat, hv⟩, huniq⟩ := RAMBuckets.existsUnique_partition Report.probes S H rs hc.1
  let blocks : Fin S → List (Report w) := fun i => bs.get (Fin.cast hlen.symm i)
  have heq : List.ofFn blocks = bs := by
    subst S
    simp [blocks]
  let c : Cut w := ⟨0, some initial⟩
  refine ⟨(blocks, canonicalCuts S c blocks), ⟨by simpa [heq] using hflat, (sitesPass_iff hS).mpr ?_⟩, ?_⟩
  · refine ⟨?_, rfl⟩
    rw [heq]
    exact checks_complete (by simp [hH]) hv (hflat ▸ hseg) (by simpa [Cut.advance, hflat] using hend)
      (by simpa [Cut.advance, hflat] using hc.1) (hflat ▸ hc.2)
  · rintro ⟨other, wire⟩ ⟨hf, hp⟩
    obtain ⟨hchecks, hwire⟩ := (sitesPass_iff hS).mp hp
    have hlo := huniq (List.ofFn other) ⟨List.length_ofFn, hf, (checks_sound hchecks).1⟩
    have hb : other = blocks := List.ofFn_injective (hlo.trans heq.symm)
    subst other
    exact Prod.ext rfl hwire

end BurstRAM

end VPVNP
end Computability
end OAI
