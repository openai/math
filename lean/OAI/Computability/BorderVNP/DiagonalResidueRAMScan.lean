import OAI.Computability.BorderVNP.DiagonalResidueRAMFrame

/-!
# Sequential scans of binary choices and shared gate records

The first scan consumes exactly one branch per private input bit. The second
scan is deterministic. Neither scans the exponential set of possible grid
points or uses a full pin as an address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM RoutingISA
variable {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)

/-- One complete structured execution with prescribed positive weight, binary
choices, clock and final memory. -/
def Exact (c : Code) (s : Bank w) (m : Memory w) (bs : List Bool) (k : ℕ)
    (z : Bank w) (mz : Memory w) : Prop :=
  ∃ es, Runs pub macros c s m es z mz ∧ TraceOK es bs k

variable {pub macros}

/-- Concatenation of positive-weight executions. -/
theorem Exact.seq {c d : Code} {s t z : Bank w} {m mt mz : Memory w} {bs cs : List Bool}
    {a b : ℕ} (h : Exact pub macros c s m bs a t mt)
    (j : Exact pub macros d t mt cs b z mz) :
    Exact pub macros (.seq c d) s m (bs++cs) (a+b) z mz := by
  obtain ⟨es,he,ke⟩ := h
  obtain ⟨fs,hf,kf⟩ := j
  exact ⟨es++fs,.seq he hf,ke.append kf⟩

/-- Sequentially store the guessed words at consecutive addresses. -/
def putBits (m : Memory w) (start : ℕ) : List Bool → Memory w
  | [] => m
  | b :: bs => putBits (Function.update m start (wordBit w b)) (start+1) bs

/-- Sequentially evaluate gate rows, assigning their fresh destinations. -/
def putRows (m : Memory w) (start : ℕ) : List Row → Memory w
  | [] => m
  | r :: rs => putRows (Function.update m start (r.value m)) (start+1) rs

/-- Advice records at the given start and all their source addresses fit. -/
def loadedRows (m : Memory w) (ip : ℕ) : List Row → Prop
  | [] => True
  | r :: rs => r.atAddress m ip ∧ r.left < 2^w ∧ r.right < 2^w ∧ loadedRows m (ip+3) rs

/-- Memory strictly below the first record is independent of all advice words. -/
theorem loadedRows_congr {m m' : Memory w} (ip : ℕ) (rs : List Row)
    (h : ∀ j ≥ ip, m' j = m j) (hs : loadedRows m ip rs) : loadedRows m' ip rs := by
  induction rs generalizing ip with
  | nil => trivial
  | cons r rs ih =>
    rcases hs with ⟨⟨h₀,h₁,h₂⟩, hl, hr, rest⟩
    exact ⟨⟨(h _ le_rfl).trans h₀, (h _ (by omega)).trans h₁, (h _ (by omega)).trans h₂⟩, hl, hr,
      ih _ (fun j hj => h _ (by omega)) rest⟩

variable (pub macros)

/-- The loop over private binary words has exactly one execution for the
specified choices, including its final guard test. -/
theorem guess_loop (d : Frame) (bs : List Bool) (s : Bank w) (m : Memory w) (i start : ℕ)
    (hs : d.stable s) (hi : s 41 = word w i) (hc : s 40 = word w start)
    (hn : i + bs.length = d.guesses) (hbound : d.guesses < 2^w)
    (hspace : start + bs.length < 2^w) :
    ∃ z, Exact pub macros (.whileLt 41 33 guessBody) s m bs (6 * bs.length + 1) z
      (putBits m start bs) ∧ d.stable z ∧ z 40 = word w (start+bs.length) := by
  induction bs generalizing s m i start with
  | nil =>
    have eq : i = d.guesses := by simpa using hn
    have endLoop : ¬s 41 < s 33 := by simp [hi,hs.1.2.1,eq]
    exact ⟨s, ⟨[tick w], .whileDone endLoop, by simp [TraceOK,tick]⟩, hs, by simpa using hc⟩
  | cons b bs ih =>
    have hit : i < d.guesses := by simp at hn; omega
    have guard : s 41 < s 33 := by
      change (s 41).val < (s 33).val
      rw [hi,hs.1.2.1,word_val _ _ (hit.trans hbound),word_val _ _ hbound]
      exact hit
    let e := effect b s m guessBody
    obtain ⟨hs', hc', hi', hm', ht⟩ := guess_effect d s m b hs start i hc hi (by simp at hspace; omega)
    obtain ⟨z,⟨es,hr,he⟩,hstable,hcursor⟩ := ih e.bank e.mem (i+1) (start+1) hs' hi' hc'
      (by simp at hn; omega) (by simp at hspace; omega)
    have step := Runs.whileStep guard (guessBody_runs pub macros b s m) hr
    have tr := (ht.append he).cons_tick
    refine ⟨z, ⟨tick w :: (e.trace ++ es), ?_, ?_⟩, hstable, ?_⟩
    · simpa only [putBits, ← hm'] using step
    · rw [show 6 * (b :: bs).length + 1 = 5 + (6*bs.length+1) + 1 by simp; omega]
      exact tr
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hcursor

/-- The deterministic loop scans the actual three-word gate records.
Writes to the preceding valuation bank preserve the remaining advice. -/
theorem gate_loop (d : Frame) (rs : List Row) (s : Bank w) (m : Memory w) (i start ip : ℕ)
    (hs : d.stable s) (hi : s 41 = word w i) (hc : s 40 = word w start) (hp : s 42 = word w ip)
    (hn : i + rs.length = d.gates) (hbound : d.gates < 2^w)
    (hspace : start + rs.length ≤ ip) (hip : ip + 3 * rs.length < 2^w)
    (ha : loadedRows m ip rs) :
    ∃ z, Exact pub macros (.whileLt 41 32 gateBody) s m [] (14 * rs.length + 1) z
      (putRows m start rs) ∧ d.stable z := by
  induction rs generalizing s m i start ip with
  | nil =>
    have eq : i = d.gates := by simpa using hn
    have endLoop : ¬s 41 < s 32 := by simp [hi,hs.1.1,eq]
    exact ⟨s, ⟨[tick w], .whileDone endLoop, by simp [TraceOK,tick]⟩, hs⟩
  | cons r rs ih =>
    have hit : i < d.gates := by simp at hn; omega
    have guard : s 41 < s 32 := by
      change (s 41).val < (s 32).val
      rw [hi,hs.1.1,word_val _ _ (hit.trans hbound),word_val _ _ hbound]
      exact hit
    rcases ha with ⟨hrow, hl, hright, htail⟩
    let e := effect false s m gateBody
    obtain ⟨hs', hc', hi', hp', hm', ht⟩ := gate_effect d s m hs start i ip hc hi hp r hrow hl hright
      (by simp at hspace hip; omega) (by simp [Nat.mul_succ] at hip; omega)
    have ha' : loadedRows e.mem (ip+3) rs := by
      apply loadedRows_congr _ _ _ htail
      intro j hj
      rw [show e.mem = _ from hm', Function.update_of_ne (by simp at hspace; omega : j ≠ start)]
    obtain ⟨z,⟨es,hr,he⟩,hstable⟩ := ih e.bank e.mem (i+1) (start+1) (ip+3) hs' hi' hc' hp'
      (by simp at hn; omega) (by simp at hspace; omega) (by simp [Nat.mul_succ] at hip; omega) ha'
    have step := Runs.whileStep guard (gateBody_runs pub macros s m) hr
    have tr := (ht.append he).cons_tick
    refine ⟨z, ⟨tick w :: (e.trace ++ es), ?_, ?_⟩, hstable⟩
    · simpa only [putRows, ← hm'] using step
    · rw [show 14 * (r :: rs).length + 1 = 13 + (14*rs.length+1) + 1 by simp; omega]
      exact tr

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
