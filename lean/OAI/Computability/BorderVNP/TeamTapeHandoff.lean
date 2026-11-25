import OAI.Computability.BorderVNP.TeamRAM
import OAI.Computability.BorderVNP.TeamTapeHandoffCapacity

/-!
# Register, program-counter, and tick handoffs between processors

Fix a locally replayed accepting path of the adaptive team RAM. At each block
boundary the next processor receives exactly the state obtained by running the
preceding chunk, together with its cumulative logical time. A halt clears its
instruction fields and is propagated through all remaining processors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff

open VPVNP BurstRAM Filter

/-- Register state kept across RAM instructions. Private subroutine tapes and signs
belong to the computation inside a block. -/
structure Control (w k : ℕ) where
  /-- Program counter word. -/
  pc : Word w
  /-- The fixed number of live register words. -/
  regs : Fin k → Word w

variable {w k : ℕ}

/-- Close the live instruction fields as soon as the program accepts. -/
def capture (P : Control w k → TeamRAM.Instr w (Control w k)) (s : Control w k) (tick : Word w) :
    Frame w k :=
  match P s with
  | .accept => .accepted tick
  | _ => .live s.pc s.regs tick

/-- Deterministic register replay on the proposed instruction choices and retrieved old words. -/
def advance (P : Control w k → TeamRAM.Instr w (Control w k)) :
    Control w k → List (TeamRAM.Event w) → Option (Control w k)
  | s, [] => some s
  | s, e :: es => match (P s).advance e.choices e.old with
    | none => none
    | some (next, _) => advance P next es

private theorem advance_prefix (P : Control w k → TeamRAM.Instr w (Control w k))
    (s : Control w k) (front tail : List (TeamRAM.Event w)) (hl : TeamRAM.Local P s (front ++ tail)) :
    ∃ s', advance P s front = some s' ∧ TeamRAM.Local P s' tail := by
  induction front generalizing s with
  | nil => exact ⟨s, rfl, hl⟩
  | cons e es ih =>
    obtain ⟨_, next, hnext, hlocal⟩ := hl
    obtain ⟨s', hs, hl'⟩ := ih next hlocal
    exact ⟨s', by simpa [advance, hnext] using hs, hl'⟩

/-- Charge of a chunk of actual adaptive RAM events. -/
abbrev cost (es : List (TeamRAM.Event w)) : ℕ := RAMBuckets.cost (fun e => e.action.extra) es

/-- Local register replay from an incoming shared frame. A halted frame propagates only
across an empty chunk. A live frame accumulates the entire chunk's charge, checking the
global cap before storing the resulting tick word. -/
def nextFrame (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w) :
    Frame w k → List (TeamRAM.Event w) → Option (Frame w k)
  | .accepted t, es => if es.isEmpty && decide (t ≤ limit) then some (.accepted t) else none
  | .live pc regs t, es =>
    if t.val + cost es ≤ limit.val then (advance P ⟨pc, regs⟩ es).map
      (fun s' => capture P s' (RAMTape.PublicExprMachine.packed w (t.val + cost es))) else none

/-- A legal incoming state is either the native live register state or its canonical
accepted encoding when the native control is already at its terminal. -/
def Incoming (P : Control w k → TeamRAM.Instr w (Control w k)) (s : Control w k) (tick : Word w)
    (f : Frame w k) : Prop :=
  f = .live s.pc s.regs tick ∨ (P s = .accept ∧ f = .accepted tick)

private theorem incoming_capture (P : Control w k → TeamRAM.Instr w (Control w k))
    (s : Control w k) (t : Word w) : Incoming P s t (capture P s t) := by
  cases h : P s <;> simp [Incoming, capture, h]

/-- Validating a chunk recovers the native successor state, its cumulative tick and
a locally valid residual path. In the halted case the residual path must already be empty. -/
theorem nextFrame_spec (P : Control w k → TeamRAM.Instr w (Control w k)) (s : Control w k)
    (t limit : Word w) (f : Frame w k) (hf : Incoming P s t f)
    (front tail : List (TeamRAM.Event w)) (hl : TeamRAM.Local P s (front ++ tail))
    (hc : t.val + cost front ≤ limit.val) :
    ∃ s', TeamRAM.Local P s' tail ∧ nextFrame P limit f front =
      some (capture P s' (RAMTape.PublicExprMachine.packed w (t.val + cost front))) := by
  rcases hf with rfl | ⟨ha, rfl⟩
  · obtain ⟨s', he, hl'⟩ := advance_prefix P s front tail hl
    exact ⟨s', hl', by simp [nextFrame, hc, he]⟩
  · cases front with
    | nil =>
      have htime : t ≤ limit := by simpa [cost, RAMBuckets.cost] using hc
      exact ⟨s, hl, by simp [nextFrame, htime, capture, ha, cost, RAMBuckets.cost]⟩
    | cons e rest =>
      have hx := hl.1
      simp [ha, TeamRAM.Instr.action] at hx

/-- The physical guard's refusal at the next fetched instruction is exactly the local
maximality test for a proposed block, including a call whose read burst would straddle
the boundary. -/
theorem maximalBlock_iff_handoff (H global : ℕ) (front tail : List (TeamRAM.Event w)) :
    Team.MaximalBlock (fun e => e.action.extra) H front tail ↔
      cost front ≤ H ∧ ∀ e rest, tail = e :: rest →
        decision (H-cost front) global e.action.extra = .handoff := by
  change (_ ∧ _) ↔ (_ ∧ _)
  refine ⟨fun ⟨hc, hs⟩ => ⟨hc, fun e rest h => ?_⟩, fun ⟨hc, hs⟩ => ⟨hc, fun e rest h => ?_⟩⟩
  · have he := hs e rest h
    change H < cost front + (1+e.action.extra) at he
    rw [decision_handoff_iff]
    omega
  · have he := (decision_handoff_iff ..).mp (hs e rest h)
    change H < cost front + (1+e.action.extra)
    omega

/-- Inside a scheduled block the next instruction passes both guards at its exact
starting tick. The argument uses the entire burst charge before any private choices. -/
theorem interior_executes (localCap globalCap elapsed : ℕ) (front tail : List (TeamRAM.Event w))
    (e : TeamRAM.Event w) (hl : cost (front ++ e :: tail) ≤ localCap)
    (hg : elapsed + cost (front ++ e :: tail) ≤ globalCap) :
    decision (localCap-cost front) (globalCap-(elapsed+cost front)) e.action.extra = .execute := by
  rw [decision_execute_iff]
  simp only [cost, RAMBuckets.cost_append, RAMBuckets.cost] at hl hg ⊢
  omega

/-- The full list of outgoing processor frames, including the last processor's terminal.
At an internal boundary the compared outgoing raw bits are exactly the successor's inputs. -/
def Chain (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w) :
    Frame w k → List (List (TeamRAM.Event w)) → List (Frame w k) → Prop
  | _, [], fs => fs = []
  | _, _ :: _, [] => False
  | f, block :: blocks, f' :: fs => nextFrame P limit f block = some f' ∧ Chain P limit f' blocks fs

/-- The local boundary tests force every handoff frame, including in singleton teams. -/
theorem chain_unique (P : Control w k → TeamRAM.Instr w (Control w k)) (limit : Word w)
    {f : Frame w k} {blocks : List (List (TeamRAM.Event w))} {fs gs : List (Frame w k)}
    (hf : Chain P limit f blocks fs) (hg : Chain P limit f blocks gs) : fs = gs := by
  induction blocks generalizing f fs gs with
  | nil => exact hf.trans hg.symm
  | cons b bs ih =>
    cases fs with
    | nil => exact hf.elim
    | cons x xs =>
      cases gs with
      | nil => exact hg.elim
      | cons y ys =>
        obtain rfl := Option.some.inj (hf.1.symm.trans hg.1)
        exact congrArg (_ :: ·) (ih hf.2 hg.2)

/-- All processor boundaries can be filled, and the last processor finishes with a
canonical accepted halt at the cumulative charge of the full path. -/
theorem exists_chain (P : Control w k → TeamRAM.Instr w (Control w k)) (s : Control w k)
    (t limit : Word w) (f : Frame w k) (hf : Incoming P s t f)
    (bs : List (List (TeamRAM.Event w))) (hl : TeamRAM.Local P s bs.flatten)
    (hc : t.val + cost bs.flatten ≤ limit.val) :
    ∃ fs : List (Frame w k), Chain P limit f bs fs ∧ fs.length = bs.length ∧
      (bs ≠ [] → fs.getLast? = some (.accepted (RAMTape.PublicExprMachine.packed w (t.val+cost bs.flatten)))) := by
  induction bs generalizing s t f with
  | nil => exact ⟨[], rfl, rfl, fun h => (h rfl).elim⟩
  | cons x xs ih =>
    have hfull : cost (x :: xs).flatten = cost x + cost xs.flatten := RAMBuckets.cost_append _ _ _
    have hx : t.val + cost x ≤ limit.val := by rw [hfull] at hc; omega
    obtain ⟨s', hrest, hnext⟩ := nextFrame_spec P s t limit f hf x xs.flatten hl hx
    let t' := RAMTape.PublicExprMachine.packed w (t.val + cost x)
    let next := capture P s' t'
    have ht' : t'.val = t.val+cost x := RAMTape.PublicExprMachine.packed_val (hx.trans_lt limit.isLt)
    have htail : t'.val+cost xs.flatten ≤ limit.val := by rw [hfull] at hc; omega
    obtain ⟨fs, hv, hlen, hend⟩ := ih s' t' next (incoming_capture ..) hrest htail
    refine ⟨next :: fs, ⟨hnext, hv⟩, by simp [hlen], fun _ => ?_⟩
    rw [hfull, ← Nat.add_assoc, ← ht']
    cases xs with
    | nil =>
      have hf' : fs = [] := hv
      subst fs
      have hstop : P s' = .accept := hrest
      simp [cost, RAMBuckets.cost, next, capture, hstop]
    | cons y ys =>
      have he := hend (by simp)
      simp [List.getLast?_cons, he]

/-- For each positive team size, an accepting adaptive execution under the global clock
has one greedy block partition and one list of handoffs from the prescribed initial PC
and registers to the propagated accepted halt. The only transmitted path-dependent data
are the register state and logical time. -/
theorem eventually_unique_handoffs {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2)
    :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 0 < r → ∀ {w k : ℕ} (P : Control w k → TeamRAM.Instr w (Control w k))
      (start : Control w k) (limit : Word w), limit.val = TeamScales.ticks ξ r n →
      ∀ (es : List (TeamRAM.Event w)), TeamRAM.Local P start es →
      (∀ e ∈ es, e.action.extra ≤ TeamScales.width n (1/2)) → cost es ≤ limit.val →
      ∃! joint : List (List (TeamRAM.Event w)) × List (Frame w k),
        joint.1.length = r ∧ joint.1.flatten = es ∧ Team.ValidBlocks (fun e => e.action.extra)
          (TeamScales.block ξ n) joint.1 ∧
        Chain P limit (initial start.pc start.regs) joint.1 joint.2 ∧ joint.2.length = r ∧
        joint.2.getLast? = some (.accepted (RAMTape.PublicExprMachine.packed w (cost es))) := by
  filter_upwards [TeamScales.eventually_ticks_fit hξ hξ'] with n ht
  intro r hr w k P start limit hlim es hl hburst hcost
  obtain ⟨blocks, ⟨hrb, hflat, hv⟩, hu⟩ := Team.existsUnique_teamBlocks _ (TeamScales.block ξ n)
    (TeamScales.width n (1/2)) r es hburst (hcost.trans (hlim ▸ (ht r hr).le))
  have hpath : TeamRAM.Local P start blocks.flatten := hflat ▸ hl
  have hcap : (0 : Word w).val + cost blocks.flatten ≤ limit.val := by simpa [hflat] using hcost
  obtain ⟨frames, hchain, hlen, hlast⟩ := exists_chain P start 0 limit _ (Or.inl rfl) blocks hpath hcap
  have hne : blocks ≠ [] := by rintro rfl; simp at hrb; omega
  have hend := hlast hne
  refine ⟨(blocks,frames), ⟨hrb, hflat, hv, hchain, hlen.trans hrb, by simpa [hflat] using hend⟩, ?_⟩
  rintro ⟨bs, fs⟩ ⟨hb', hf', hv', hc', _, _⟩
  obtain rfl := hu bs ⟨hb', hf', hv'⟩
  exact congrArg (Prod.mk bs) (chain_unique P limit hc' hchain)

/-- The rounded binary logarithm of `2nr` suffices for the actual cumulative tick bound. -/
theorem ticks_fit_word {ξ : ℝ} (hξ : 0 ≤ ξ) {n r : ℕ} (hn : 1 ≤ n) (hr : 0 < r) :
    TeamScales.ticks ξ r n < 2 ^ TeamScales.logWidth r n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have htime : (n : ℝ) ^ (1 - ξ / 2) ≤ n := by
    calc
      _ ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
      _ = _ := Real.rpow_one _
  have hcap : TeamScales.ticks ξ r n ≤ r*n := by
    have h := (Nat.floor_le (mul_nonneg (by positivity : 0 ≤ (r : ℝ))
      (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) (1 - ξ / 2)))).trans
      (mul_le_mul_of_nonneg_left htime (by positivity : 0 ≤ (r : ℝ)))
    exact_mod_cast h
  have hw : TeamScales.logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold TeamScales.logWidth
    rw [← Real.natCeil_logb_natCast]; push_cast; rfl
  rw [hw]
  apply hcap.trans_lt (lt_of_lt_of_le _ (Nat.le_pow_clog (by decide) (2*n*r)))
  have hnpos : 0 < n*r := Nat.mul_pos (by omega) hr
  rw [Nat.mul_comm r n, Nat.mul_assoc]
  omega

/-- The `r-1` physical link strings are the encodings of all but the final outgoing frame. -/
def sharedBits (fs : List (Frame w k)) : List (List Bool) := fs.dropLast.map Frame.bits

/-- Every actual typed processor trace determines the correct number of successor links. -/
theorem sharedBits_length (fs : List (Frame w k)) : (sharedBits fs).length = fs.length-1 := by
  simp [sharedBits]

/-- A complete processor assignment, including the register handoffs and the sorted
memory checks and predecessor records within the team. -/
structure Joint (w k r h : ℕ) where
  /-- Per-processor instruction blocks, records, and cross-block sorting checks. -/
  history : TeamTranscript.History (TeamRAM.Event w) (Word w) r h
  /-- The successive outgoing register frames, with a final local verdict. -/
  frames : List (Frame w k)

/-- The accepted local data agree with all globally shared fields, preserving the native
program counter, registers, clock and per-instruction sign contributions. -/
def Joint.Valid {r h : ℕ} (t : Joint w k r h) (hr : 0 < r) (H : ℕ)
    (P : Control w k → TeamRAM.Instr w (Control w k)) (start : Control w k)
    (limit : Word w) (I : ℕ) (header : ℕ → Word w) (es : List (TeamRAM.Event w))
    (bits : List (List Bool)) (place : Equiv.Perm (Fin (2 ^ (h+Nat.clog 2 r)))) : Prop :=
  t.history.Valid hr H TeamRAM.Event.action I header place es ∧ TeamRAM.Local P start es ∧
    TeamRAM.Claims 1 es (t.history.records.drop I) ∧ es.map TeamRAM.Event.choices = bits ∧
    Chain P limit (initial start.pc start.regs) t.history.chunks t.frames ∧ t.frames.length = r ∧
    t.frames.getLast? = some (.accepted (RAMTape.PublicExprMachine.packed w (cost es))) ∧
    t.history.weight (TeamRAM.Sign.value ∘ TeamRAM.Event.sign) =
      (es.map (TeamRAM.Sign.value ∘ TeamRAM.Event.sign)).prod

/-- At the exact team clock, a genuine accepting adaptive RAM path has a unique joint
assignment of scheduled events, checked memory, physical Batcher data, and successor
register frames. Conversely a passing joint assignment recovers the native accepting path.
The choice of a sufficiently wide word, the global cap and the initial state precede all
path data. -/
theorem eventually_execute_iff_joint {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, ∀ hr : 0 < r, ∀ {w k : ℕ}
      (P : Control w k → TeamRAM.Instr w (Control w k)) (start : Control w k) (limit : Word w),
      limit.val = TeamScales.ticks ξ r n → ∀ I : ℕ, I ≤ r*(3*TeamScales.block ξ n) →
      ∀ (header : ℕ → Word w) (es : List (TeamRAM.Event w)) (bits : List (List Bool)),
      (∀ e ∈ es, e.action.extra ≤ TeamScales.width n (1/2)) → cost es ≤ limit.val →
      let h := Nat.clog 2 (4 * TeamScales.block ξ n)
      ∀ place : Equiv.Perm (Fin (2 ^ (h+Nat.clog 2 r))),
        TeamRAM.execute P start (RAMMemory.initialMemory I header) bits = some es ↔
        ∃! t : Joint w k r h, t.Valid hr (TeamScales.block ξ n) P start limit I header es bits place := by
  filter_upwards [TeamScales.eventually_ticks_fit hξ hξ', eventually_unique_handoffs hξ hξ'] with n ht hj
  intro r hr w k P start limit he I hi header es bits hburst hcost h place
  have hc := hcost.trans (he ▸ (ht r hr).le)
  have fit := TeamTranscript.accesses_length_le TeamRAM.Event.action header es hi
    (hc.trans (Nat.mul_le_mul_left _ (Nat.sub_le ..)))
  obtain ⟨hist, hv, uh⟩ := TeamTranscript.existsUnique_history hr h _ _ TeamRAM.Event.action I header
    place es hburst hc fit
  constructor
  · intro actual
    obtain ⟨hl, hm, hb⟩ := TeamRAM.execute_spec actual
    obtain ⟨⟨bs, fs⟩, ⟨hlen, hf, hs, chain, hfs, hend⟩, _⟩ := hj r hr P start limit he es hl hburst hcost
    have hchunks : hist.chunks = bs := by
      have h₁ := hv.2.2.1.eq_teamBlocks
      have h₂ := hs.eq_teamBlocks
      rw [hv.1, hv.2.1] at h₁
      rw [hlen, hf] at h₂
      exact h₁.symm.trans h₂
    rw [← hchunks] at chain
    refine ⟨⟨hist,fs⟩, ⟨hv, hl, (TeamRAM.claims_of_history_iff hv fit).mpr hm, hb,
      chain, hfs, hend, hv.weight_eq _⟩, ?_⟩
    rintro ⟨hist',fs'⟩ ⟨hv', _, _, _, hc', _, _, _⟩
    obtain rfl := uh hist' hv'
    obtain rfl := chain_unique P limit hc' chain
    rfl
  · rintro ⟨t, ⟨hv', hl, old, hb, _, _, _, _⟩, _⟩
    exact TeamRAM.execute_iff.mpr ⟨hl, (TeamRAM.claims_of_history_iff hv' fit).mp old, hb⟩

end TeamTapeHandoff

end BorderVNP
end Computability
end OAI
