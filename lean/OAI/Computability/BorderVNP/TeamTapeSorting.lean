import OAI.Computability.BorderVNP.TeamTapeSortingGuard

/-! # Physical team sorter and boundary verifier

Each companion-paper probe contributes two old memory records, a read and a write.
The fixed named-stack table consumes their canonical five-word encodings, checks the
two boundary payloads, runs every Batcher layer, and scans its sorted block.
For any arrangement of the pairs among the processors and any arbitrary link bits,
it terminates within the same polynomial clock. A correct chronological memory trace
has a unique accepted exchange assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeSorting

open VPVNP BurstRAM RAMTape RAMLayout RAMMemory RAMSerialization RAMSort RAMBoundary

attribute [local instance] portDecidableEq

variable {d e w : ℕ}

/-- Local block of canonical pairs after the emitter closes its buffer with empty slots. -/
def rawBlock (hw : 2 ≤ w) (e : ℕ) (v : Word d) (x : ℕ → Option (WordRecord w)) :
    Wires (2+e) (RawSlot w) :=
  fun i => (recordFormat hw).words (block (2+e) v.val x i)

private theorem decoded_rawBlock (hw : 2 ≤ w) (e : ℕ) (v : Word d)
    (x : ℕ → Option (WordRecord w)) :
    SortReplay.decoded hw (rawBlock hw e v x) = block (2+e) v.val (wire x) := by
  funext i
  simp [rawBlock, SortReplay.decoded, parsedSlot, Format.parse_words, block, wire]

/-- Initial physical bank for one virtual block. Each shared endpoint is supplied once. -/
def siteInput (hw : 2 ≤ w) (a : Fields d e w) (v : Word d) (x : ℕ → Option (WordRecord w)) :
    Stacks Port :=
  inputBank (SitePost.prestate v (incoming a v) (outgoing a v) (rawBlock hw e v x, [])
    ((List.ofFn (incidentBits (embedFields a) v)).drop (16*w)))

/-- Number of steps covering the boundary canonicality guard and the complete physical
memory post-pass with its two accumulated verdict bits. -/
def siteBudget (d e w : ℕ) := 205*w+46 + SitePost.budget d e w 2

/-- The actual finite table counts exactly one path on local success and zero otherwise.
All paths halt at the stated time, for arbitrary messages and malformed field contents. -/
theorem program_spec (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w) (a : Fields d e w)
    (v : Word d) (x : ℕ → Option (WordRecord w)) (t : ℕ) (ht : siteBudget d e w ≤ t) :
    let ok := FormatAt hw hc a v ∧ MemoryAt (memory hw hc a) v (block (2+e) v.val (wire x))
    (∀ c, program.body.count c t (siteInput hw a v x) = @ite ℕ ok (Classical.propDecidable _) 1 0) ∧
      (∀ c, program.body.AllStops c t (siteInput hw a v x)) := by
  classical
  intro ok
  let prev := incoming a v
  let sent := outgoing a v
  let flags := [Sorter.verifyOK sent sent, Sorter.verifyOK prev prev]
  let raw := rawBlock hw e v x
  let tail := (List.ofFn (incidentBits (embedFields a) v)).drop (16*w)
  obtain ⟨out, run, hout⟩ := guard_runs v prev sent (raw, []) tail
  change guard.Runs (205*w+46) (siteInput hw a v x) out at run
  change out ∘ Sum.inr = SitePost.prestate v prev sent (raw, flags) tail at hout
  have hcan : SortReplay.CanonicalBlock hw raw := fun i =>
    (SortReplay.canonical_iff hw _).mpr ⟨_, rfl⟩
  have zeroBytes : (Boundary.recordBytes (fun _ : Fin 5 => (0 : Word w))).all (!·) = true := by
    change (Boundary.recordBytes ((recordFormat hw).words none)).all (!·) = true
    rw [SortReplay.recordBytes_words, recordFormat_empty]
    simp
  obtain ⟨hp, hs⟩ := parsed_edges hw hc a v
  let remaining := t - (205*w+46)
  have htime : t = remaining + (205*w+46) := by unfold siteBudget at ht; dsimp [remaining]; omega
  have hbudget : SitePost.budget d e w flags.length ≤ remaining := by
    change SitePost.budget d e w 2 ≤ _
    unfold siteBudget at ht; dsimp [remaining]; omega
  have post := SitePost.complete_spec hw hc (embedFields a) v (raw, flags) hcan prev sent hp
    (fun _ => hs) (fun hv => by simpa [prev, incoming, hv] using zeroBytes)
    (fun hv => by simpa [sent, outgoing, Nat.not_lt.mpr hv] using zeroBytes) remaining hbudget
  have hok : (flags.all id = true ∧ SortCanonical hw hc (embedFields a) v ∧
      MemoryAt (memory hw hc a) v (SortReplay.decoded hw raw)) ↔ ok := by
    simp only [flags, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id_eq,
      Sorter.verifyOK_iff hw, and_true, ← SortReplay.canonical_iff, raw, decoded_rawBlock,
      ok, FormatAt, prev, sent]
    tauto
  constructor
  · intro c
    change (guard.body.followedBy (SitePost.complete.onPorts Sum.inr).body).count _ _ _ = _
    rw [Routine.count_followedBy, htime, run.count_eq, FiniteRoutine.count_onPorts _ _ Sum.inr_injective, hout]
    apply (post.1 _).trans
    split <;> split <;> first | rfl | (rename_i hy hn; exact (hn (hok.mp hy)).elim) | (rename_i hn hy; exact (hn (hok.mpr hy)).elim)
  · intro c
    change (guard.body.followedBy (SitePost.complete.onPorts Sum.inr).body).AllStops _ _ _
    rw [Routine.allStops_followedBy, htime, run.allStops_iff, FiniteRoutine.allStops_onPorts _ _ Sum.inr_injective, hout]
    exact post.2 _

/-- The local stack clock, including the two canonicality checks, is eventually at most
`n^8` on every input. The first parameter is the padded block capacity and the second is
the total index width for the XOR comparators. -/
theorem siteBudget_le {n d e w : ℕ} (hn : 4000010 ≤ n) (hH : 2^e ≤ 2*n)
    (hd : 2+e+d ≤ n) (hw : w ≤ n) : siteBudget d e w ≤ n^8 := by
  have hp := SitePost.budget_le hn hH hd hw
  have add : SitePost.budget d e w 2 = SitePost.budget d e w 0 + 2 := by
    unfold SitePost.budget; omega
  have hn7 : n ≤ n^7 := by simpa only [pow_one] using
    (Nat.pow_le_pow_right (show 0 < n by omega) (show 1 ≤ 7 by decide))
  have scale : 254*n^7 ≤ n^8 := by
    rw [show n^8 = n*n^7 by ring]
    exact Nat.mul_le_mul_right _ (by omega)
  unfold siteBudget
  rw [add]
  omega

/-- For the companion's four-word records and arbitrarily interleaved padded input wires,
one and only one raw assignment makes every physical named-stack table accept exactly
when the chronological record list agrees with execution of the fixed path. -/
theorem existsUnique_bits_iff_transcript (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (x : ℕ → Option (WordRecord w)) {es : List (TeamRecords.Access (Word w))}
    {rs : List (TeamRecords.Record (Word w))}
    (he : TeamRecords.Matches es rs) (ht : TeamRecords.Timed es)
    (hp : (rs.flatMap TeamRecords.pair).Perm (occupied ((2+e)+d) x)) (t : ℕ)
    (hclock : siteBudget d e w ≤ t) :
    (∃! a : Fields d e w, ∀ v, program.body.count (fun _ _ => 0) t (siteInput hw a v x) = 1) ↔
      rs = TeamRecords.transcript (fun _ => 0) es := by
  classical
  let m := actualMemoryMessages (2+e) d (wire x)
  have hf : m.FitsWord := actualFits x
  have iff (a : Fields d e w) :
      (∀ v, program.body.count (fun _ _ => 0) t (siteInput hw a v x) = 1) ↔
        (∀ v, FormatAt hw hc a v) ∧ memory hw hc a = m ∧ rs = TeamRecords.transcript (fun _ => 0) es := by
    have hi (v : Word d) := (program_spec hw hc a v x t hclock).1 (fun _ _ => 0)
    simp_rw [hi]
    simp only [ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not, forall_and]
    rw [pairedMemory_iff_transcript x (memory hw hc a) he ht hp]
  constructor
  · rintro ⟨a, ha, _⟩
    exact ((iff a).mp ha).2.2
  · intro hs
    exact ⟨encodeFields hw m hf, (iff _).mpr ⟨format_encode hw hc m hf, memory_encode hw hc m hf, hs⟩,
      fun a ha => fields_eq_encode hw hc a m hf ((iff a).mp ha).1 ((iff a).mp ha).2.1⟩

end TeamTapeSorting

end BorderVNP
end Computability
end OAI
