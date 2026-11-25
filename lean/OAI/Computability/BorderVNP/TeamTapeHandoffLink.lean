import OAI.Computability.BorderVNP.TeamTapeHandoffCodec

/-!
# Physical sender and receiver on a shared team link

The sender builds its message from the local field stacks before comparing it
with the guessed link. At the other endpoint the receiver reads those same
shared bits before the next part of its incident stream.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeHandoff.Link

open VPVNP.RAMTape

variable {w k : ℕ}

/-- The codec workspace and the independent incoming guess of the outgoing wire. -/
abbrev Port (k : ℕ) := Codec.Port k ⊕ Unit

/-- The fixed states of the sender's word serializer and bit comparison. -/
abbrev State (k : ℕ) := (Codec.serialize k).State ⊕ CompareState

private def afterWrite : Option (Codec.serialize k).State → State k
  | some q => .inl q
  | none => .inr (.left true)

private def comparePort : Bool → Port k
  | false => .inl .wire
  | true => .inr ()

private theorem comparePort_injective : Function.Injective (@comparePort k) := by
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- The sender serializes the locally computed fields onto its wire workspace,
then compares that stack with the physical candidate until the first end test. -/
def sender (k : ℕ) : StackCode (Port k) (State k)
  | .inl q => ((Codec.serialize k).body.code q).rename Sum.inl afterWrite
  | .inr q => (compareCode q).rename comparePort Sum.inr

/-- Workspace with the local successor fields and the physical guess on a separate stack. -/
def senderBank (f : Frame w k) (raw : List Bool) : Stacks (Port k) :=
  Sum.elim (Codec.bank f []) (fun _ => raw)

/-- Sender execution starts at the entry instruction of the width-independent serializer. -/
def entry (k : ℕ) : State k := .inl (Codec.serialize k).body.entry

/-- Every raw guess, including a truncated or overlong one, reaches the comparison outcome
after the stated number of bit instructions. Only the wire and guess stacks may be consumed. -/
theorem sender_run (f : Frame w k) (raw : List Bool) :
    ∃ out, StackRuns (sender k)
      ((k + 2) * (5 * w + 2) + 8 + (2 * min (1 + (k + 2) * w) raw.length + 2))
      (entry k) (senderBank f raw) (.inr (.done (decide (f.bits = raw)))) out ∧
      ∀ p : Codec.Port k, p ≠ .wire → out (.inl p) = Codec.bank f [] p := by
  let start := senderBank f raw
  let staged := Function.update (Codec.bank f []) .wire f.bits
  let mid : Stacks (Port k) := Sum.elim staged (fun _ => raw)
  have serialize := Codec.serialize_runs f []
  rw [List.append_nil] at serialize
  have first := serialize.lift (target := sender k) Sum.inl Sum.inl_injective
    afterWrite start (fun q h => by cases q <;> first | rfl | contradiction)
  have hstart : installStacks Sum.inl start (Codec.bank f []) = start :=
    installStacks_eq Sum.inl_injective start _ (fun _ => rfl)
  have hmid : installStacks Sum.inl start staged = mid := by
    apply installStacks_frame (target := mid) (small := staged) Sum.inl_injective (fun _ => rfl)
    intro p hp
    cases p with
    | inl p => exact (hp p rfl).elim
    | inr => rfl
  rw [hstart, hmid] at first
  obtain ⟨lastStacks, comparison⟩ := outgoing_checked f raw
  have last := comparison.lift (target := sender k) comparePort comparePort_injective
    Sum.inr mid (fun _ _ => rfl)
  have hcmp := installStacks_eq comparePort_injective mid (streams f.bits raw)
    (fun b => by
      cases b with
      | false => exact Function.update_self .wire f.bits (Codec.bank f [])
      | true => rfl)
  rw [hcmp] at last
  refine ⟨_, first.trans last, ?_⟩
  intro p hp
  have outside : ∀ b, comparePort b ≠ Sum.inl p := by
    intro b
    cases b <;> simp [comparePort, hp.symm]
  rw [installStacks_outside _ _ outside]
  exact Function.update_of_ne hp ..

/-- A physical guess admits an accepting sender execution exactly when it equals
the locally prescribed frame, including the zero PC and registers at a halt. -/
theorem sender_accept_iff (f : Frame w k) (raw : List Bool) :
    (∃ t out, StackRuns (sender k) t (entry k) (senderBank f raw) (.inr (.done true)) out) ↔
      f.bits = raw := by
  obtain ⟨s, run, _⟩ := sender_run f raw
  constructor
  · rintro ⟨t, out, accept⟩
    let bound := (k + 2) * (5 * w + 2) + 8 + (2 * min (1 + (k + 2) * w) raw.length + 2)
    have a := accept.paths (bound + 1)
    have b := run.paths (t + 1)
    rw [show bound + 1 + t = t + 1 + bound by omega, b] at a
    simpa [stackPaths, sender, compareCode, StackOp.rename] using a
  · intro h
    exact ⟨_, s, by simpa only [h, decide_true] using run⟩

/-- The actual accepting sender branch determines every field read by the next endpoint,
leaves its incident suffix available, and allows just one typed interpretation of the guess. -/
theorem receiver_of_accept (f : Frame w k) (raw suffix : List Bool) {t : ℕ}
    {out : Stacks (Port k)} (accept : StackRuns (sender k) t (entry k) (senderBank f raw)
      (.inr (.done true)) out) :
    (Codec.decode k).Runs ((k + 2) * (6 * w + 2) + 3)
        (Codec.incoming k w (raw ++ suffix)) (Codec.bank f suffix) ∧
      ∃! g : Frame w k, g.bits = raw := by
  have he := (sender_accept_iff f raw).mp ⟨t, out, accept⟩
  exact ⟨he ▸ Codec.decode_runs f suffix, unique_frame_on_link raw f he⟩

/-- A raw halt with a separately supplied PC, register file and timestamp passes the
physical sender check exactly for the canonical zeros and the prescribed elapsed time. -/
theorem halted_candidate_iff (pc ticks guessTime : VPVNP.BurstRAM.Word w)
    (regs : Fin k → VPVNP.BurstRAM.Word w) :
    let f : Frame w k := .accepted ticks
    let raw := true :: (Frame.live pc regs guessTime).words.flatMap VPVNP.BurstRAM.wordBits
    (∃ t out, StackRuns (sender k) t (entry k) (senderBank f raw) (.inr (.done true)) out) ↔
      pc = 0 ∧ regs = (fun _ => 0) ∧ guessTime = ticks := by
  intro f raw
  rw [sender_accept_iff]
  constructor
  · intro h
    have he : (Frame.live 0 (fun _ : Fin k => 0) ticks).bits =
        (Frame.live pc regs guessTime).bits := by
      apply congrArg (List.cons false)
      simpa only [f, Frame.words, List.ofFn_const] using (List.cons.inj h).2
    obtain ⟨hpc, hregs, htime⟩ := Frame.live.inj (Frame.bits_injective he)
    exact ⟨hpc.symm, hregs.symm, htime.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp only [f, raw, Frame.bits, Frame.halted, Frame.words, List.ofFn_const]

end TeamTapeHandoff.Link

end BorderVNP
end Computability
end OAI
