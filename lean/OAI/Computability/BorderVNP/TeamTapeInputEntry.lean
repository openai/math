import OAI.Computability.BorderVNP.TeamTapeInputLayout
import OAI.Computability.BorderVNP.TeamTapeInputEmitSetup

/-! # From the processor tape alone to its initialized record buffer

In the pinned literal, the public starting address follows the two cut lengths. It is
a padded binary word of width `w`. The public buffer capacity follows as a compact
binary field. This single instruction table starts on the raw tape with empty workspace,
decodes the four public fields, prepares the cursor and buffer, and emits the physical
pairs from the entire RAM initialization segment. The interior routing bytes survive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInput.Entry

open VPVNP BurstRAM RAMTape RAMSerialization TeamTapeInputEmit.Setup

/-- Parser workspace, public staging parameters and physical record buffer. -/
abbrev Port := TeamTapeInput.Port ⊕ TeamTapeInputEmit.Setup.Port

private abbrev peekPort : Port := .inl (.peek .input)
private abbrev dataPort : Port := .inl (.cut .header)
private abbrev incidentPort : Port := .inl (.cut .incident)

/-- The emitter consumes the extracted initialization segment directly from the parser. -/
def setupPort : TeamTapeInputEmit.Setup.Port → Port
  | .emit .bits => dataPort
  | p => .inr p

private theorem setup_injective : Function.Injective setupPort := by
  intro i j h
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
    first | cases i <;> cases j <;> simp_all [setupPort] | cases i <;> simp_all [setupPort] |
      cases j <;> simp_all [setupPort] | simp_all [setupPort]

private def taggedPorts (dst : Port) : Option Unit → Port
  | none => peekPort
  | some _ => dst

private def tagged (dst : Port) : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).onPorts (taggedPorts dst)

private theorem tagged_runs (dst : Port) (hd : dst ≠ peekPort) (s : Stacks Port) (bs tail : List Bool)
    (hin : s peekPort = Evaluator.InputBank.fieldBits bs ++ tail) (hs : s dst = []) :
    (tagged dst).Runs (3*bs.length+1) s (Function.update (Function.update s peekPort tail) dst bs) := by
  have inj : Function.Injective (taggedPorts dst) := by
    rintro (_ | ⟨⟩) (_ | ⟨⟩) h <;> simp_all [taggedPorts]
  apply (FiniteRoutine.ofRoutine (Evaluator.InputBank.readField ())).runs_onPorts_framed inj
    (Evaluator.InputBank.readField_runs () bs tail (fun _ => []))
  · rintro (_ | ⟨⟩) <;> assumption
  · rintro (_ | ⟨⟩) <;> simp [taggedPorts, Evaluator.InputBank.frame, hd.symm]
  · intro p hp
    have h₁ : p ≠ peekPort := fun e => hp none e.symm
    have h₂ : p ≠ dst := fun e => hp (some ()) e.symm
    simp [h₁, h₂]

private def decodePorts : AffinePin.Index.Port → Port
  | .bits => .inl .bits
  | .high => .inl .high
  | .index => .inr .bucket
  | .tmp => .inl .scratch

/-- Parse both public staging fields, expanding the bucket capacity to a unary tally. -/
def readSetup : FiniteRoutine Port :=
  ((tagged (.inr .start)).followedBy (tagged (.inl .bits))).followedBy
    (AffinePin.Index.decode.onPorts decodePorts)

/-- Public staging fields as they appear in the literal, before any variable literal bits. -/
def setupBits (w n a H : ℕ) : List Bool :=
  Evaluator.InputBank.fieldBits (BurstRAM.wordBits (TeamTapeInputEmit.word w a)) ++
    Evaluator.InputBank.fieldBits (TeamTapeInput.digits n H)

/-- The full deterministic public-input and initialization procedure. -/
def program : FiniteRoutine Port :=
  ((TeamTapeInput.program.onPorts Sum.inl).followedBy readSetup).followedBy
    ((TeamTapeInputEmit.Setup.setup.onPorts setupPort).followedBy
      (TeamTapeInputEmit.program.onPorts (setupPort ∘ TeamTapeInputEmit.Setup.Port.emit)))

private theorem readSetup_runs (w n a H : ℕ) (hH : H ≤ n)
    (tail : List Bool) (s : Stacks Port) (hin : s peekPort = setupBits w n a H ++ tail)
    (hs : s (.inr .start) = []) (hb : s (.inl .bits) = []) (hh : s (.inl .high) = [])
    (ht : s (.inl .scratch) = []) (hc : s (.inr .bucket) = []) :
    let u := Function.update (Function.update (Function.update s peekPort tail)
      (.inr .start) (BurstRAM.wordBits (TeamTapeInputEmit.word w a))) (.inr .bucket) (List.replicate H true)
    ∃ t ≤ 3*w + 9*Nat.clog 2 (n+1) + 7*H+4, readSetup.Runs t s u := by
  intro u
  let addr := BurstRAM.wordBits (TeamTapeInputEmit.word w a)
  let bs := TeamTapeInput.digits n H
  let m := Function.update (Function.update s peekPort (Evaluator.InputBank.fieldBits bs ++ tail)) (.inr .start) addr
  let z := Function.update (Function.update m peekPort tail) (.inl .bits) bs
  have first := tagged_runs (.inr .start) (by decide) s addr (Evaluator.InputBank.fieldBits bs ++ tail)
    (by simpa [setupBits, addr, bs, List.append_assoc] using hin) hs
  have second := tagged_runs (.inl .bits) (by decide) m bs tail rfl (by simpa [m] using hb)
  obtain ⟨t, htime, dec⟩ := AffinePin.Index.decode_runs bs
  have hv : TapeWord.value bs = H := TeamTapeInput.digits_value hH
  rw [hv] at dec htime
  have run : (AffinePin.Index.decode.onPorts decodePorts).Runs t z u := by
    apply AffinePin.Index.decode.runs_onPorts_framed (by decide : Function.Injective decodePorts) dec
    · intro i; cases i <;> simp [z, m, decodePorts, AffinePin.Index.bank, hh, hc, ht]
    · intro i; cases i <;> simp [u, decodePorts, AffinePin.Index.bank, hb, hh, ht]
    · intro k hk
      have kb : k ≠ .inl .bits := fun e => hk .bits e.symm
      have kc : k ≠ .inr .bucket := fun e => hk .index e.symm
      by_cases kp : k = peekPort <;> by_cases ka : k = .inr .start <;>
        simp_all [z, m, u, addr]
  refine ⟨_, ?_, (first.followedBy second).followedBy run⟩
  simp only [addr, bs, TeamTapeInput.digits, length_wordBits] at htime ⊢
  omega

/-- Exact physical startup from the raw tape, with no preloaded cursor, buffer or width.
The caller can now append its ordinary/burst probe records and subsequently close and sort
the same buffer. The retained routing bits are independently available to that caller. -/
theorem runs {w : ℕ} (hw : 2 ≤ w) (p : UniversalMachine.Program) (n t₀ a H : ℕ)
    (free pins routing : List Bool) (exterior : List (List Bool)) (hH : H ≤ n)
    (hf : (UniversalMachine.programPrefix p).length + 4*Nat.clog 2 (n+1)+2 +
      (setupBits w n a H ++ free).length = t₀)
    (hsize : t₀+exterior.flatten.length+pins.length+routing.length ≤ n) :
    let m := t₀+exterior.flatten.length+pins.length
    let pub := TeamTapeInput.parameters (TeamTapeInput.digits n m) (TeamTapeInput.digits n routing.length)
    let literal := UniversalMachine.programPrefix p ++ pub ++ (setupBits w n a H ++ free)
    let data := TeamTapeInput.inputData literal exterior pins
    let pad := List.replicate (n-(m+routing.length)) false
    let raw := data ++ routing ++ pad
    2*(a+data.length) ≤ 2^w → 2*data.length ≤ 4*H →
    ∃ t out, t ≤ 46*n+19 + (3*w + 9*Nat.clog 2 (n+1) + 7*H+4) +
        (10*w+20*H+13 + TeamTapeInputEmit.budget w data.length) ∧
      program.Runs t (Sum.elim (TeamTapeInput.initial raw) (fun _ => [])) out ∧
      TeamTapeInputEmit.Ready hw H (a+data.length) [] (TeamTapeInputEmit.records w a data)
        (out ∘ setupPort ∘ TeamTapeInputEmit.Setup.Port.emit) ∧ out incidentPort = routing ∧
      out (.inr .start) = BurstRAM.wordBits (TeamTapeInputEmit.word w a) ∧
      out peekPort = free ++ exterior.flatten ++ pins ++ routing ++ pad ∧
      out (.inl .bits) = [] ∧ out (.inl .high) = [] ∧ out (.inl .scratch) = [] ∧
      out (.inr .bucket) = List.replicate H true := by
  intro m pub lit data pad raw fits cap
  let tail := free ++ exterior.flatten ++ pins ++ routing ++ pad
  let parsed := TeamTapeInput.loaded (UniversalMachine.programPrefix p) (setupBits w n a H ++ tail) data routing
  let s : Stacks Port := Sum.elim parsed (fun _ => [])
  obtain ⟨_, _, t, htime, run⟩ := TeamTapeInput.run_layout p n t₀ (setupBits w n a H ++ free)
    pins routing exterior hf hsize
  have parse : (TeamTapeInput.program.onPorts Sum.inl).Runs t
      (Sum.elim (TeamTapeInput.initial raw) (fun _ => [])) s := by
    apply TeamTapeInput.program.runs_onPorts_framed Sum.inl_injective run
    · exact fun _ => rfl
    · intro k; cases k <;> first | rfl | (rename_i p'; cases p' <;> simp [s, parsed, TeamTapeInput.loaded, tail, data, lit, pub, m, pad, List.append_assoc])
    · rintro (k | k) hk
      · exact (hk k rfl).elim
      · rfl
  obtain ⟨t', ht', read⟩ := readSetup_runs w n a H hH tail s rfl rfl rfl rfl rfl rfl
  let u := Function.update (Function.update (Function.update s peekPort tail) (.inr .start)
    (BurstRAM.wordBits (TeamTapeInputEmit.word w a))) (.inr .bucket) (List.replicate H true)
  have su : u ∘ setupPort = TeamTapeInputEmit.Setup.input w H a data := by
    funext i
    rcases i with _ | _ | k <;> first | rfl | (cases k <;> rfl)
  let v := installStacks setupPort u (TeamTapeInputEmit.Setup.prepared w H a data)
  have setup := TeamTapeInputEmit.Setup.setup.runs_onPorts setup_injective u (TeamTapeInputEmit.Setup.setup_runs w H a data)
  rw [← su, installStacks_eq setup_injective u (u ∘ setupPort) (fun _ => rfl)] at setup
  let small := setupPort ∘ TeamTapeInputEmit.Setup.Port.emit
  have sv : v ∘ small = TeamTapeInputEmit.Setup.prepared w H a data ∘ TeamTapeInputEmit.Setup.Port.emit :=
    funext fun i => installStacks_at setup_injective u _ _
  have ready : TeamTapeInputEmit.Ready hw H a data [] (v ∘ small) := sv.symm ▸ TeamTapeInputEmit.Setup.ready hw H a data
  obtain ⟨k, smallOut, hk, hr, hfinal⟩ := TeamTapeInputEmit.runs ready fits (by simpa using cap)
  let out := installStacks small v smallOut
  have inj : Function.Injective small := setup_injective.comp (fun _ _ => TeamTapeInputEmit.Setup.Port.emit.inj)
  have emit := TeamTapeInputEmit.program.runs_onPorts inj v hr
  rw [installStacks_eq inj v (v ∘ small) (fun _ => rfl)] at emit
  have he : out ∘ small = smallOut := funext fun i => installStacks_at inj v smallOut i
  have outside : ∀ i, setupPort i ≠ incidentPort := by
    rintro (_ | _ | k)
    · simp [setupPort]
    · simp [setupPort]
    · cases k <;> simp [setupPort, incidentPort, dataPort]
  have hx : out incidentPort = routing := (installStacks_outside v smallOut (fun i => outside (.emit i))).trans
    (installStacks_outside u _ outside)
  have preserved (i : TeamTapeInput.Port) (hi : i ≠ .cut .header) : out (.inl i) = u (.inl i) := by
    have h : ∀ j, setupPort j ≠ .inl i := by
      rintro (_ | _ | j)
      · simp [setupPort]
      · simp [setupPort]
      · cases j <;> simp [setupPort, dataPort, hi.symm]
    exact (installStacks_outside v smallOut (fun j => h (.emit j))).trans (installStacks_outside u _ h)
  have hs : out (.inr .start) = BurstRAM.wordBits (TeamTapeInputEmit.word w a) :=
    (installStacks_outside v smallOut (fun j => by cases j <;> simp [small, setupPort])).trans
      (installStacks_at setup_injective u _ .start)
  have hb : out (.inr .bucket) = List.replicate H true :=
    (installStacks_outside v smallOut (fun j => by cases j <;> simp [small, setupPort])).trans
      (installStacks_at setup_injective u _ .bucket)
  exact ⟨_, out, Nat.add_le_add (Nat.add_le_add htime ht') (Nat.add_le_add_left hk _),
    (parse.followedBy read).followedBy (setup.followedBy emit), by change TeamTapeInputEmit.Ready _ _ _ _ _ (out ∘ small); rw [he]; simpa only [List.nil_append] using hfinal, hx, hs,
    preserved (.peek .input) (by decide), preserved .bits (by decide),
    preserved .high (by decide), preserved .scratch (by decide), hb⟩

end TeamTapeInput.Entry

end BorderVNP
end Computability
end OAI
