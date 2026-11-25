import OAI.Computability.BorderVNP.TeamLocalClockModel
import OAI.Computability.BorderVNP.TeamTapeHandoffLink

/-!
# Emitting and checking the computed successor frame

A continuing handoff copies the architectural registers, the elapsed clock and
a binary word generated from the retained finite PC. An accepted halt copies
one canonical zero word into all instruction fields. Register contents in the
architectural bank are preserved in both cases. The computed stream is compared
with the actual successor-link bits; the last processor simply requires a halt.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamLocalClock.Finish

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff

variable {w p r k : ℕ}

/-- Only these three extra bit stacks are needed outside the shared loop bank. -/
inductive Port (r k : ℕ) where
  | clock (u : TeamLocalClock.Port r k)
  | payload | candidate | tmp
  deriving DecidableEq, Fintype

/-- The terminal outcome or the retained program-counter label for a live handoff. -/
inductive Mode (p : ℕ) where
  | accepted | live (pc : Fin p)
  deriving Fintype

/-- The bit for the physical outgoing register frame. -/
def Mode.halted : Mode p → Bool
  | .accepted => true
  | .live _ => false

/-- Integer literal to be staged into the PC/zero word workspace. -/
def Mode.pcValue : Mode p → ℕ
  | .accepted => 0
  | .live pc => pc.val

/-- Exact typed frame read from the current architectural registers and cumulative time. -/
def frame (mode : Mode p) (regs : Fin r → Word w) (elapsed : Word w) : Frame w r :=
  match mode with
  | .accepted => .accepted elapsed
  | .live pc => .live (packed w pc.val) regs elapsed

/-- Fixed layout for arbitrary actual candidate bits and an in-progress encoded payload. -/
def bank (core : Stacks (TeamLocalClock.Port r k)) (payload candidate : List Bool) : Stacks (Port r k)
  | .clock u => core u
  | .payload => payload
  | .candidate => candidate
  | .tmp => []

private theorem install_clock (core core' : Stacks (TeamLocalClock.Port r k)) (payload raw : List Bool) :
    installStacks Port.clock (bank core payload raw) core' = bank core' payload raw := by
  funext p
  cases p with
  | clock i => exact installStacks_at (fun _ _ he => Port.clock.inj he) _ _ _
  | payload | candidate | tmp => rw [installStacks_outside (hl := fun _ => by simp)]; rfl

private def sources (mode : Mode p) : List (TeamLocalClock.Port r k) :=
  .meter (.reg 5) :: (List.ofFn fun j : Fin r => if mode.halted then .meter (.reg 5) else .isa (.reg j)) ++
    [.meter (.reg 2)]

private def copyFields : List (TeamLocalClock.Port r k) → FiniteRoutine (Port r k)
  | [] => .ret
  | x :: xs => (copyFields xs).followedBy (SuccessorFields.prependCopy (.clock x) .payload .tmp)

private theorem copy_fields_run (fields : List (TeamLocalClock.Port r k))
    (core : Stacks (TeamLocalClock.Port r k)) (payload raw : List Bool) (width : ℕ)
    (hw : ∀ i ∈ fields, (core i).length = width) :
    (copyFields fields).Runs (fields.length*(5*width+2)+1) (bank core payload raw)
      (bank core (fields.flatMap core ++ payload) raw) := by
  induction fields with
  | nil => simp only [copyFields, List.length_nil, zero_mul, zero_add, List.flatMap_nil, List.nil_append]; exact Routine.runs_ret _
  | cons x xs ih =>
    have tail := ih (fun i hi => hw i (List.mem_cons_of_mem _ hi))
    let mid := bank core (xs.flatMap core ++ payload) raw
    have hp := SuccessorFields.prependCopy_runs (Port.clock x) Port.payload Port.tmp
      (by simp) (by simp) (by simp) mid rfl
    have he : Function.update mid Port.payload (core x ++ (xs.flatMap core ++ payload)) =
        bank core ((x::xs).flatMap core ++ payload) raw := by
      funext i; cases i <;> simp [bank, mid, List.append_assoc]
    change (SuccessorFields.prependCopy (Port.clock x) Port.payload Port.tmp).Runs (5*(core x).length+2)
      mid (Function.update mid Port.payload (core x ++ (xs.flatMap core ++ payload))) at hp
    rw [he, hw x (List.mem_cons_self ..)] at hp
    rw [show (x::xs).length*(5*width+2)+1 = (xs.length*(5*width+2)+1)+(5*width+2) by simp only [List.length_cons, Nat.succ_mul]; omega]
    exact tail.followedBy hp

private def literal (n : ℕ) : FiniteRoutine (Port r k) :=
  ((ISA.loadLiteral n (5 : Fin 6)).onPorts TeamLocalClock.Port.meter).onPorts Port.clock

private theorem literal_run (n : ℕ) (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (regs : Fin 6 → Word w) (max : Word w) (stamp payload raw : List Bool) :
    (literal n).Runs (8*w+3) (bank (banks pub s regs max stamp) payload raw)
      (bank (banks pub s (Function.update regs 5 (packed w n)) max stamp) payload raw) := by
  have hm := meter_runs pub s regs _ max stamp (ISA.loadLiteral_run n (5 : Fin 6) Fin.elim0 (0 : Word w) regs [])
  simpa only [literal, packed, install_clock] using ((ISA.loadLiteral n (5 : Fin 6)).onPorts TeamLocalClock.Port.meter).runs_onPorts
    (fun _ _ he => Port.clock.inj he) (bank (banks pub s regs max stamp) payload raw) hm

/-- The physical serializer stages the actual PC literal and clears its workspace before
return. For a halt its all-zero PC word also supplies every canonical zero register. -/
def serialize (mode : Mode p) : FiniteRoutine (Port r k) :=
  (((literal mode.pcValue).followedBy (copyFields (sources mode))).followedBy
    (.ofRoutine (Routine.push .payload mode.halted))).followedBy (literal 0)

private theorem source_data (mode : Mode p) (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (l g elapsed max : Word w) (stamp : List Bool) :
    let reg := Function.update (chargeRegisters l g elapsed 0) 5 (packed w mode.pcValue)
    let core := banks pub s reg max stamp
    (sources (r := r) (k := k) mode).flatMap core = (frame mode s.reg elapsed).words.flatMap wordBits ∧
      ∀ i ∈ sources mode, (core i).length = w := by
  intro reg core
  cases mode with
  | live pc =>
    constructor
    · simp [sources, Mode.halted, Mode.pcValue, frame, Frame.words, core, banks, reg, ISA.bank,
        chargeRegisters]
      rw [List.flatMap_def, List.flatMap_def, List.map_ofFn, List.map_ofFn]; rfl
    · intro i hi
      simp [sources, Mode.halted] at hi
      rcases hi with h | ⟨j, h⟩ | h <;> subst i <;>
        simp [core, banks, reg, ISA.bank, ISA.configBank, chargeRegisters]
  | accepted =>
    constructor
    · simp [sources, Mode.halted, Mode.pcValue, frame, Frame.words, core, banks, reg, ISA.bank,
        chargeRegisters, List.ofFn_const]
      rw [List.flatMap_def, List.flatMap_def, List.map_replicate, List.map_replicate]; rfl
    · intro i hi
      simp [sources, Mode.halted] at hi
      rcases hi with h | ⟨j, h⟩ | h <;> subst i <;> simp [core, banks, reg, ISA.bank, chargeRegisters]

/-- Finish serialization yields precisely the typed frame and restores the original clock
and architectural bank. Its cost is linear in the physical word width. -/
theorem serialize_run (mode : Mode p) (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (l g elapsed max : Word w) (stamp raw : List Bool) :
    let core := banks pub s (chargeRegisters l g elapsed 0) max stamp
    (serialize (r := r) (k := k) mode).Runs (2*(8*w+3)+(r+2)*(5*w+2)+2) (bank core [] raw)
      (bank core (frame mode s.reg elapsed).bits raw) := by
  intro core
  let regs := chargeRegisters l g elapsed 0
  let mid := Function.update regs 5 (packed w mode.pcValue)
  let arch := banks pub s mid max stamp
  let f := frame mode s.reg elapsed
  have load := literal_run mode.pcValue pub s regs max stamp [] raw
  obtain ⟨hbits, hwidth⟩ := source_data mode pub s l g elapsed max stamp
  have copy := copy_fields_run (sources mode) arch [] raw w hwidth
  have hcount : (sources (r := r) (k := k) mode).length = r+2 := by simp [sources]
  change (sources mode).flatMap arch = f.words.flatMap wordBits at hbits
  rw [hbits, List.append_nil, hcount] at copy
  have htag : (FiniteRoutine.ofRoutine (Routine.push (Port.payload : Port r k) mode.halted)).Runs 1
      (bank arch (f.words.flatMap wordBits) raw) (bank arch f.bits raw) := by
    have hp := Routine.runs_push (Port.payload : Port r k) mode.halted (bank arch (f.words.flatMap wordBits) raw)
    have eq : Function.update (bank arch (f.words.flatMap wordBits) raw) .payload
        (mode.halted :: (f.words.flatMap wordBits)) = bank arch f.bits raw := by
      funext z; cases z <;> cases mode <;> simp [f, frame, Frame.bits, Frame.halted, Mode.halted, bank]
    rw [← eq]; exact hp
  have clear := literal_run 0 pub s mid max stamp f.bits raw
  have he : Function.update mid 5 (packed w 0) = regs := by
    funext j; fin_cases j <;> rfl
  rw [he] at clear
  have total := ((load.followedBy copy).followedBy htag).followedBy clear
  rw [show 2*(8*w+3)+(r+2)*(5*w+2)+2 = (((8*w+3)+((r+2)*(5*w+2)+1))+1)+(8*w+3) by ring]
  exact total

/-- The fixed sender controller compares the computed physical frame against the
shared candidate, or directly tests the final halt on the last processor. -/
inductive Label (p r k : ℕ) where
  | enter (mode : Mode p) (last : Bool)
  | write (mode : Mode p) (q : (serialize (r := r) (k := k) mode).State)
  | compare (q : CompareState)
  | done (ok : Bool)
  deriving Fintype

private def cmpPorts : Bool → Port r k
  | false => .payload
  | true => .candidate

private def cmpLabel : CompareState → Label p r k
  | .done ok => .done ok
  | q => .compare q

/-- The sender and last-processor controls have no nondeterministic rows. -/
def rows : StackCode (Port r k) (Label p r k)
  | .enter mode last => .goto (if last then .done mode.halted else .write mode (serialize mode).body.entry)
  | .write mode q => ((serialize mode).body.code q).rename id (fun next => next.elim (.compare (.left true)) (.write mode))
  | .compare q => (compareCode q).rename cmpPorts cmpLabel
  | .done ok => .halt ok

/-- With no successor, a processor must have accepted. No guessed link or path choice
is introduced. -/
theorem last_run (mode : Mode p) (s : Stacks (Port r k)) :
    StackRuns rows 1 (.enter mode true) s (.done mode.halted) s :=
  .cons (.goto (by simp [rows])) (.nil ..)

/-- On a nonfinal processor exactly the computed frame passes the successor comparison.
The architecture, elapsed time, local probe stamp, and read cap are unaffected. -/
theorem successor_run (mode : Mode p) (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (l g elapsed max : Word w) (stamp raw : List Bool) :
    let core := banks pub s (chargeRegisters l g elapsed 0) max stamp
    let f := frame mode s.reg elapsed
    ∃ out : Stacks (Port r k), StackRuns rows
      ((2*(8*w+3)+(r+2)*(5*w+2)+2) + (2*min (1+(r+2)*w) raw.length+2)+1)
      (.enter mode false) (bank core [] raw) (.done (decide (f.bits=raw))) out ∧
      ∀ j, out (.clock j) = core j := by
  intro core f
  let label (u : Option (serialize (r := r) (k := k) mode).State) : Label p r k :=
    u.elim (.compare (.left true)) (.write mode)
  have r₁ := (serialize_run mode pub s l g elapsed max stamp raw).lift id Function.injective_id label
    (bank core [] raw) (target := rows) (by
      rintro (_ | q) h
      · contradiction
      · rfl)
  have hi (u : Stacks (Port r k)) : installStacks id (bank core [] raw) u = u :=
    funext fun j => installStacks_at Function.injective_id _ _ j
  rw [hi, hi] at r₁
  obtain ⟨t, rt⟩ := outgoing_checked f raw
  have hinj : Function.Injective (cmpPorts (r := r) (k := k)) := by intro x y h; cases x <;> cases y <;> first | rfl | contradiction
  let b := bank core f.bits raw
  have r₂ := rt.lift cmpPorts hinj (cmpLabel (p := p)) b (target := rows (p := p)) (by
    intro q h; cases q <;> rfl)
  have hb : installStacks cmpPorts b (streams f.bits raw) = b :=
    installStacks_eq hinj _ _ (by intro j; cases j <;> rfl)
  rw [hb] at r₂
  refine ⟨_, .cons (.goto (by simp [rows, label])) (r₁.trans r₂), ?_⟩
  intro j
  rw [installStacks_outside (hl := fun a => by cases a <;> simp [cmpPorts])]
  rfl

/-- Acceptance of an arbitrary outgoing link by the actual finish routine
determines the exact canonical frame generated from the physical register bank. -/
theorem successor_accept_iff (mode : Mode p) (pub : Fin k → Word w) (s : PrivateRAM.LogConfig w p r)
    (l g elapsed max : Word w) (stamp raw : List Bool) :
    let core := banks pub s (chargeRegisters l g elapsed 0) max stamp
    (∃ t out, StackRuns rows t (.enter mode false) (bank core [] raw) (.done true) out) ↔
      (frame mode s.reg elapsed).bits = raw := by
  intro core
  obtain ⟨st, run, _⟩ := successor_run mode pub s l g elapsed max stamp raw
  constructor
  · rintro ⟨t, out, h⟩
    let bound := (2*(8*w+3)+(r+2)*(5*w+2)+2) + (2*min (1+(r+2)*w) raw.length+2)+1
    have a := h.paths (bound+1)
    have b := run.paths (t+1)
    rw [show bound+1+t = t+1+bound by omega, b] at a
    simpa [stackPaths, rows] using a
  · intro he
    exact ⟨_, _, by simpa only [he, decide_true] using run⟩

end TeamLocalClock.Finish

end BorderVNP
end Computability
end OAI
