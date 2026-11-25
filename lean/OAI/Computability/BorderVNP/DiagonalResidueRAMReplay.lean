import OAI.Computability.BorderVNP.DiagonalResidueRAMEvaluate

/-!
# Uniqueness of the residue reader on ordinary binary choices

An ordinary branch consumes exactly one bit; arithmetic and memory probes
consume none. Two terminating paths whose flattened tapes extend to the same
word consequently agree in every event, register and memory write.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM RoutingISA

variable {w : ℕ} {S : Type*}

/-- A native instruction does not call a private machine with a separate choice tape. -/
def ordinary (i : TeamRAM.Instr w S) : Bool :=
  match i with
  | .call .. => false
  | _ => true

private theorem guess_agrees (i : TeamRAM.Instr w S) (h : ordinary i = true)
    {bs cs rest rest' : List Bool} {old : List (Word w)} {v v' : S × TeamRAM.Sign}
    (hb : i.advance bs old = some v) (hc : i.advance cs old = some v')
    (ht : bs ++ rest = cs ++ rest') : bs = cs := by
  cases i with
  | accept | reject => contradiction
  | call => contradiction
  | localStep | load | store =>
    cases bs <;> cases cs <;> first | rfl | contradiction
  | choose f =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        cases bs <;> cases cs <;> first | contradiction | simpa using (List.cons.inj ht).1

/-- Native execution without private calls has at most one terminating trace
compatible with a given extended stream of binary guesses. -/
theorem native_unique {P : S → TeamRAM.Instr w S} (ordinaryTable : ∀ s, ordinary (P s) = true)
    {s m es t mt} (a : NativePrefix P s m es t mt) (endA : P t = .accept)
    {fs z mz} (b : NativePrefix P s m fs z mz) (endB : P z = .accept)
    {tail tail' : List Bool}
    (shared : es.flatMap TeamRAM.Event.choices ++ tail = fs.flatMap TeamRAM.Event.choices ++ tail') :
    es = fs ∧ t = z ∧ mt = mz := by
  induction a generalizing fs z mz tail tail' with
  | nil =>
    cases b with
    | nil => exact ⟨rfl,rfl,rfl⟩
    | cons ha _ _ => simp [endA,TeamRAM.Instr.action] at ha
  | @cons s m act bits next sign rs t mt ha hs _ ih =>
    cases b with
    | nil => simp [endB,TeamRAM.Instr.action] at ha
    | @cons _ _ act' bits' next' sign' rs' _ _ ha' hs' run' =>
      have he := Option.some.inj (ha.symm.trans ha')
      subst act'
      simp only [List.flatMap_cons, List.append_assoc] at shared
      obtain rfl := guess_agrees (P s) (ordinaryTable s) hs hs' shared
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (hs.symm.trans hs'))
      obtain ⟨rfl,rfl,rfl⟩ := ih endA run' endB (List.append_cancel_left shared)
      exact ⟨rfl,rfl,rfl⟩

/-- An execution of a whole structured program ends at the last native PC
with the very same post-state. -/
theorem at_last {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (r : Runs pub macros c s m es t mt) :
    NativePrefix (c.program.fetch pub macros) ⟨0,s⟩ m es ⟨Fin.last c.slots,t⟩ mt := by
  let lab (i : ℕ) : Fin (c.slots+1) := ⟨min i c.slots, by omega⟩
  have hc : Contains c.row lab 0 c.slots c := by
    intro i _ hi
    have hlt : i < c.slots := by omega
    simp [lab, Code.row, min_eq_left hlt.le, hlt]
  have h := r.nativePrefix c.row lab hc
  rw [show fetch c.row pub macros = c.program.fetch pub macros by funext q; exact fetch_row c pub macros q] at h
  simpa only [show lab 0 = 0 by ext; simp [lab], show lab c.slots = Fin.last c.slots by ext; simp [lab]] using h

/-- For an all-ordinary opcode table, structured returns on compatible guess
streams agree, including final registers. -/
theorem unique_returns {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} (h : ∀ pc, c.program.tag pc = .native)
    {s m es t mt} (a : Runs pub macros c s m es t mt)
    {fs z mz} (b : Runs pub macros c s m fs z mz) {tail tail' : List Bool}
    (shared : es.flatMap TeamRAM.Event.choices ++ tail = fs.flatMap TeamRAM.Event.choices ++ tail') :
    es = fs ∧ t = z ∧ mt = mz := by
  have ordinaryTable (q) : ordinary (c.program.fetch pub macros q) = true := by
    simp only [TeamOpcode.Program.fetch,h]
    split
    · cases ((c.program.base.code q.pc).resize w).runLogged pub q.logged <;> simp [TeamOpcode.nativeAction,ordinary]
      rename_i result
      cases result <;> rfl
    · rfl
  obtain ⟨he, hs, hm⟩ := native_unique ordinaryTable (at_last a) (c.fetch_finish pub macros t)
    (at_last b) (c.fetch_finish pub macros z) shared
  exact ⟨he,congrArg TeamOpcode.State.reg hs,hm⟩

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
