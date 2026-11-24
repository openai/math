import OAI.Computability.VPVNP.PairSimulationMapConsistency

/-!
# A private directory scan comparing all incident selector fields

Each directory cell points to the beginning of a port's selector suffix.
The enclosing loop reads that pointer and compares the suffix to the same
anchor, carrying the difference mask across ports. The anchor and directory
may overlap any of the input fields because every memory access is a read.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapPortScan

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- The comparison loop uses the first seven of the directory scanner's registers. -/
def innerRegs (reg : Fin 11 ↪ Fin r) : Fin 7 ↪ Fin r := (Fin.castLEEmb (by decide)).trans reg

/-- Registers 7 through 10 hold the directory cursor, its exclusive end,
the first selector bit of the anchor, and the common selector length. -/
def instruction (pc : Fin 7 → Fin p) (reg : Fin 11 ↪ Fin r) (inner yes no : Fin p) :
    Fin 7 → Instr w p r k :=
  ![.jumpEq (reg 7) (reg 8) (pc 5) (pc 1),
    .loadPrivate (reg 0) (reg 7) (pc 2), .binary .add (reg 1) (reg 0) (reg 10) (pc 3),
    .copy (reg 2) (reg 9) inner, .binary .add (reg 7) (reg 7) (reg 3) (pc 0),
    .constant (reg 5) 0 (pc 6), .jumpEq (reg 4) (reg 5) yes no]

theorem resize_instruction (pc : Fin 7 → Fin p) (reg : Fin 11 ↪ Fin r) (inner yes no : Fin p)
    (i : Fin 7) :
    (instruction (w := 1) (k := k) pc reg inner yes no i).resize w =
      instruction pc reg inner yes no i := by
  fin_cases i <;> rfl

/-- The fixed outer code invokes the same inner loop for every directory entry. -/
structure Linked (M : Machine w p r k) (pc inner : Fin 7 → Fin p) (reg : Fin 11 ↪ Fin r)
    (yes no : Fin p) : Prop where
  outer : ∀ i, M.code (pc i) = instruction pc reg (inner 0) yes no i
  body : MapConsistency.Linked M inner (innerRegs reg) (pc 4)

/-- The port-directory scan writes the directory cursor and six inner-loop registers. -/
def Preserved (reg : Fin 11 ↪ Fin r) (a : Fin r) : Prop :=
  a ≠ reg 0 ∧ a ≠ reg 1 ∧ a ≠ reg 2 ∧ a ≠ reg 4 ∧ a ≠ reg 5 ∧ a ≠ reg 6 ∧ a ≠ reg 7

/-- All words of every selected slice equal the corresponding words of the anchor. -/
def Agrees (mem : Word w → Word w) (dir anchor : Word w) (ports width : ℕ) : Prop :=
  ∀ i : Fin ports, ∀ j : Fin width,
    mem (mem (dir + (i.val : Word w)) + (j.val : Word w)) = mem (anchor + (j.val : Word w))

instance (mem : Word w → Word w) (dir anchor : Word w) (ports width : ℕ) :
    Decidable (Agrees mem dir anchor ports width) := inferInstanceAs (Decidable (∀ _, ∀ _, _))

variable {M : Machine w p r k} {pc inner : Fin 7 → Fin p} {reg : Fin 11 ↪ Fin r} {yes no : Fin p}

private theorem step_at (hl : Linked M pc inner reg yes no) (i : Fin 7) {c : Config w p r}
    (hc : c.pc = pc i) :
    M.program.step c = (instruction pc reg (inner 0) yes no i).run M.publicData c := by
  simp [Machine.program, hc, hl.outer i]

private theorem onePort (hl : Linked M pc inner reg yes no) (width : ℕ) (c : Config w p r)
    (hc : c.pc = pc 0) (hne : c.reg (reg 7) ≠ c.reg (reg 8))
    (hlen : c.reg (reg 10) = (width : Word w)) (hw : width < 2 ^ w) (h1 : c.reg (reg 3) = 1) :
    ∃ out, Prefix M c (List.replicate (7*width+6) .tick) out ∧ out.pc = pc 0 ∧
      out.reg (reg 7) = c.reg (reg 7) + 1 ∧
      (out.reg (reg 4) = 0 ↔ c.reg (reg 4) = 0 ∧ ∀ j : Fin width,
        c.privateMem (c.privateMem (c.reg (reg 7)) + (j.val : Word w)) =
          c.privateMem (c.reg (reg 9) + (j.val : Word w))) ∧
      (∀ a, Preserved reg a → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  let start := c.privateMem (c.reg (reg 7))
  let anchor := c.reg (reg 9)
  let c₁ := {c with pc := pc 1}
  let c₂ := c₁.put (pc 2) (reg 0) start
  let c₃ := c₂.put (pc 3) (reg 1) (start + (width : Word w))
  let q := c₃.put (inner 0) (reg 2) anchor
  have s₀ : M.program.step c = .localStep c₁ := by
    rw [step_at hl 0 hc]
    simp [instruction, Instr.run, hne, c₁]
  have s₁ : M.program.step c₁ = .localStep c₂ := step_at hl 1 rfl
  have s₂ : M.program.step c₂ = .localStep c₃ := by
    rw [step_at hl 2 rfl]
    change CallAction.localStep (c₂.put (pc 3) (reg 1) (c₂.reg (reg 0) + c₂.reg (reg 10))) = _
    simp [c₃, c₂, c₁, Config.put, hlen]
  have s₃ : M.program.step c₃ = .localStep q := by
    rw [step_at hl 3 rfl]
    change CallAction.localStep (c₃.put (inner 0) (reg 2) (c₃.reg (reg 9))) = _
    simp [q, c₃, c₂, c₁, Config.put, anchor]
  have setup : Prefix M c (List.replicate 4 .tick) q :=
    .tick s₀ (.tick s₁ (.tick s₂ (.tick s₃ (.nil _))))
  obtain ⟨d, scan, hd, _, _, mask, frame, hm, hp⟩ :=
    MapConsistency.compareArrays hl.body (fun i : Fin width ↦ c.privateMem (start+(i.val:Word w)))
      (fun i : Fin width ↦ c.privateMem (anchor+(i.val:Word w))) start anchor q rfl
      (by change q.reg (reg 0) = _; simp [q, c₃, c₂, Config.put])
      (by change q.reg (reg 1) = _; simp [q, c₃, Config.put])
      (by change q.reg (reg 2) = _; simp [q])
      (by change q.reg (reg 3) = _; simp [q, c₃, c₂, c₁, Config.put, h1]) hw
      (fun _ ↦ rfl) (fun _ ↦ rfl)
  have d3 : d.reg (reg 3) = 1 := by
    rw [frame] <;> simp [innerRegs, q, c₃, c₂, c₁, Config.put, h1]
  have d7 : d.reg (reg 7) = c.reg (reg 7) := by
    rw [frame] <;> simp [innerRegs, q, c₃, c₂, c₁, Config.put]
  let out := d.put (pc 0) (reg 7) (c.reg (reg 7) + 1)
  have last : M.program.step d = .localStep out := by
    rw [step_at hl 4 hd]
    change CallAction.localStep (d.put (pc 0) (reg 7) (d.reg (reg 7) + d.reg (reg 3))) = _
    rw [d7, d3]
  have finalStep : Prefix M d (List.replicate 1 .tick) out := .tick last (.nil _)
  refine ⟨out, ?_, rfl, by simp [out], ?_, ?_, hm, hp⟩
  · convert (setup.append scan).append finalStep using 1
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  · change d.reg (reg 4) = 0 ↔ _ at mask
    simpa [out, q, c₃, c₂, c₁, Config.put, innerRegs, start, anchor] using mask
  · rintro a ⟨h₀,h₁,h₂,h₄,h₅,h₆,h₇⟩
    change Function.update d.reg (reg 7) _ a = _
    rw [Function.update_of_ne h₇, frame]
    · simp [q, c₃, c₂, c₁, Config.put, Function.update_of_ne, h₀, h₁, h₂]
    all_goals assumption

/-- The loop walks the pointer table and branches to its declared success
or failure label. Its fixed trace length applies on malformed words too. -/
theorem run (hl : Linked M pc inner reg yes no) (ports width : ℕ) (dir anchor : Word w)
    (c : Config w p r) (hc : c.pc = pc 0) (hdir : c.reg (reg 7) = dir)
    (hend : c.reg (reg 8) = dir + (ports : Word w)) (ha : c.reg (reg 9) = anchor)
    (hlen : c.reg (reg 10) = (width : Word w)) (hn : ports < 2 ^ w) (hw : width < 2 ^ w)
    (h1 : c.reg (reg 3) = 1) :
    ∃ out, Prefix M c (List.replicate ((7*width+6)*ports+3) .tick) out ∧
      out.pc = (if c.reg (reg 4) = 0 ∧ Agrees c.privateMem dir anchor ports width
        then yes else no) ∧
      (∀ a, Preserved reg a → out.reg a = c.reg a) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction ports generalizing c dir with
  | zero =>
    have he : c.reg (reg 7) = c.reg (reg 8) := hdir.trans (by simpa using hend.symm)
    let q := {c with pc := pc 5}
    let d := q.put (pc 6) (reg 5) 0
    let out := {d with pc := if c.reg (reg 4) = 0 then yes else no}
    have s₀ : M.program.step c = .localStep q := by
      rw [step_at hl 0 hc]
      simp [instruction, Instr.run, he, q]
    have s₁ : M.program.step q = .localStep d := step_at hl 5 rfl
    have s₂ : M.program.step d = .localStep out := by
      rw [step_at hl 6 rfl]
      change CallAction.localStep
        {d with pc := if d.reg (reg 4) = d.reg (reg 5) then yes else no} = _
      simp [d, q, out, Config.put]
    refine ⟨out, .tick s₀ (.tick s₁ (.tick s₂ (.nil _))), by simp [out, Agrees], ?_, rfl, rfl⟩
    rintro a ⟨_,_,_,_,h₅,_,_⟩
    simp [out, d, q, Config.put, Function.update_of_ne h₅]
  | succ n ih =>
    have ne : c.reg (reg 7) ≠ c.reg (reg 8) := by
      rw [hdir, hend]
      intro h
      have hz : ((n+1 : ℕ) : Word w) = 0 := add_left_cancel (a := dir) (by simpa using h.symm)
      have hv := congrArg Fin.val hz
      change (n+1) % (2 ^ w) = 0 at hv
      rw [Nat.mod_eq_of_lt hn] at hv
      omega
    obtain ⟨d, pre, hd, cursor, mask, frame, hm, hp⟩ := onePort hl width c hc ne hlen hw h1
    obtain ⟨out, rest, ho, other, hm', hp'⟩ :=
      ih (dir+1) d hd (by rw [cursor, hdir])
        (by rw [frame, hend] <;> simp [Preserved, add_assoc, add_comm (1:Word w)])
        (by rw [frame, ha]; simp [Preserved])
        (by rw [frame, hlen]; simp [Preserved]) (by omega)
        (by rw [frame, h1]; simp [Preserved])
    refine ⟨out, ?_, ?_, fun a h ↦ (other a h).trans (frame a h), hm'.trans hm, hp'.trans hp⟩
    · convert pre.append rest using 1
      rw [← List.replicate_add]
      congr 1
      rw [Nat.mul_succ]
      omega
    · rw [ho]
      simp [mask, hm, hdir, ha, Agrees, Fin.forall_fin_succ, add_assoc, add_comm (1 : Word w),
        and_assoc]

end PairSimulation.MapPortScan

end VPVNP
end Computability
end OAI
