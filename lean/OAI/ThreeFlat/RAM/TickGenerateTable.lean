import OAI.ThreeFlat.RAM.ExpressionScan

namespace OAI
/-! # Relocatable native table for bounded comparison-record generation -/

namespace ThreeFlat.RAM.TickGenerateTable

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan

variable {w k p r : ℕ} (e : Term w k 1)

def driver (loc : Fin (e.labels+6) → Fin p) (i : Fin 6) := loc (Fin.natAdd e.labels i)
def desc (loc : Fin (e.labels+6) → Fin p) (i : Fin e.labels) := loc (i.castAdd 6)
def regs (reg : Fin (4+e.binds) ↪ Fin r) := (Fin.castAddEmb e.binds).trans reg
def temp (reg : Fin (4+e.binds) ↪ Fin r) := (Fin.natAddEmb 4).trans reg

def labels (loc : Fin (e.labels+6) → Fin p) (exit : Fin p) : Labels p :=
  ⟨driver e loc 3, desc e loc e.first,driver e loc 4,driver e loc 5,exit⟩

def prologue (start stop : Word w) (P : Fin 6 → Fin p) (R : Fin 4 → Fin r)
    (loop exit : Fin p) : Fin 6 → Instr w p r k
  | 0 => .constant (R 0) start (P 1)
  | 1 => .constant (R 1) stop (P 2)
  | 2 => .constant (R 3) 1 (P 3)
  | 3 => .jumpLt (R 0) (R 1) loop exit
  | 4 => .writeExternal (R 0) (R 2) (P 5)
  | _ => .binary .add (R 0) (R 0) (R 3) (P 3)

/-- Expression instructions are followed by the six native setup/scan rows.
The register bank has four persistent scan registers and one per expression bind. -/
def emit (start stop : Word w) (loc : Fin (e.labels+6) → Fin p)
    (reg : Fin (4+e.binds) ↪ Fin r) (exit : Fin p) : Fin (e.labels+6) → Instr w p r k :=
  Fin.addCases
    (e.emit (desc e loc) (fun _ => regs e reg 0) (temp e reg) (regs e reg 2) (driver e loc 4))
    (prologue start stop (driver e loc) (regs e reg) (desc e loc e.first) exit)

variable (M : Machine w p r k) (start stop : Word w) (loc : Fin (e.labels+6) → Fin p)
    (reg : Fin (4+e.binds) ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (loc i) = emit e start stop loc reg exit i)

include rom in
theorem installed_driver (i : Fin 6) : M.code (driver e loc i) =
    prologue start stop (driver e loc) (regs e reg) (desc e loc e.first) exit i := by
  simpa only [driver,emit,Fin.addCases_right] using rom (Fin.natAdd e.labels i)

include rom in
theorem installed_desc (i : Fin e.labels) : M.code (desc e loc i) =
    e.emit (desc e loc) (fun _ => regs e reg 0) (temp e reg) (regs e reg 2) (driver e loc 4) i := by
  simpa only [desc,emit,Fin.addCases_left] using rom (i.castAdd 6)

theorem fresh (i : Fin 4) (j : Fin e.binds) : regs e reg i ≠ temp e reg j := by
  intro h
  have h' := congrArg Fin.val (reg.injective h)
  change i.val = 4+j.val at h'
  omega

include rom in
theorem installed : Installed M (regs e reg) (labels e loc exit) := by
  constructor
  · exact installed_driver e M start stop loc reg exit rom 3
  · exact installed_driver e M start stop loc reg exit rom 4
  · exact installed_driver e M start stop loc reg exit rom 5

def boot (P : Fin 6 → Fin p) (R : Fin 4 → Fin r) (start stop : Word w) (c : Config w p r) :=
  ((c.put (P 1) (R 0) start).put (P 2) (R 1) stop).put (P 3) (R 3) 1

include rom in
/-- Running the physical ROM at any injected start label emits one interval
and reaches the caller's continuation. No initial register preconditions are needed. -/
theorem generate (n : ℕ) (span : start.val+n = stop.val) (word : ℕ → Word w)
    (c : Config w p r) (m : Memory w) (entry : c.pc = driver e loc 0)
    (correct : ∀ (x : Word w) (m' : Memory w), start.val ≤ x.val → x.val < stop.val →
      agreesOutside start.val stop.val m' m → e.eval M.publicData m' (fun _ => x) = word x.val) :
    ∃ steps ≤ 4+n*(e.steps+3), ∃ out : Config w p r, out.pc = exit ∧
      advance M.program steps c m = some (out,fillSegment start.val n word m) := by
  let R := regs e reg
  let P := driver e loc
  let L := labels e loc exit
  let begin := boot P R start stop c
  have rb := installed_driver e M start stop loc reg exit rom
  have setup : advance M.program 3 c m = some (begin,m) := by
    simp only [advance,Machine.program,entry,rb,prologue,Instr.run,boot,P,R,begin,
      Config.put]
  have z : begin.reg (R 0) = start := by
    simp [begin,boot,Config.put, R.injective.eq_iff,Function.update]
  have o : begin.reg (R 1) = stop := by
    simp [begin,boot,Config.put, R.injective.eq_iff,Function.update]
  have inv : scanInvariant R start.val stop.val m begin m :=
    ⟨Config.put_same .., by rw [z], by rw [o], fun _ _ => rfl⟩
  have bd := describes_expression M R L e (desc e loc) (temp e reg) (fresh e reg)
    rfl (installed_desc e M start stop loc reg exit rom) start.val stop.val m word correct
  obtain ⟨s,hs,out,pcok,run⟩ := DescriptorScan.generate M R L
    (installed e M start stop loc reg exit rom) e.steps word _ bd n begin m rfl inv
    (by rw [z,o]; exact span)
  refine ⟨3+s,by omega,out,pcok,?_⟩
  rw [z] at run
  exact advance_trans setup run

end ThreeFlat.RAM.TickGenerateTable

end OAI
