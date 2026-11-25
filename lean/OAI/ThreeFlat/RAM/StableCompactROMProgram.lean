import OAI.ThreeFlat.RAM.StableCompactROMDecode
import OAI.ThreeFlat.RAM.StableCompactROMAccess

namespace OAI
/-! # A single native public-memory program for every stable-compaction width -/

namespace ThreeFlat.RAM.StableCompactROMProgram

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w k : ℕ}

private def loadAt (l : ℕ) : Term w k 4 := (.binary .add (.result 0) (.literal (l : Word w)) : Term w k 4).load

/-- Registers hold the address of the descriptor triple, site, padded width, and logical width. -/
private def fetch : Term w k 4 :=
  decodeProgram.instantiate ![loadAt 0, loadAt 1, loadAt 2, .result 1, .result 2, .result 3]

/-- Four registers hold the four-word row key, the padded and logical widths, and ROM base.
The machine reads three ROM words irrespective of the width and number of local rows. -/
def program : Term w k 4 := fetch.instantiate ![pointerProgram,siteProgram,.result 1,.result 2]

theorem program_binds : (program (w:=w) (k:=k)).binds ≤ 56 := by
  have dec := decodeProgram_binds (w:=w) (k:=k)
  have coord := pointerProgram_binds (w:=w) (k:=k)
  simp [program,fetch,loadAt,Term.load,Term.binary,Term.literal,Term.binds,Fin.sum_univ_succ,siteProgram_binds]
  omega

theorem program_labels : (program (w:=w) (k:=k)).labels ≤ 169 := by
  rw [Term.labels_eq]
  have := program_binds (w:=w) (k:=k)
  omega

theorem program_steps : (program (w:=w) (k:=k)).steps ≤ 113 := by
  rw [Term.steps_eq]
  have := program_binds (w:=w) (k:=k)
  omega

theorem program_regs : (program (w:=w) (k:=k)).regCount ≤ 61 := by
  change 4 + ((program (w:=w) (k:=k)).binds + 1) ≤ 61
  have := program_binds (w:=w) (k:=k)
  omega

theorem program_eval (e : Entry) (N n base t v : ℕ) (j : Fin 4) (hn : n ≤ N)
    (hv : v < N) (four : 4 < 2^w) (sites : N < 2^w) (keyfit : 4*(t*N+v)+j.val < 2^w)
    (romfit : base+3*(4*t+j.val)+2 < 2^w) (fit : e.Fits w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 4 → Word w)
    (key : vs 0 = ((4*(t*N+v)+j.val : ℕ) : Word w)) (width : vs 1 = (N : Word w))
    (crop : vs 2 = (n : Word w)) (ptr : vs 3 = (base : Word w))
    (stored : ∀ l : Fin 3, mem (base+3*(4*t+j.val)+l.val) = (e.word l : Word w)) :
    program.eval words mem vs = (e.atSite N n v : Word w) := by
  obtain ⟨addr,sv⟩ := addresses_eval N base t v j hv four sites keyfit words mem vs key width ptr
  let env : Fin 4 → Word w := fun i => (![pointerProgram,siteProgram,.result 1,.result 2] i : Term w k 4).eval words mem vs
  have readCell (l : Fin 3) : (loadAt l.val).eval words mem env = (e.word l : Word w) := by
    have hfit : base+3*(4*t+j.val)+l.val < 2^w := by have := l.isLt; omega
    have pe : env 0 = ((base+3*(4*t+j.val) : ℕ) : Word w) := addr
    simp only [loadAt,Term.eval_load,Term.eval_binary,Term.eval_literal,Term.eval,pe,BinaryOp.eval,
      ← Nat.cast_add,Fin.val_cast_of_lt hfit,stored]
  simp only [program,Term.eval_instantiate]
  change fetch.eval words mem env = _
  rw [fetch,Term.eval_instantiate]
  exact decodeProgram_eval e N n v four (hn.trans_lt sites) (hv.trans sites) fit words mem _
    (readCell 0) (readCell 1) (readCell 2) sv width crop

end ThreeFlat.RAM.StableCompactROMProgram

end OAI
