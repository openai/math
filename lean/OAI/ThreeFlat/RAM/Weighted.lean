import OAI.Computability.VPVNP.RAMProgram
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Nodup

namespace OAI
/-! # Weighted path semantics for the bounded word RAM

A returning instruction contributes the scalar encoded by its output word. The
two continuations of a binary choice contribute separately, even when their
program counters agree. The reports retain the actual choices and all probes.
-/

namespace ThreeFlat.RAM

open Computability.VPVNP.BurstRAM PrivateRAM

/-- The fixed field's elements occupy a subset of the machine words. -/
structure FieldCode (F : Type*) (w : ℕ) where
  encode : F → Word w
  decode : Word w → F
  decode_encode : ∀ x, decode (encode x) = x

/-- One-word encoding of any finite field fitting in the address width. Words
outside the encoding denote zero. -/
noncomputable def FieldCode.ofCardLe {F : Type*} [Fintype F] [Zero F] {w : ℕ}
    (h : Fintype.card F ≤ 2 ^ w) : FieldCode F w where
  encode x := ((Fintype.equivFin F) x).castLE h
  decode a := if ha : a.val < Fintype.card F then (Fintype.equivFin F).symm ⟨a.val, ha⟩ else 0
  decode_encode x := by simp

@[simp] theorem FieldCode.encode_val_ofCardLe {F : Type*} [Fintype F] [Zero F] {w : ℕ}
    (h : Fintype.card F ≤ 2 ^ w) (x : F) :
    ((ofCardLe h).encode x).val = ((Fintype.equivFin F) x).val := rfl

theorem FieldCode.decode_of_card_le {F : Type*} [Fintype F] [Zero F] {w : ℕ}
    (h : Fintype.card F ≤ 2 ^ w) (x : Word w) (hx : Fintype.card F ≤ x.val) :
    (ofCardLe h).decode x = (0 : F) := by simp [ofCardLe, Nat.not_lt.mpr hx]

variable {F C : Type*} {w p r k : ℕ}

def FieldCode.terminal [One F] (code : FieldCode F w) : Option (Word w) → F
  | none => 1
  | some v => code.decode v

/-- All accepted native reports under the enforced instruction cap. -/
def reports (P : Program w C) : ℕ → C → Memory w → List (Report w)
  | 0, _, _ => []
  | f + 1, c, m =>
    match P.step c with
    | .localStep next => (reports P f next m).map (Report.prepend .tick)
    | .branch next =>
      (reports P f (next false) m).map (Report.prepend (.choice false)) ++
      (reports P f (next true) m).map (Report.prepend (.choice true))
    | .read a next => (reports P f (next (m a.val)) m).map (Report.prepend (.read a (m a.val)))
    | .write a v next => (reports P f next (writeMemory m a v)).map (Report.prepend (.write a v))
    | .finish result => [⟨[], result⟩]
    | .reject => []

/-- The path sum obtained by executing each opcode. -/
def mass [Semiring F] (code : FieldCode F w) (P : Program w C) : ℕ → C → Memory w → F
  | 0, _, _ => 0
  | f + 1, c, m =>
    match P.step c with
    | .localStep next => mass code P f next m
    | .branch next => mass code P f (next false) m + mass code P f (next true) m
    | .read a next => mass code P f (next (m a.val)) m
    | .write a v next => mass code P f next (writeMemory m a v)
    | .finish result => code.terminal result
    | .reject => 0

/-- Weighted value of a machine whose registers and private memory have their
standard zero initialization. The initial persistent word and external memory
are the inputs. -/
def value [Semiring F] (code : FieldCode F w) (M : Machine w p r k)
    (fuel : ℕ) (state : Word w) (memory : Memory w) : F :=
  mass code M.program fuel (M.program.start state) memory

theorem mass_eq_sum_reports [Semiring F] (code : FieldCode F w) (P : Program w C)
    (f : ℕ) (c : C) (m : Memory w) :
    mass code P f c m = ((reports P f c m).map (fun r => code.terminal r.result)).sum := by
  induction f generalizing c m with
  | zero => simp [mass, reports]
  | succ f ih =>
    cases h : P.step c <;>
      simp [mass, reports, h, List.map_map, Function.comp_def, Report.prepend, ih]

private theorem mem_reports_of_guessed {P : Program w C} {f c es out}
    (h : Guessed P f c es out) {m : Memory w} (hm : Correct m es) :
    (⟨es, out⟩ : Report w) ∈ reports P f c m := by
  induction h generalizing m with
  | done h => simp [reports, h]
  | step h _ ih =>
    simp only [reports, h, List.mem_map]
    exact ⟨_, ih hm, rfl⟩
  | @branch f c next b es r h _ ih =>
    simp only [reports, h, List.mem_append, List.mem_map]
    cases b with
    | false => exact Or.inl ⟨_, ih hm, rfl⟩
    | true => exact Or.inr ⟨_, ih hm, rfl⟩
  | read h _ ih =>
    obtain ⟨rfl, hm⟩ := hm
    simp only [reports, h, List.mem_map]
    exact ⟨_, ih hm, rfl⟩
  | write h _ ih =>
    simp only [reports, h, List.mem_map]
    exact ⟨_, ih hm, rfl⟩

/-- The reports are precisely the local opcode histories whose reads agree
with the initial external memory and all prior writes. -/
theorem mem_reports_iff (P : Program w C) (f : ℕ) (c : C) (m : Memory w) (out : Report w) :
    out ∈ reports P f c m ↔ Guessed P f c out.events out.result ∧ Correct m out.events := by
  constructor
  · induction f generalizing c m out with
    | zero => simp [reports]
    | succ f ih =>
      intro hr
      cases h : P.step c with
      | finish v =>
        simp [reports, h] at hr
        subst out
        exact ⟨.done h, trivial⟩
      | reject => simp [reports, h] at hr
      | localStep t =>
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (by simpa only [reports, h] using hr)
        obtain ⟨hg, hc⟩ := ih _ _ _ hs
        exact ⟨.step h hg, hc⟩
      | branch t =>
        simp only [reports, h, List.mem_append, List.mem_map] at hr
        obtain ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ := hr <;>
          obtain ⟨hg, hc⟩ := ih _ _ _ hs <;> exact ⟨.branch h hg, hc⟩
      | read a t =>
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (by simpa only [reports, h] using hr)
        obtain ⟨hg, hc⟩ := ih _ _ _ hs
        exact ⟨.read h hg, rfl, hc⟩
      | write a v t =>
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (by simpa only [reports, h] using hr)
        obtain ⟨hg, hc⟩ := ih _ _ _ hs
        exact ⟨.write h hg, hc⟩
  · rintro ⟨hg, hc⟩
    exact mem_reports_of_guessed hg hc

private theorem prepend_injective (e : Event w) :
    Function.Injective (Report.prepend e) := by
  rintro ⟨x,a⟩ ⟨y,b⟩ h
  simpa [Report.prepend] using h

/-- Enumerating the two branches separately gives each coherent history
exactly one contribution. -/
theorem reports_nodup (P : Program w C) (f : ℕ) (c : C) (m : Memory w) :
    (reports P f c m).Nodup := by
  induction f generalizing c m with
  | zero => simp [reports]
  | succ f ih =>
    cases h : P.step c with
    | finish _ | reject => simp [reports, h]
    | localStep t | read _ t | write _ _ t =>
      simpa only [reports, h] using (ih _ _).map (prepend_injective _)
    | branch next =>
      simp only [reports, h, List.nodup_append]
      refine ⟨(ih _ _).map (prepend_injective _), (ih _ _).map (prepend_injective _), ?_⟩
      intro a ha b hb
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
      simp [Report.prepend]

theorem mem_reports_iff_execute (P : Program w C) (f : ℕ) (c : C) (m : Memory w) (out : Report w) :
    out ∈ reports P f c m ↔ execute P f c m (choiceBits out.events) = some out := by
  rw [mem_reports_iff, execute_iff]
  simp

end ThreeFlat.RAM

end OAI
