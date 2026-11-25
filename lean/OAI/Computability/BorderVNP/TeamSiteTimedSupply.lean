import OAI.Computability.BorderVNP.TeamSiteTimedMacro
import OAI.Computability.BorderVNP.TeamSiteSupplyChunk

/-! # Chronological branch supplies for a trusted-clock native site

For a fixed budget the native remaining marks can be recorded in a finite control.
This description is used for the RAM transcript alone. The physical program has
a fixed control and represents those marks on its initialized clock tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedSupply

open VPVNP VPVNP.RAMTape VPVNP.BurstRAM TeamPrivateTape TeamPrivateFragment
open TeamPrivateValue TeamPrivateTimeout TeamPrivateCall TeamSiteChoices

variable {Q Γ : Type} {m g w : ℕ}

/-- Store the decremented finite counter in the successor control while keeping
every write and tape motion of the native command. -/
def step {N : ℕ} (left : Fin (N+1)) (c : TapeCommand Q Γ m) : TapeCommand (Fin (N+1) × Q) Γ m :=
  ⟨(⟨left.val-1,(Nat.sub_le ..).trans_lt left.isLt⟩,c.next),c.write,c.direction⟩

/-- The auxiliary finite-control table inspects the original halt before it tests
for an exhausted clock. -/
def table (N : ℕ) (P : TapeTable Q Γ m) : TapeTable (Fin (N+1) × Q) Γ m := fun st heads =>
  match P st.2 heads with
  | .halt a s => .halt a s
  | .one c => if st.1.val = 0 then .halt false false else .one (step st.1 c)
  | .two l r => if st.1.val = 0 then .halt false false else .two (step st.1 l) (step st.1 r)

/-- Reindex a natural counter bounded by the initial budget. -/
private abbrev count {N : ℕ} (n : ℕ) (h : n ≤ N) : Fin (N+1) := ⟨n,Nat.lt_succ_of_le h⟩

private theorem step_apply {N : ℕ} (left : Fin (N+1)) (c : TapeCommand Q Γ m) (blank : Γ)
    (ts : Fin m → SymbolTape Γ) : (step left c).apply blank ts = c.apply blank ts := rfl

private theorem stop_at (N : ℕ) (P : TapeTable Q Γ m) (blank : Γ) (n : ℕ) (h : n ≤ N)
    (q : Q) (ts : Fin m → SymbolTape Γ) : TapeStops (table N P) blank (n+1) (count n h,q) ts := by
  induction n generalizing q ts with
  | zero => cases e : P q (fun i => (ts i).head) <;> simp [TapeStops,table,e]
  | succ n ih =>
    rw [TapeStops]
    cases e : P q (fun i => (ts i).head) with
    | halt a s => simp [table,e]
    | one c =>
      simp only [table,e,count, Nat.succ_ne_zero,↓reduceIte,step_apply]
      exact ih (by omega) c.next (c.apply blank ts)
    | two l r =>
      simp only [table,e,count, Nat.succ_ne_zero,↓reduceIte,step_apply]
      exact ⟨ih (by omega) l.next (l.apply blank ts),ih (by omega) r.next (r.apply blank ts)⟩

/-- The auxiliary table and the physical timed table return exactly the same
three-valued result on every bit spelling, also at malformed bursts and timeout. -/
theorem symbol_eval (N : ℕ) (P : TapeTable Q Γ m) (blank mark : Γ) (hm : blank ≠ mark)
    (n : ℕ) (h : n ≤ N) (q : Q) (left : List Γ) (ts : Fin m → SymbolTape Γ) (bits : List Bool) :
    symbolEval (table N P) blank (n+1) (count n h,q) ts bits =
      symbolEval (TeamPrivateTimeout.table blank mark P) blank (n+1) q
        (timedTapes blank mark left n ts) bits := by
  have heads (u : ℕ) (left' : List Γ) (zs : Fin m → SymbolTape Γ) :
      (fun i : Fin m => (timedTapes blank mark left' u zs i.succ).head) = fun i => (zs i).head :=
    funext fun i => by simp [timedTapes]
  induction n generalizing q left ts bits with
  | zero =>
    cases e : P q (fun i => (ts i).head) <;>
      simp only [symbolEval,table,TeamPrivateTimeout.table,e,↓reduceIte,
        timedTapes,Fin.cons_zero,Fin.cons_succ,meter,hm]
  | succ n ih =>
    have head : (timedTapes blank mark left (n+1) ts 0).head = mark := by simp [timedTapes,meter]
    rw [symbolEval.eq_2,symbolEval.eq_2]
    simp only [table,TeamPrivateTimeout.table,heads,head,↓reduceIte]
    cases e : P q (fun i => (ts i).head) with
    | halt a s => rfl
    | one c =>
      simp only [count,Nat.succ_ne_zero,↓reduceIte,step_apply,TeamPrivateTimeout.command_apply]
      exact ih (by omega) c.next (blank::left) (c.apply blank ts) bits
    | two l r =>
      cases bits with
      | nil => simp [count]
      | cons b tail =>
        cases b <;> simp only [count,Nat.succ_ne_zero,↓reduceIte,step_apply,
          Bool.false_eq_true,TeamPrivateTimeout.command_apply]
        · exact ih (by omega) l.next (blank::left) (l.apply blank ts) tail
        · exact ih (by omega) r.next (blank::left) (r.apply blank ts) tail

/-- Finite-control description used to obtain chronological event lists at a fixed
length. Its code is independent of the choices and RAM contents. -/
def shadow (N : ℕ) (M : TeamSite.Macro Q Γ m g) : TeamSite.Macro (Fin (N+1) × Q) Γ m g where
  alphabet := M.alphabet
  digit := M.digit
  inputTape := M.inputTape
  table := table N M.table
  start := (count N le_rfl,M.start)

/-- Every possible private input and branch obeys the charged clock of the
auxiliary native description, including all malformed strings. -/
theorem shadow_bounded (N : ℕ) (M : TeamSite.Macro Q Γ m g) (vs : List (Word w)) :
    (shadow N M).bounded (N+1) vs :=
  stop_at N M.table M.alphabet.blank N le_rfl M.start _

/-- Replace the finite-control branch evaluator by the genuine independently
initialized timed macro on exactly the same consecutive words and choice bits. -/
theorem shadow_eval (N : ℕ) (M : TeamSite.Macro Q Γ m g) (mark : Γ)
    (hm : M.alphabet.blank ≠ mark) (vs : List (Word w)) (bits : List Bool) :
    (shadow N M).eval (N+1) vs bits = M.timedEval mark N vs bits := by
  let ts := input M.alphabet.blank M.digit M.inputTape (inputBits vs)
  have raw := symbolEval_tracks M.alphabet (table N M.table) (N+1) (count N le_rfl,M.start) ts bits
  have timed := symbolEval_tracks M.alphabet (TeamPrivateTimeout.table M.alphabet.blank mark M.table)
    (N+1) M.start (M.timedSymbols mark N vs) bits
  have eq := raw.trans ((symbol_eval N M.table M.alphabet.blank mark hm N le_rfl M.start [] ts bits).trans timed.symm)
  simpa only [Macro.eval,Macro.timedEval,Macro.timedInitial,Macro.timedTable,Macro.initial,
    shadow,ts,Option.map_map,Function.comp_def] using congrArg (Option.map sign) eq

/-- The RAM instruction semantics agree at every control state and every path
spelling. This transfers native supply witnesses without changing the events. -/
theorem macros_eq {a : ℕ} (lib : Fin a → TeamSite.Macro Q Γ m g) (mark : Fin a → Γ)
    (hm : ∀ j, (lib j).alphabet.blank ≠ mark j) (N : ℕ) :
    TeamSiteEvents.macros (w:=w) (fun j => shadow N (lib j)) (N+1) =
      fun j => (lib j).timedEval (mark j) N := by
  funext j vs bs
  exact shadow_eval N (lib j) (mark j) (hm j) vs bs

/-- Every infinite supply produces a genuine bounded chronological history for
the actual timed RAM. It returns its exact finite choice prefix and final guard
witness, including the reason for a failed range check. -/
theorem exists_history {p r k a : ℕ} (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (mark : Fin a → Γ)
    (hm : ∀ j, (lib j).alphabet.blank ≠ mark j) (N : ℕ)
    (s : TeamOpcode.State w p r) (c : Window w) (u : Supply) (safe : c.Safe) :
    ∃ es z fin v, Chunk (P.fetch pub (fun j => (lib j).timedEval (mark j) N)) s c es z fin ∧
      TeamSiteEvents.Prefix u (chunkBits es) ∧
      SupplyRun.Run P pub (fun j => shadow N (lib j)) (N+1) z fin
        (drop u (chunkBits es).length) [] z fin v := by
  obtain ⟨es,z,fin,v,h⟩ := SupplyRun.exists_run P pub (fun j => shadow N (lib j)) (N+1)
    s c u safe (fun j vs _ => shadow_bounded N (lib j) vs)
  exact ⟨es,z,fin,v,macros_eq lib mark hm N ▸ h.chunk,h.prefix,h.stopped⟩

end TeamSite.TimedSupply

end BorderVNP
end Computability
end OAI
