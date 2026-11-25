import OAI.ThreeFlat.RAM.PhysicalProcedure
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # Native reverse scatter of trace lanes into terminal lists

Five public words locate the destination vector, the root heads, the lane links, and
give the two counts. The scanner first zeros the heads, then visits the lanes in
decreasing order. Each push uses one link word and one head word. A nonzero pointer
encodes its lane index plus one.
-/

namespace Hierarchy.TraceIntervalScanner

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ContinuationLink PhysicalProcedure
open scoped Fin.CommRing

variable {w P R K lanes roots : ℕ}

/-- Follow at most the specified number of links. A bad pointer or a remaining
nonempty chain when the budget runs out is reported by `none`. -/
def decode (N n : ℕ) (m : Memory w) : ℕ → ℕ → Option (List (Fin n))
  | 0, p => if p = 0 then some [] else none
  | _ + 1, 0 => some []
  | fuel + 1, j + 1 =>
    if hj : j < n then (decode N n m fuel (m (N+j)).val).map (⟨j,hj⟩ :: ·) else none

/-- Physical linked-list representation of the indicated lane IDs. -/
def Chain (N : ℕ) (m : Memory w) : ℕ → List (Fin lanes) → Prop
  | p, [] => p=0
  | p, j::js => p=j.val+1 ∧ Chain N m (m (N+j.val)).val js

theorem Chain.read {N p fuel : ℕ} {m : Memory w} {xs : List (Fin lanes)}
    (h : Chain N m p xs) (bound : xs.length ≤ fuel) : decode N lanes m fuel p = some xs := by
  induction xs generalizing p fuel with
  | nil =>
    change p = 0 at h
    subst p
    cases fuel <;> rfl
  | cons j js ih =>
    obtain ⟨rfl, tail⟩ := h
    cases fuel with
    | zero => simp at bound
    | succ fuel =>
      simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
      simp [decode, j.isLt, ih tail bound]

theorem chain_of_decode {N n fuel ptr : ℕ} {m : Memory w} {xs : List (Fin n)}
    (h : decode N n m fuel ptr = some xs) : Chain N m ptr xs := by
  induction fuel generalizing ptr xs with
  | zero =>
    by_cases hp : ptr=0
    · subst ptr
      simp [decode] at h
      subst xs
      rfl
    · simp [decode,hp] at h
  | succ fuel ih =>
    cases ptr with
    | zero =>
      simp [decode] at h
      subst xs
      rfl
    | succ j =>
      by_cases hj : j<n
      · cases e : decode N n m fuel (m (N+j)).val with
        | none => simp [decode,hj,e] at h
        | some ys =>
          simp [decode,hj,e] at h
          subst xs
          exact ⟨rfl,ih e⟩
      · simp [decode,hj] at h

private theorem Chain.congr_mem {N p : ℕ} {m o : Memory w} {xs : List (Fin lanes)}
    (h : Chain N m p xs) (same : ∀ j ∈ xs, o (N+j.val) = m (N+j.val)) : Chain N o p xs := by
  induction xs generalizing p with
  | nil => exact h
  | cons j js ih =>
    refine ⟨h.1, ?_⟩
    rw [same j (.head _)]
    exact ih h.2 fun k hk => same k (.tail _ hk)

/-- The pinned source and the two writable arrays may be separated by unused words. -/
structure Layout (w D H N lanes roots : ℕ) : Prop where
  beforeHeads : D+lanes ≤ H
  beforeLinks : H+roots ≤ N
  room : N+lanes < 2^w

def Loaded (D : ℕ) (dest : Fin lanes → Fin roots) (m : Memory w) : Prop :=
  ∀ j, m (D+j.val) = ((dest j).val : Word w)

def Frame (H N lanes roots : ℕ) (m o : Memory w) : Prop :=
  ∀ a, (a < H ∨ H+roots ≤ a) → (a < N ∨ N+lanes ≤ a) → o a = m a

def Output (H N : ℕ) (dest : Fin lanes → Fin roots) (m o : Memory w) : Prop :=
  Frame H N lanes roots m o ∧
    ∀ v, decode N lanes o lanes (o (H+v.val)).val =
      some ((List.finRange lanes).filter (fun j => dest j = v))

theorem Output.chain {H N : ℕ} {dest : Fin lanes → Fin roots} {m o : Memory w}
    (h : Output H N dest m o) (v : Fin roots) :
    Chain N o (o (H+v.val)).val ((List.finRange lanes).filter (fun j => dest j=v)) :=
  chain_of_decode (h.2 v)

private theorem Chain.ptr_bound {N ptr : ℕ} {m : Memory w} {xs : List (Fin lanes)}
    (h : Chain N m ptr xs) : ptr ≤ lanes := by
  cases xs with
  | nil =>
    change ptr=0 at h
    rw [h]
    exact Nat.zero_le _
  | cons q qs => rw [h.1]; exact q.isLt

private theorem Chain.next_bound {N ptr : ℕ} {m : Memory w} {xs : List (Fin lanes)}
    (h : Chain N m ptr xs) (sorted : xs.Pairwise (· < ·)) (q : Fin lanes) (inList : q ∈ xs) :
    (m (N+q.val)).val=0 ∨ q.val+1 < (m (N+q.val)).val ∧ (m (N+q.val)).val ≤ lanes := by
  induction xs generalizing ptr with
  | nil => cases inList
  | cons x xs ih =>
    obtain ⟨later, sortedTail⟩ := List.pairwise_cons.mp sorted
    rcases List.mem_cons.mp inList with eq | tail
    · subst x
      cases xs with
      | nil => exact Or.inl h.2
      | cons z zs =>
        have lt : q.val < z.val := later z (.head _)
        rw [h.2.1]
        exact Or.inr ⟨by omega, z.isLt⟩
    · exact ih h.2 sortedTail tail

/-- Every stored head is a representable one-based lane index or the zero sentinel. -/
theorem Output.head_bound {H N : ℕ} {dest : Fin lanes → Fin roots} {m o : Memory w}
    (h : Output H N dest m o) (v : Fin roots) : (o (H+v.val)).val ≤ lanes :=
  (h.chain v).ptr_bound

/-- The next pointer is either null or strictly larger than the current one-based
pointer. This applies to every lane because it lies in its own destination fiber. -/
theorem Output.link_monotone {H N : ℕ} {dest : Fin lanes → Fin roots} {m o : Memory w}
    (h : Output H N dest m o) (q : Fin lanes) :
    (o (N+q.val)).val=0 ∨ q.val+1 < (o (N+q.val)).val ∧ (o (N+q.val)).val ≤ lanes :=
  (h.chain (dest q)).next_bound ((List.pairwise_lt_finRange lanes).filter _) q (by simp)

private def bucket (dest : Fin lanes → Fin roots) (remaining : ℕ) (v : Fin roots) :=
  ((List.finRange lanes).drop remaining).filter (fun j => dest j = v)

private theorem bucket_cons (dest : Fin lanes → Fin roots) {j : ℕ} (hj : j<lanes) (v : Fin roots) :
    bucket dest j v = if dest ⟨j,hj⟩ = v then ⟨j,hj⟩ :: bucket dest (j+1) v
      else bucket dest (j+1) v := by
  have len : j < (List.finRange lanes).length := by simpa using hj
  unfold bucket
  rw [List.drop_eq_getElem_cons len]
  simp [List.filter_cons]

private theorem bucket_late (dest : Fin lanes → Fin roots) {j : ℕ} {v : Fin roots} {u : Fin lanes}
    (hu : u ∈ bucket dest j v) : j ≤ u.val := by
  have prior := (List.mem_filter.mp hu).1
  obtain ⟨a, ha, eq⟩ := List.mem_drop_iff_getElem.mp prior
  have := congrArg Fin.val eq
  simp at this
  omega

private def State (D H N : ℕ) (dest : Fin lanes → Fin roots) (left : ℕ) (m₀ m : Memory w) : Prop :=
  Loaded D dest m ∧ Frame H N lanes roots m₀ m ∧
    ∀ v, Chain N m (m (H+v.val)).val (bucket dest left v)

private def cleared (H roots : ℕ) (m : Memory w) : Memory w :=
  fun a => if H≤a ∧ a<H+roots then 0 else m a

private theorem initial_state {D H N : ℕ} (L : Layout w D H N lanes roots)
    (dest : Fin lanes → Fin roots) (m : Memory w) (loaded : Loaded D dest m) :
    State D H N dest lanes m (cleared H roots m) := by
  have ⟨dh,_,_⟩ := L
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h : D+j.val<H := by omega
    simpa [cleared, Nat.not_le.mpr h] using loaded j
  · intro a out _
    have h : ¬(H≤a ∧ a<H+roots) := by omega
    simp [cleared,h]
  · intro v
    have h : H≤H+v.val ∧ H+v.val<H+roots := by omega
    have empty : (List.finRange lanes).drop lanes = [] := List.drop_eq_nil_iff.mpr (by simp)
    simp [cleared, h, bucket, empty, Chain]

private def pushed (H N j v : ℕ) (m : Memory w) : Memory w :=
  Function.update (Function.update m (N+j) (m (H+v))) (H+v) ((j+1 : ℕ) : Word w)

private theorem push_state {D H N : ℕ} (L : Layout w D H N lanes roots)
    (dest : Fin lanes → Fin roots) {j : ℕ} (hj : j<lanes) (m₀ m : Memory w)
    (h : State D H N dest (j+1) m₀ m) :
    State D H N dest j m₀ (pushed H N j (dest ⟨j,hj⟩).val m) := by
  let v := dest ⟨j,hj⟩
  obtain ⟨dh, hn, room⟩ := L
  obtain ⟨load, frame, chains⟩ := h
  have hv : v.val < roots := v.isLt
  have ptr : (((j+1 : ℕ) : Word w)).val = j+1 := Fin.val_cast_of_lt (by omega)
  have stable (z : Fin roots) :
      Chain N (pushed H N j v.val m) (m (H+z.val)).val (bucket dest (j+1) z) := by
    apply (chains z).congr_mem
    intro u hu
    have := bucket_late dest hu
    simp [pushed, Function.update_of_ne (show N+u.val ≠ H+v.val by omega),
      Function.update_of_ne (show N+u.val ≠ N+j by omega)]
  change State D H N dest j m₀ (pushed H N j v.val m)
  refine ⟨?_, ?_, ?_⟩
  · intro u
    simpa [pushed, Function.update_of_ne (show D+u.val ≠ H+v.val by omega),
      Function.update_of_ne (show D+u.val ≠ N+j by omega)] using load u
  · intro a ha hb
    simpa [pushed, Function.update_of_ne (show a ≠ H+v.val by omega),
      Function.update_of_ne (show a ≠ N+j by omega)] using frame a ha hb
  · intro z
    rw [bucket_cons dest hj z]
    by_cases eq : v = z
    · subst z
      rw [ite_eq_left (show dest ⟨j,hj⟩ = v from rfl)]
      refine ⟨by simpa only [pushed, Function.update_self] using ptr, ?_⟩
      simpa [pushed, Function.update_of_ne (show N+j ≠ H+v.val by omega)] using stable v
    · rw [ite_eq_right eq]
      have ne : H+z.val ≠ H+v.val := fun x => eq (Fin.ext (by omega))
      have zlt := z.isLt
      have head : pushed H N j v.val m (H+z.val) = m (H+z.val) := by
        simp [pushed, Function.update_of_ne ne, Function.update_of_ne (show H+z.val ≠ N+j by omega)]
      rw [head]
      exact stable z

/-- Seven setup rows, four rows to clear one head, and ten rows to push one lane. -/
def rows (pc : Fin 21 ↪ Fin P) (r : Fin 11 ↪ Fin R) (pub : Fin 5 → Fin K) (exit : Fin P) :
    Fin 21 → Instr w P R K
  | 0 => .constant (r 0) 0 (pc 1)
  | 1 => .constant (r 1) 1 (pc 2)
  | 2 => .publicWord (r 2) (pub 0) (pc 3)
  | 3 => .publicWord (r 3) (pub 1) (pc 4)
  | 4 => .publicWord (r 4) (pub 2) (pc 5)
  | 5 => .publicWord (r 5) (pub 3) (pc 6)
  | 6 => .publicWord (r 6) (pub 4) (pc 7)
  | 7 => .jumpEq (r 5) (r 0) (pc 11) (pc 8)
  | 8 => .binary .sub (r 5) (r 5) (r 1) (pc 9)
  | 9 => .binary .add (r 8) (r 3) (r 5) (pc 10)
  | 10 => .writeExternal (r 8) (r 0) (pc 7)
  | 11 => .jumpEq (r 6) (r 0) exit (pc 12)
  | 12 => .copy (r 7) (r 6) (pc 13)
  | 13 => .binary .sub (r 6) (r 6) (r 1) (pc 14)
  | 14 => .binary .add (r 8) (r 2) (r 6) (pc 15)
  | 15 => .readExternal (r 9) (r 8) (pc 16)
  | 16 => .binary .add (r 10) (r 3) (r 9) (pc 17)
  | 17 => .readExternal (r 9) (r 10) (pc 18)
  | 18 => .binary .add (r 8) (r 4) (r 6) (pc 19)
  | 19 => .writeExternal (r 8) (r 9) (pc 20)
  | _ => .writeExternal (r 10) (r 7) (pc 11)

def data (w D H N lanes roots : ℕ) : Fin 5 → Word w
  | 0 => D
  | 1 => H
  | 2 => N
  | 3 => roots
  | 4 => lanes

def procedure (w D H N lanes roots : ℕ) : Procedure w where
  labels := 21
  registers := 11
  slots := 5
  block := ⟨0, fun pc r pub exit => rows pc r pub exit⟩
  publicData := data w D H N lanes roots

private structure Ready (r : Fin 11 ↪ Fin R) (c : Config w P R) (D H N rootsLeft lanesLeft : ℕ) :
    Prop where
  zero : c.reg (r 0) = 0
  one : c.reg (r 1) = 1
  dst : c.reg (r 2) = (D : Word w)
  heads : c.reg (r 3) = (H : Word w)
  links : c.reg (r 4) = (N : Word w)
  roots : c.reg (r 5) = (rootsLeft : Word w)
  lanes : c.reg (r 6) = (lanesLeft : Word w)

private theorem write_at (m : Memory w) (a : ℕ) (v : Word w) (fits : a < 2^w) :
    writeMemory m (a : Word w) v = Function.update m a v := by
  funext x
  by_cases h : x=a <;> simp [writeMemory, Fin.val_cast_of_lt fits, Function.update, h]

private theorem word_sub_one (j : ℕ) : ((j+1 : ℕ) : Word w) - 1 = (j : Word w) := by
  simp

private theorem word_ne_zero {n : ℕ} (fits : n+1<2^w) : ((n+1 : ℕ) : Word w) ≠ 0 := by
  intro h
  have hx := congrArg Fin.val h
  rw [Fin.val_cast_of_lt fits] at hx
  simp at hx

private theorem cleared_zero (H : ℕ) (m : Memory w) : cleared H 0 m = m := by
  funext a
  have h : ¬(H ≤ a ∧ a < H+0) := by omega
  simp only [cleared,ite_eq_right h]

private theorem clear_last (H j : ℕ) (m : Memory w) :
    cleared H j (Function.update m (H+j) 0) = cleared H (j+1) m := by
  funext a
  by_cases h : a=H+j
  · subst a
    simp [cleared]
  · by_cases small : H≤a ∧ a<H+j
    · simp [cleared,small, show H≤a ∧ a<H+(j+1) by omega]
    · simp [cleared,small,show ¬(H≤a ∧ a<H+(j+1)) by omega,Function.update_of_ne h]

section Execution

variable (M : Machine w P R K) (pc : Fin 21 ↪ Fin P) (r : Fin 11 ↪ Fin R)
  (pub : Fin 5 → Fin K) (exit : Fin P)
  (rom : ∀ i, M.code (pc i) = rows pc r pub exit i)

include rom in
private theorem init_run {D H N lanes roots : ℕ}
    (loaded : ∀ i, M.publicData (pub i) = data w D H N lanes roots i)
    (c : Config w P R) (m : Memory w) (start : c.pc=pc 0) :
    ∃ o, advance M.program 7 c m = some (o,m) ∧ o.pc=pc 7 ∧ Ready r o D H N roots lanes := by
  let o := ((((((c.put (pc 1) (r 0) 0).put (pc 2) (r 1) 1).put (pc 3) (r 2) D).put
    (pc 4) (r 3) H).put (pc 5) (r 4) N).put (pc 6) (r 5) roots).put (pc 7) (r 6) lanes
  refine ⟨o, ?_, rfl, ?_⟩
  · simp [advance, Machine.program, start, rom, rows, Instr.run, loaded, data, o, Config.put]
  · constructor <;> simp (config := {decide := true}) [o,Config.put,Function.update,r.injective.eq_iff]

include rom in
private theorem clear_one {D H N j lanes : ℕ} (c : Config w P R) (m : Memory w)
    (start : c.pc=pc 7) (ready : Ready r c D H N (j+1) lanes)
    (fit : H+j+1 < 2^w) :
    ∃ o, advance M.program 4 c m = some (o, Function.update m (H+j) 0) ∧
      o.pc=pc 7 ∧ Ready r o D H N j lanes := by
  let o := (c.put (pc 9) (r 5) j).put (pc 7) (r 8) (H+j : ℕ)
  have nz := word_ne_zero (w := w) (n := j) (by omega)
  refine ⟨o, ?_, rfl, ?_⟩
  · simp (config := {decide := true}) [advance,Machine.program,start,rom,rows,Instr.run,Config.put,
      Function.update,r.injective.eq_iff,BinaryOp.eval,ready.zero,ready.one,ready.heads,ready.roots,
      nz,word_sub_one,o,← Nat.cast_add,write_at m (H+j) 0 (by omega)]
  · constructor <;> simp (config := {decide := true}) [o,Config.put,Function.update,r.injective.eq_iff,
      ready.zero,ready.one,ready.dst,ready.heads,ready.links,ready.lanes]

include rom in
private theorem clear_run {D H N j lanes : ℕ} (c : Config w P R) (m : Memory w)
    (start : c.pc=pc 7) (ready : Ready r c D H N j lanes) (fit : H+j < 2^w) :
    ∃ o, advance M.program (4*j+1) c m = some (o,cleared H j m) ∧
      o.pc=pc 11 ∧ Ready r o D H N 0 lanes := by
  induction j generalizing c m with
  | zero =>
    refine ⟨{c with pc:=pc 11}, ?_, rfl, ready.zero, ready.one, ready.dst, ready.heads,
      ready.links, ready.roots, ready.lanes⟩
    simp [advance, Machine.program, start, rom, rows, Instr.run, ready.roots, ready.zero, cleared_zero]
  | succ j ih =>
    obtain ⟨o, run, atHead, good⟩ := clear_one M pc r pub exit rom c m start ready (by omega)
    obtain ⟨f, finish, finalpc, final⟩ := ih o (Function.update m (H+j) 0) atHead good (by omega)
    refine ⟨f, ?_, finalpc, final⟩
    rw [clear_last] at finish
    simpa only [show 4*(j+1)+1 = 4+(4*j+1) by omega] using advance_trans run finish

include rom in
private theorem push_one {D H N j : ℕ} (L : Layout w D H N lanes roots) (dest : Fin lanes → Fin roots)
    (hj : j<lanes) (c : Config w P R) (m : Memory w) (start : c.pc=pc 11)
    (ready : Ready r c D H N 0 (j+1)) (loaded : Loaded D dest m) :
    ∃ o, advance M.program 10 c m = some (o, pushed H N j (dest ⟨j,hj⟩).val m) ∧
      o.pc=pc 11 ∧ Ready r o D H N 0 j := by
  let v := (dest ⟨j,hj⟩).val
  have hv : v < roots := (dest ⟨j,hj⟩).isLt
  have dh := L.beforeHeads
  have hn := L.beforeLinks
  have room := L.room
  have nz := word_ne_zero (w:=w) (n:=j) (by omega)
  have dv : (((D+j : ℕ) : Word w)).val = D+j := Fin.val_cast_of_lt (by omega)
  have hd : (((H+v : ℕ) : Word w)).val = H+v := Fin.val_cast_of_lt (by omega)
  have ld : m (D+j) = (v : Word w) := loaded ⟨j,hj⟩
  let o := ((((((c.put (pc 13) (r 7) (j+1 : ℕ)).put (pc 14) (r 6) j).put
    (pc 15) (r 8) (D+j : ℕ)).put (pc 16) (r 9) v).put (pc 17) (r 10) (H+v : ℕ)).put
    (pc 18) (r 9) (m (H+v))).put (pc 11) (r 8) (N+j : ℕ)
  change ∃ o, _ = some (o, pushed H N j v m) ∧ _
  refine ⟨o, ?_, rfl, ?_⟩
  · simp (config := {decide := true}) [advance,Machine.program,start,rom,rows,Instr.run,Config.put,
      r.injective.eq_iff,BinaryOp.eval,ready.zero,ready.one,ready.dst,
      ready.heads,ready.links,ready.lanes,nz,word_sub_one,o,←Nat.cast_add,dv,hd,ld,pushed,
      write_at m (N+j) _ (by omega)]
    exact write_at _ (H+v) _ (by omega)
  · constructor <;> simp (config := {decide := true}) [o,Config.put,Function.update,r.injective.eq_iff,
      ready.zero,ready.one,ready.dst,ready.heads,ready.links,ready.roots]

include rom in
private theorem scatter_run {D H N j : ℕ} (L : Layout w D H N lanes roots)
    (dest : Fin lanes → Fin roots) (hj : j≤lanes) (m₀ : Memory w)
    (c : Config w P R) (m : Memory w) (start : c.pc=pc 11) (ready : Ready r c D H N 0 j)
    (inv : State D H N dest j m₀ m) :
    ∃ o m', advance M.program (10*j+1) c m = some (o,m') ∧ o.pc=exit ∧ Output H N dest m₀ m' := by
  induction j generalizing c m with
  | zero =>
    refine ⟨{c with pc:=exit},m, ?_, rfl, inv.2.1, ?_⟩
    · simp [advance,Machine.program,start,rom,rows,Instr.run,ready.zero,ready.lanes]
    · intro v
      have h := inv.2.2 v
      simp [bucket] at h
      exact h.read (by simpa using (List.length_filter_le (fun j => decide (dest j=v)) (List.finRange lanes)))
  | succ j ih =>
    obtain ⟨o,run,atHead,good⟩ := push_one M pc r pub exit rom L dest (by omega : j<lanes)
      c m start ready inv.1
    have next := push_state L dest (by omega : j<lanes) m₀ m inv
    obtain ⟨z,m',tail,stop,post⟩ := ih (by omega) o _ atHead good next
    refine ⟨z,m',?_,stop,post⟩
    simpa only [show 10*(j+1)+1=10+(10*j+1) by omega] using advance_trans run tail

end Execution

/-- Exact deterministic run from an arbitrary caller configuration at the block entry. -/
theorem advance_scanner {D H N : ℕ} (L : Layout w D H N lanes roots)
    (dest : Fin lanes → Fin roots) (M : Machine w P R K) (pc : Fin 21 ↪ Fin P)
    (r : Fin 11 ↪ Fin R) (pub : Fin 5 → Fin K) (exit : Fin P)
    (rom : ∀ i, M.code (pc i) = rows pc r pub exit i)
    (given : ∀ i, M.publicData (pub i) = data w D H N lanes roots i)
    (c : Config w P R) (m : Memory w) (start : c.pc=pc 0) (loaded : Loaded D dest m) :
    ∃ out mem, advance M.program (9+4*roots+10*lanes) c m = some (out,mem) ∧
      out.pc=exit ∧ Output H N dest m mem := by
  obtain ⟨a,runA,pcA,okA⟩ := init_run M pc r pub exit rom given c m start
  have hn := L.beforeLinks
  have room := L.room
  obtain ⟨b,runB,pcB,okB⟩ := clear_run M pc r pub exit rom a m pcA okA (by omega)
  obtain ⟨out,mem,runC,stop,post⟩ := scatter_run M pc r pub exit rom L dest le_rfl m b _
    pcB okB (initial_state L dest m loaded)
  refine ⟨out, mem, ?_, stop, post⟩
  rw [show 9+4*roots+10*lanes = (7+(4*roots+1))+(10*lanes+1) by omega]
  exact advance_trans (advance_trans runA runB) runC

/-- The linked native program clears the output heads, then constructs each sorted
compact terminal fiber. The destination array and all other exterior words are preserved. -/
theorem procedure_spec {D H N : ℕ} (L : Layout w D H N lanes roots) (dest : Fin lanes → Fin roots) :
    (procedure w D H N lanes roots).Spec (Loaded D dest) (Output H N dest) (9+4*roots+10*lanes) := by
  intro P R K M pc r pub exit installed given c m start loaded
  obtain ⟨out,mem,run,stop,post⟩ := advance_scanner L dest M pc r pub exit installed given c m start loaded
  exact ⟨_, le_rfl, out, mem, run, stop, post⟩

end Hierarchy.TraceIntervalScanner

end OAI
