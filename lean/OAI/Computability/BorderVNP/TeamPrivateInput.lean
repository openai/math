import OAI.Computability.BorderVNP.TeamPrivateRepresentation
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Loading a binary string onto the input tape of a private machine

The first pop supplies the scanned symbol. The loader reverses the remaining bits onto
scratch, then pops them in reverse order and pushes each digit onto the input tape's right
bit stacks. The two passes restore the original order and empty the scratch stack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateInput

open VPVNP.RAMTape TeamPrivateTape

variable {g m : ℕ} {Γ R : Type*}

/-- Ports touched by the input loader. Each lane is one right-neighbor stack. -/
inductive Port (g : ℕ)
  /-- Unconsumed binary input, first bit at the top. -/
  | raw
  /-- Holds the reversed tail while the loader fills the output lanes. -/
  | scratch
  /-- Right-neighbor bits of one symbol track of the selected input tape. -/
  | lane (j : Fin g)
  deriving DecidableEq, Fintype

/-- The first digit, the digit being distributed, and the bounded lane cursor are finite. -/
inductive State (g : ℕ)
  /-- Pop the initial scanned digit, including the empty-input case. -/
  | start
  /-- Read the next bit of the tail. -/
  | reverse (head : Option Bool)
  /-- Save one tail bit on the reversal stack. -/
  | stash (head : Option Bool) (b : Bool)
  /-- Read the next bit from the reversed tail. -/
  | take (head : Option Bool)
  /-- Push the encoded digit onto the remaining symbol tracks. -/
  | spread (head : Option Bool) (b : Bool) (j : Fin (g+1))
  /-- Return the original first digit to the simulator. -/
  | done (head : Option Bool)
  deriving Fintype

/-- Fixed elementary instructions for any binary-to-symbol encoding. -/
def code (enc : Bool → Fin g → Bool) : StackCode (Port g) (State g)
  | .start => .pop .raw .reverse
  | .reverse h => .pop .raw fun b => b.elim (.take h) (.stash h)
  | .stash h b => .push .scratch b (.reverse h)
  | .take h => .pop .scratch fun b => b.elim (.done h) (fun x => .spread h x 0)
  | .spread h b j => if hj : j.val < g then
      .push (.lane ⟨j.val, hj⟩) (enc b ⟨j.val, hj⟩) (.spread h b (⟨j.val, hj⟩ : Fin g).succ)
    else .goto (.take h)
  | .done _ => .halt false

/-- Raw stack, reversal scratch, and the right neighbors in each bit plane. -/
def store (raw scratch : List Bool) (lanes : Fin g → List Bool) : Stacks (Port g)
  | .raw => raw
  | .scratch => scratch
  | .lane j => lanes j

private theorem setRaw (x y : List Bool) (z : Fin g → List Bool) (w : List Bool) :
    Function.update (store x y z) .raw w = store w y z := by
  funext j; cases j <;> simp [store]

private theorem setScratch (x y : List Bool) (z : Fin g → List Bool) (w : List Bool) :
    Function.update (store x y z) .scratch w = store x w z := by
  funext j; cases j <;> simp [store]

private theorem setLane (x y : List Bool) (z : Fin g → List Bool) (i : Fin g) (w : List Bool) :
    Function.update (store x y z) (.lane i) w = store x y (Function.update z i w) := by
  funext j
  cases j with
  | raw | scratch => simp [store]
  | lane j => by_cases he : j = i <;> simp [store, he]

variable (enc : Bool → Fin g → Bool) (h : Option Bool)

private theorem reverse_run (xs acc : List Bool) (z : Fin g → List Bool) :
    StackRuns (code enc) (2*xs.length+1) (.reverse h) (store xs acc z)
      (.take h) (store [] (xs.reverse ++ acc) z) := by
  induction xs generalizing acc with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [store, List.head?_nil, Option.elim_none, List.tail_nil, List.reverse_nil,
      List.nil_append, setRaw]
    exact .nil ..
  | cons b xs ih =>
    rw [List.length_cons, Nat.mul_succ, show 2*xs.length+2+1 = (2*xs.length+1)+1+1 by omega]
    refine .cons (.pop rfl) ?_
    simp only [store, List.head?_cons, Option.elim_some, List.tail_cons, setRaw]
    refine .cons (.push rfl) ?_
    simpa only [store, setScratch, List.reverse_cons, List.append_assoc, List.singleton_append]
      using ih (b :: acc)

private def filledLanes (b : Bool) (z : Fin g → List Bool) (n : ℕ) (j : Fin g) : List Bool :=
  if j.val < n then enc b j :: z j else z j

private theorem spread_run (b : Bool) (scratch : List Bool) (z : Fin g → List Bool)
    (n : ℕ) (i : Fin (g+1)) (hn : i.val + n = g) :
    StackRuns (code enc) (n+1) (.spread h b i) (store [] scratch (filledLanes enc b z i.val))
      (.take h) (store [] scratch (fun j => enc b j :: z j)) := by
  induction n generalizing i with
  | zero =>
    have hi : i.val = g := by omega
    have hz : filledLanes enc b z i.val = fun j => enc b j :: z j := by
      funext j; simp [filledLanes, hi, j.isLt]
    rw [hz]
    exact .cons (.goto (by simp [code, hi])) (.nil ..)
  | succ n ih =>
    let j : Fin g := ⟨i.val, by omega⟩
    have hc : code enc (.spread h b i) = .push (.lane j) (enc b j) (.spread h b j.succ) := by
      simp [code, j.isLt, j]
    have hz : Function.update (filledLanes enc b z i.val) j (enc b j :: filledLanes enc b z i.val j) =
        filledLanes enc b z j.succ.val := by
      funext l
      by_cases hl : l = j
      · subst l; simp [filledLanes, j]
      · have hd : l.val ≠ i.val := fun he => hl (Fin.ext he)
        have he : l.val < i.val+1 ↔ l.val < i.val := by omega
        simp [filledLanes, hl, j, he]
    refine .cons (.push hc) ?_
    rw [setLane]
    simp only [store]
    rw [hz]
    exact ih j.succ (by dsimp [j]; omega)

private theorem take_run (xs : List Bool) (z : Fin g → List Bool) :
    StackRuns (code enc) ((g+2)*xs.length+1) (.take h) (store [] xs z)
      (.done h) (store [] [] (fun j => (xs.map (fun b => enc b j)).reverse ++ z j)) := by
  induction xs generalizing z with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [store, List.head?_nil, List.tail_nil, Option.elim_none, setScratch,
      List.map_nil, List.reverse_nil, List.nil_append]
    exact .nil ..
  | cons b xs ih =>
    have hs := spread_run enc h b xs z g 0 (by simp)
    have hz : filledLanes enc b z 0 = z := by funext j; simp [filledLanes]
    rw [Fin.val_zero, hz] at hs
    have hr := hs.trans (ih (fun j => enc b j :: z j))
    rw [List.length_cons, Nat.mul_succ, show (g+2)*xs.length+(g+2)+1 =
      (g+1 + ((g+2)*xs.length+1))+1 by omega]
    refine .cons (.pop rfl) ?_
    simpa only [store, List.head?_cons, List.tail_cons, Option.elim_some, setScratch,
      List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using hr

/-- Exact loading time, valid also for an empty input or zero symbol tracks. -/
def steps (g : ℕ) (bs : List Bool) : ℕ := (g+4)*bs.tail.length+3

/-- The first bit is retained in control and all remaining bits occur in their original order
in every lane. Both unbounded auxiliary stacks are empty on return. -/
theorem runs (bs : List Bool) :
    StackRuns (code enc) (steps g bs) .start (store bs [] (fun _ => []))
      (.done bs.head?) (store [] [] (fun j => bs.tail.map (fun b => enc b j))) := by
  have r := reverse_run enc bs.head? bs.tail [] (fun _ => [])
  have t := take_run enc bs.head? bs.tail.reverse (fun _ => [])
  simp only [List.append_nil, List.length_reverse, List.map_reverse, List.reverse_reverse] at r t
  have he : steps g bs = ((2*bs.tail.length+1)+((g+2)*bs.tail.length+1))+1 := by
    unfold steps; ring
  rw [he]
  refine .cons (.pop rfl) ?_
  simpa only [store, setRaw] using r.trans t

/-- Raw and scratch stacks alongside the full bank of native tape bit tracks. -/
abbrev NativePort (m g : ℕ) := Bool ⊕ TeamPrivateTape.Port (m*g)

/-- Install the loader's output lanes as the selected tape's right-neighbor stacks. -/
def ports (i : Fin m) : Port g → NativePort m g
  | .raw => .inl false
  | .scratch => .inl true
  | .lane j => .inr (finProdFinEquiv (i,j), true)

/-- Every stack used by the loader has a distinct physical port. -/
theorem ports_injective (i : Fin m) : Function.Injective (ports (g := g) i) := by
  intro p q h
  cases p <;> cases q <;> simp_all [ports]

/-- Before loading, only the raw binary input port is occupied. -/
def initial (bs : List Bool) : Stacks (NativePort m g) :=
  Sum.elim (fun b => if b then [] else bs) (fun _ => [])

/-- The native simulator sees its prescribed tape bank, with both loader auxiliaries empty. -/
def loaded (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (bs : List Bool) :
    Stacks (NativePort m g) := Sum.elim (fun _ => []) (bank (tracks a (input a.blank digit i bs)))

/-- Fixed lookup of the initial scanned bits from the first pop of the input stack. -/
def headBits (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (b : Option Bool) :
    Fin (m*g) → Bool := fun j =>
  let p := finProdFinEquiv.symm j
  if p.1 = i then a.bits ((b.map digit).getD a.blank) p.2 else false

/-- Initial head bits agree with the native tape input, including its empty case. -/
theorem headBits_eq (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (bs : List Bool) :
    headBits a digit i bs.head? = heads (tracks a (input a.blank digit i bs)) := by
  funext j
  obtain ⟨⟨t, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  by_cases he : t = i <;>
    simp [headBits, heads, tracks, input, SymbolTape.track, he, a.blank_bits, List.head?_map]

/-- Replace the return for each possible first pop by the caller's simulator entry for
the corresponding native tuple of scanned bits. -/
def withHead (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (label : State g → R)
    (entry : (Fin (m*g) → Bool) → R) : State g → R
  | .done h => entry (headBits a digit i h)
  | q => label q

private theorem loaded_at (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (bs : List Bool)
    (j : Port g) :
    loaded a digit i bs (ports i j) =
      store [] [] (fun k => bs.tail.map (fun b => a.bits (digit b) k)) j := by
  cases j with
  | raw | scratch => rfl
  | lane k =>
    cases bs <;> simp [loaded, ports, store, bank, tracks, input, SymbolTape.track, List.map_map,
      Function.comp_def]

private theorem loaded_outside (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (bs : List Bool)
    (p : NativePort m g) (hp : ∀ j, ports i j ≠ p) :
    loaded a digit i bs p = initial bs p := by
  rcases p with (b | ⟨k, side⟩)
  · cases b
    · exact (hp .raw rfl).elim
    · rfl
  · obtain ⟨⟨t, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    by_cases ht : t = i
    · subst t
      cases side
      · simp [loaded, initial, bank, tracks, input, SymbolTape.track]
      · exact (hp (.lane j) rfl).elim
    · cases side <;> simp [loaded, initial, bank, tracks, input, SymbolTape.track, ht]

/-- Link the loader to an arbitrary native simulator entry. On every raw binary string its
deterministic run prepares exactly the native input tapes and scanned bits in linear time. -/
theorem native_runs (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (bs : List Bool)
    (target : StackCode (NativePort m g) R) (label : State g → R)
    (entry : (Fin (m*g) → Bool) → R)
    (rows : ∀ q, ((code (fun b => a.bits (digit b))) q).returns = false →
      target (withHead a digit i label entry q) =
        ((code (fun b => a.bits (digit b))) q).rename (ports i) (withHead a digit i label entry)) :
    StackRuns target (steps g bs) (label .start) (initial bs)
      (entry (heads (tracks a (input a.blank digit i bs)))) (loaded a digit i bs) := by
  have r := (runs (fun b => a.bits (digit b)) bs).lift (ports i) (ports_injective i)
    (withHead a digit i label entry) (initial bs) rows
  have hin (p : Port g) : initial bs (ports i p) = store bs [] (fun _ => []) p := by
    cases p <;> rfl
  rw [installStacks_eq (ports_injective i) _ _ hin, installStacks_frame (ports_injective i)
    (loaded_at a digit i bs) (loaded_outside a digit i bs)] at r
  simpa only [withHead, headBits_eq] using r

end TeamPrivateInput

end BorderVNP
end Computability
end OAI
