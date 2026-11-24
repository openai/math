import OAI.Computability.VPVNP.PairSimulationInlinePublic

/-!
# Linking lowered table prefixes into a larger native machine

The caller may place a continuation directly at an accepting exit and its own rejecting
instruction at a failure exit. A source prefix only executes nonterminal rows, so these
exit labels can be shared even when the source instruction at the exit is absent.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.InlinePublic

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {v w C p r k P R K : ℕ}

/-- Install the consecutive source blocks and local registers at enclosing locations. -/
def embedding (C p r : ℕ) (pc : Fin (p * (C + 3)) → Fin P) (reg : Fin (r + 2) ↪ Fin R) :
    Placement C p r P R where
  pc i j := pc ((canonical C p r).pc i j)
  reg := (canonical C p r).reg.trans reg
  unit := reg (canonical C p r).unit
  acc := reg (canonical C p r).acc
  distinct := fun e => (canonical C p r).distinct (reg.injective e)
  reg_unit i e := (canonical C p r).reg_unit i (reg.injective e)
  reg_acc i e := (canonical C p r).reg_acc i (reg.injective e)

/-- A terminal source entry can be an external continuation label. Its outgoing row
is unnecessary when linking prefixes. -/
def Placement.withExits (D : Placement C p r P R) (exit : Fin p → Option (Fin P)) :
    Placement C p r P R :=
  {D with pc := fun i j => if j = 0 then (exit i).getD (D.entry i) else D.pc i j}

@[simp] theorem Placement.entry_withExits (D : Placement C p r P R)
    (exit : Fin p → Option (Fin P)) (i : Fin p) :
    (D.withExits exit).entry i = (exit i).getD (D.entry i) := by
  simp [Placement.entry, Placement.withExits]

/-- A nonterminal source row has a continuation. -/
def continues : Instr v p r k → Bool
  | .returnState _ | .accept | .reject => false
  | _ => true

private theorem continues_local {i : Instr v p r k} {pub : Fin k → Word w}
    {s next : Config w p r} (h : (i.resize w).run pub s = .localStep next) :
    continues i = true := by
  cases i <;> first | rfl | cases h

private theorem continues_branch {i : Instr v p r k} {pub : Fin k → Word w}
    {s : Config w p r} {next : Bool → Config w p r} (h : (i.resize w).run pub s = .branch next) :
    continues i = true := by
  cases i <;> first | rfl | cases h

@[simp] theorem padded_length (pad : ℕ) (es : List (Event w)) :
    (padded pad es).length = (pad + 1) * es.length := by
  induction es with
  | nil => simp [padded]
  | cons e es ih => simp [padded, ih, Nat.mul_succ]; omega

@[simp] theorem padded_ticks (pad n : ℕ) :
    padded pad (List.replicate n (.tick : Event w)) = List.replicate ((pad + 1) * n) .tick := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, padded, ih, ← List.replicate_succ, ← List.replicate_add]
    congr 1
    rw [Nat.mul_succ]
    omega

private theorem tickBits (pad : ℕ) (es : List (Event w)) :
    choiceBits (List.replicate pad .tick ++ es) = choiceBits es := by
  induction pad with
  | zero => rfl
  | succ pad ih => simpa [List.replicate_succ, choiceBits] using ih

@[simp] theorem padded_choiceBits (pad : ℕ) (es : List (Event w)) :
    choiceBits (padded pad es) = choiceBits es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [padded, tickBits]; cases e <;> simp [choiceBits, ih]

/-- Transport every local path, with the same choice bits and the exact fixed slowdown.
Only nonterminal code must be linked. The host's final configuration exposes the entire
source register file, the private memory, and the enclosing caller's register frame. -/
theorem prefix_lower (T : Template p r k) (bank : Fin k → ℕ) (D : Placement C p r P R)
    (M : Machine w P R K) {frame : Fin R → Word w}
    (bound : ∀ j, operand bank (T.code j) ≤ C)
    (hc : ∀ j, continues (T.code j) = true → ContainsAt M T bank D j)
    {s last : Config w p r} {h : Config w P R} {es : List (Event w)}
    (path : Prefix (T.instantiate w (fun j => (bank j : Word w))) s es last)
    (rel : Related D frame s h) :
    ∃ out, Prefix M h (padded (C + 2) es) out ∧ Related D frame last out := by
  induction path generalizing h with
  | nil s => exact ⟨h, .nil _, rel⟩
  | @tick s next last es step tail ih =>
    obtain ⟨mid, pre, actions⟩ := simulate_row (bound s.pc) (hc s.pc (continues_local step)) rel
    rw [step] at actions
    generalize hmid : M.program.step mid = act at actions
    cases actions with
    | localStep nextRel =>
      obtain ⟨out, post, outRel⟩ := ih nextRel
      exact ⟨out, pre.append (.tick hmid post), outRel⟩
  | @choice s g b last es step tail ih =>
    obtain ⟨mid, pre, actions⟩ := simulate_row (bound s.pc) (hc s.pc (continues_branch step)) rel
    rw [step] at actions
    generalize hmid : M.program.step mid = act at actions
    cases actions with
    | branch nextRel =>
      obtain ⟨out, post, outRel⟩ := ih (nextRel b)
      exact ⟨out, pre.append (.choice hmid post), outRel⟩

/-- The map table's deterministic path and its computed histogram share the same private
memory. A bound on the source tick count scales by the uniform block length. -/
theorem ticks_lower (T : Template p r k) (bank : Fin k → ℕ) (D : Placement C p r P R)
    (M : Machine w P R K) {frame : Fin R → Word w}
    (bound : ∀ j, operand bank (T.code j) ≤ C)
    (hc : ∀ j, continues (T.code j) = true → ContainsAt M T bank D j)
    {s last : Config w p r} {h : Config w P R} {n : ℕ}
    (path : Prefix (T.instantiate w (fun j => (bank j : Word w))) s (List.replicate n .tick) last)
    (rel : Related D frame s h) :
    ∃ out, Prefix M h (List.replicate ((C + 3) * n) .tick) out ∧ Related D frame last out := by
  simpa using prefix_lower T bank D M bound hc path rel

/-- View a live host configuration as source state at a known entry. -/
def restrict (D : Placement C p r P R) (pc : Fin p) (h : Config w P R) : Config w p r :=
  ⟨pc, h.persistent, h.reg ∘ D.reg, h.privateMem⟩

theorem restrict_related (D : Placement C p r P R) (pc : Fin p) (h : Config w P R)
    (hp : h.pc = D.entry pc) : Related D h.reg (restrict D pc h) h :=
  ⟨⟨fun _ => rfl, rfl, rfl, fun _ _ => rfl⟩, hp⟩

end PairSimulation.InlinePublic

end VPVNP
end Computability
end OAI
