import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedyPhases

/-!
# Dispatcher guards for the greedy record readers

Every call writes its vertex's label, reads the next cursor from the immutable
record header and leaves the active dispatcher frame intact. Consequently
the guard continues through all records and stops at the first address past
the directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.WalkLayout

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w N width q : ℕ}

private theorem base_lt_stop (L : WalkLayout w N width) (space : L.limit < 2 ^ w) (i : Fin N) :
    L.base i.val < L.base N := by
  have h : L.origin + N + i.val * (2 + width) < L.limit :=
    Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right i.isLt (by omega)) _
  change (L.origin + N + i.val * (2 + width)) % (2 ^ w) < L.limit % (2 ^ w)
  rwa [Nat.mod_eq_of_lt (h.trans space), Nat.mod_eq_of_lt space]

private theorem has_visit (m : Memory w) (base : Word w) (arity n : ℕ) (fit : n < 2 ^ w) :
    ∃ value, Visit m base arity n value := by
  obtain ⟨_, regs, _, _, _, h⟩ := choose_trace base m arity n (fun _ ↦ base + 1 + 1) fit
  exact ⟨regs 2, visit_native m base _ arity n fit h.symm⟩

private def fixedOutsideLabels (L : WalkLayout w N width) (initial m : Memory w) : Prop :=
  ∀ z, z < L.origin ∨ L.origin + N ≤ z → m z = initial z

/-- Induction along the actual reader reports. At each boundary the immutable
directory still supplies the next cursor and the memory outside the labels is
unchanged from the prepared input. -/
private theorem read_induction (L : WalkLayout w N width)
    (ptrs : Fin N → List (Word w)) (outside : Memory w) (arity n : ℕ)
    (size : ∀ i, (ptrs i).length = width) (space : L.limit < 2 ^ w) (fit : n < 2 ^ w)
    (Q : Word w → Memory w → List (Report w) → Prop)
    (done : ∀ m, fixedOutsideLabels L (L.initialMemory ptrs outside) m → Q (L.base N) m [])
    (step : ∀ (i : Fin N) m (r : Report w) rs,
      fixedOutsideLabels L (L.initialMemory ptrs outside) m → L.base i.val < L.base N →
      r.result = some (L.base (i.val + 1)) → Q (L.base (i.val + 1)) (after m r.events) rs →
      Q (L.base i.val) m (r :: rs))
    (rs : List (Report w)) (native : runSegment (visitMachine w arity n).program
      (1 + (visitCode arity n).length) (some (L.base 0)) (L.initialMemory ptrs outside)
      (List.replicate N []) = some rs) :
    Q (L.base 0) (L.initialMemory ptrs outside) rs := by
  let initial := L.initialMemory ptrs outside
  let fixed := fixedOutsideLabels L initial
  let M := (visitMachine w arity n).program
  let fuel := 1 + (visitCode arity n).length
  have loop (left k : ℕ) (stop : k + left = N) (m : Memory w) (keep : fixed m)
      (reports : List (Report w))
      (run : runSegment M fuel (some (L.base k)) m (List.replicate left []) = some reports) :
      Q (L.base k) m reports := by
    induction left generalizing k m reports with
    | zero =>
      have empty : [] = reports := Option.some.inj run
      subst reports
      simp only [Nat.add_zero] at stop
      subst k
      exact done m keep
    | succ left ih =>
      let i : Fin N := ⟨k, by omega⟩
      let labels (j : Fin N) := m (L.label j).val
      have rep : L.Represents initial m id (Equiv.refl (Fin N)) labels := ⟨fun _ ↦ rfl, keep⟩
      obtain ⟨dest, next, _⟩ := rep.record L size i
      obtain ⟨v, es, he, hm, _⟩ := has_visit m (L.base k) arity n fit
      rw [show m (L.base k).val = L.label i from dest] at hm
      rw [show m (L.base k + 1).val = L.base (k + 1) from next] at he
      have nextKeep : fixed (after m es) := by
        intro z hz
        rw [hm]
        have away : z ≠ (L.label i).val := by rw [L.label_val]; have := i.isLt; omega
        exact (ite_eq_right away).trans (keep z hz)
      rw [List.replicate_succ, runSegment, he] at run
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp run
      exact step i m _ tail keep (base_lt_stop L space i) rfl (ih (k+1) (by omega) _ nextKeep _ ht)
  exact loop N 0 (Nat.zero_add _) initial (fun _ _ ↦ rfl) rs native

/-- Guard validity for any native reader trace on a prepared operand directory.
Only the mutable labels must be disjoint from the active scheduler fields. -/
theorem read_valid (C : Schedule.Catalog q) (worker : Fin q) (ports : Schedule.Ports w)
    (pub : Fin (C worker).params → Word w) (L : WalkLayout w N width)
    (ptrs : Fin N → List (Word w)) (outside : Memory w) (arity n : ℕ)
    (size : ∀ i, (ptrs i).length = width) (space : L.limit < 2 ^ w) (fit : n < 2 ^ w)
    (tag : ports.tag.val < L.origin ∨ L.origin + N ≤ ports.tag.val)
    (frame : ∀ j : Fin ((C worker).params + 1), (ports.activeFrame + (j.val : Word w)).val < L.origin ∨
      L.origin + N ≤ (ports.activeFrame + (j.val : Word w)).val)
    (ready : Schedule.Ready C worker ports pub (L.base N) (L.initialMemory ptrs outside))
    (rs : List (Report w)) (native : runSegment (visitMachine w arity n).program
      (1 + (visitCode arity n).length) (some (L.base 0)) (L.initialMemory ptrs outside)
      (List.replicate N []) = some rs) :
    Schedule.ValidTrace C worker ports pub (L.base N) (L.base 0) (L.initialMemory ptrs outside) rs := by
  let initial := L.initialMemory ptrs outside
  let fixed := fixedOutsideLabels L initial
  have live {m : Memory w} (keep : fixed m) : Schedule.Ready C worker ports pub (L.base N) m := by
    refine ⟨(keep _ tag).trans ready.1, ?_, ?_⟩
    · exact (keep _ (by simpa using frame 0)).trans ready.2.1
    · exact funext fun i ↦ (keep _ (frame i.succ)).trans (congrFun ready.2.2 i)
  exact read_induction L ptrs outside arity n size space fit
    (Schedule.ValidTrace C worker ports pub (L.base N)) (fun _ keep ↦ ⟨live keep, le_rfl⟩)
    (fun i _ _ _ keep active ret tail ↦ ⟨live keep, active, L.base (i.val + 1), ret, tail⟩)
    rs native

end CompressorRecords.Greedy.WalkLayout

namespace CompressorRecords.GreedyArena.Assignment

open BurstRAM Compression Greedy
open scoped Fin.CommRing

variable {w N width q d arity n : ℕ} {V A : Type*}
variable {L : WalkLayout w N width} {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {rows : OperandRows d} {m : Memory w} {encode : A → Word w} {label : V → A}

/-- The reports of the actual assignment reader can be lifted into the linked
dispatcher under the same guard as the source reader. -/
theorem read_valid (P : Assignment L T G order rows arity n m encode label)
    (C : Schedule.Catalog q) (worker : Fin q) (ports : Schedule.Ports w)
    (pub : Fin (C worker).params → Word w)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width)
    (space : L.limit < 2 ^ w) (fit : n < 2 ^ w)
    (tag : ports.tag.val < L.origin ∨ L.origin + N ≤ ports.tag.val)
    (frame : ∀ j : Fin ((C worker).params + 1), (ports.activeFrame + (j.val : Word w)).val < L.origin ∨
      L.origin + N ≤ (ports.activeFrame + (j.val : Word w)).val)
    (ready : Schedule.Ready C worker ports pub (L.base N) (after m (eventLog P.prep))) :
    Schedule.ValidTrace C worker ports pub (L.base N) (L.base 0) (after m (eventLog P.prep)) P.reads := by
  have native := P.readRun
  rw [P.prepMemory] at native ready ⊢
  exact WalkLayout.read_valid C worker ports pub L _ _ arity n size space fit tag frame ready _ native

end CompressorRecords.GreedyArena.Assignment

end VPVNP
end Computability
end OAI
