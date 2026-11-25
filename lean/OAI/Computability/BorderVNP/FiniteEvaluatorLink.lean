import OAI.Computability.BorderVNP.FiniteEvaluatorTrace

/-! # Relocating chronological field traces within the assembled evaluator

A normal return carries a fixed marked event history in every table containing
its actual instruction rows. The continuation may be the next stage or a loop test.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamRAM

variable {w p : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The private identifiers occurring in a structured source fragment. -/
def uses (j : Macro) : Code → Bool
  | .call i .. => decide (i=j)
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b | .choose a b => uses j a || uses j b
  | .whileLt _ _ a => uses j a
  | _ => false

/-- One chronological list of marked events read by every linked occurrence of the
fragment, and its actual private opcodes occur in the fragment's finite code. -/
structure Spelling (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (c : Code) (s : Bank w)
    (es : List (TeamRAM.Event w)) (xs : List (Mark 8 w)) : Prop where
  linked : ∀ (main : Code) (lab : ℕ → Fin (main.slots+1)) start finish, Contains main.row lab start finish c →
    trace main.program pub mac ⟨lab start,s⟩ es = xs
  ids : ∀ j e, (some j,e) ∈ xs → uses j c = true

/-- Actual native endpoint of a fragment in a containing structured table. -/
theorem linkedPrefix {c s mem es z mz} (run : Runs pub mac c s mem es z mz) {main : Code}
    {lab : ℕ → Fin (main.slots+1)} {start finish} (h : Contains main.row lab start finish c) :
    NativePrefix (main.program.fetch pub mac) ⟨lab start,s⟩ mem es ⟨lab finish,z⟩ mz := by
  simpa only [show fetch main.row pub mac = main.program.fetch pub mac from funext (fetch_row main pub mac)] using run.nativePrefix main.row lab h

/-- Both actual code intervals of a sequence. -/
theorem seq_intervals {main a b : Code} {lab : ℕ → Fin (main.slots+1)} {start finish}
    (h : Contains main.row lab start finish (.seq a b)) :
    Contains main.row lab start (start+a.slots) a ∧ Contains main.row lab (start+a.slots) finish b := by
  constructor <;> intro i hi hj
  · rw [h i hi (by simp only [Code.slots]; omega)]; simp [Code.emit,hj]
  · rw [h i (by omega) (by simp only [Code.slots]; omega)]; simp [Code.emit,not_lt.mpr hi]

private theorem tag_native (P : TeamOpcode.Program p 64 32 8) (pub : Arg → Word w) (pc : Fin p) (bank : Bank w)
    (h : P.tag pc = .native) : privateID (TeamOpcode.prepare P pub ⟨pc,bank⟩).1 = none := by
  simp only [TeamOpcode.prepare,h]
  split <;> rfl

private def atomID : Code → Option Macro
  | .call j .. => some j
  | _ => none

private theorem atomSpelling {c s mem action next sg bs} (hc : c.isAtom=true)
    (ha : (c.atom pub mac s).action = some action)
    (step : (c.atom pub mac s).advance bs (previous mem action) = some (next,sg)) :
    let e : TeamRAM.Event w := ⟨action,previous mem action,bs,sg⟩
    Spelling pub mac c s [e] [(atomID c,e)] := by
  intro e
  constructor
  · intro main lab start finish H
    have op := (fetch_entry H pub mac s).trans (fetch_atom lab start start finish c hc pub mac s)
    rw [fetch_row] at op
    have idEq : privateID (TeamOpcode.prepare main.program pub ⟨lab start,s⟩).1 = atomID c := by
      have tag : main.program.tag (lab start) = (c.emit lab start start finish).2 :=
        congrArg Prod.snd (H start le_rfl (Nat.lt_add_of_pos_right c.slots_pos))
      cases c <;> try contradiction
      all_goals simp only [Code.emit] at tag
      all_goals first
        | exact tag_native main.program pub (lab start) s tag
        | (simp only [TeamOpcode.prepare,tag,privateID,atomID])
    simp only [trace,e,op,resume_advance,step,Option.map_some,idEq]
  · intro j z hz
    have eq := congrArg Prod.fst (List.mem_singleton.mp hz)
    change some j = atomID c at eq
    cases c <;> try contradiction
    simp [atomID] at eq
    simp [uses,eq]

private inductive Fork where
  | eq (x y : Reg)
  | lt (x y : Reg)
  | guess (bit : Bool)

private def Fork.code : Fork → Code → Code → Code
  | .eq x y => .ifEq x y
  | .lt x y => .ifLt x y
  | .guess _ => .choose

private def Fork.bit (s : Bank w) : Fork → Bool
  | .eq x y => decide (s x = s y)
  | .lt x y => decide (s x < s y)
  | .guess b => b

private def Fork.event : Fork → TeamRAM.Event w
  | .eq .. | .lt .. => tick w
  | .guess b => choiceTick w b

private theorem forkSpelling (f : Fork) (a b : Code) {s es xs}
    (child : Spelling pub mac (if f.bit s then a else b) s es xs) :
    Spelling pub mac (f.code a b) s (f.event::es) ((none,f.event)::xs) := by
  constructor
  · intro main lab start finish H
    let dest := if f.bit s then start+1 else start+1+a.slots
    have part : Contains main.row lab dest finish (if f.bit s then a else b) := by
      dsimp only [dest]
      split
      · apply H.forkLeft (b := b) (by cases f <;> rfl)
        intro i hlo hhi; cases f <;> simp only [Fork.code,Code.emit,ite_eq_right (Nat.ne_of_gt hlo),ite_eq_left hhi]
      · apply H.forkRight (a := a) (by cases f <;> rfl)
        intro i hlo hhi; cases f <;> simp only [Fork.code,Code.emit,ite_eq_right (Nat.ne_of_gt hlo),ite_eq_right (not_lt.mpr hhi)]
    have op := fetch_entry H pub mac s
    rw [fetch_row] at op
    have idEq : privateID (TeamOpcode.prepare main.program pub ⟨lab start,s⟩).1 = none := by
      apply tag_native
      have tag := congrArg Prod.snd (H start le_rfl (Nat.lt_add_of_pos_right (f.code a b).slots_pos))
      cases f <;> simpa only [Fork.code,Code.program,Code.emit,ite_true] using tag
    have step : (main.program.fetch pub mac ⟨lab start,s⟩).advance (f.event (w := w)).choices f.event.old =
        some (⟨lab dest,s⟩,.plus) := by
      rw [op]
      cases f <;> simp only [Fork.code,Fork.event,Code.emit,ite_true,fetch_jumpEq,fetch_jumpLt,fetch_choose,Instr.advance,tick,choiceTick,dest,Fork.bit,decide_eq_true_eq]
      all_goals split <;> simp_all
    simp only [trace,step,idEq,child.linked main lab dest finish part]
  · intro j e he
    rcases List.mem_cons.mp he with he | he
    · cases he
    · have idOk := child.ids j e he
      cases f <;> simp only [Fork.code,uses] <;> split at idOk <;> simp [idOk]

private theorem loopChild {main a : Code} {x y : Reg} {lab : ℕ → Fin (main.slots+1)} {start finish}
    (h : Contains main.row lab start finish (.whileLt x y a)) : Contains main.row lab (start+1) start a := by
  intro i hlo hhi
  rw [h i (by omega) (by simp only [Code.slots]; omega)]
  simp only [Code.emit,ite_eq_right (by omega : i≠start)]

private theorem loopHead {main a : Code} {x y : Reg} {lab : ℕ → Fin (main.slots+1)} {start finish}
    (h : Contains main.row lab start finish (.whileLt x y a)) (s : Bank w) (rest : List (TeamRAM.Event w)) :
    trace main.program pub mac ⟨lab start,s⟩ (tick w :: rest) =
      (none,tick w)::trace main.program pub mac ⟨if s x<s y then lab (start+1) else lab finish,s⟩ rest := by
  have op := fetch_entry h pub mac s
  rw [fetch_row] at op
  have tag : main.program.tag (lab start) = .native := by
    have hi := congrArg Prod.snd (h start le_rfl (Nat.lt_add_of_pos_right (Code.whileLt x y a).slots_pos))
    simpa only [Code.program,Code.emit,ite_true] using hi
  simp only [trace,tick,op,Code.emit,ite_true,fetch_jumpLt,Instr.advance,tag_native main.program pub (lab start) s tag]

/-- All actual instruction fetches in any linked occurrence of the run have
the same chronological words, branch scripts and routine identifiers. -/
theorem spelling {c s mem es z mz} (h : Runs pub mac c s mem es z mz) :
    ∃ xs, Spelling pub mac c s es xs := by
  induction h with
  | atom hc ha step => exact ⟨_,atomSpelling hc ha step⟩
  | seq first second ih1 ih2 =>
    obtain ⟨xs,hx⟩ := ih1
    obtain ⟨ys,hy⟩ := ih2
    refine ⟨xs++ys,⟨?_,?_⟩⟩
    · intro main lab start finish H
      obtain ⟨left,right⟩ := seq_intervals H
      rw [trace_append (linkedPrefix first left),hx.linked _ _ _ _ left,hy.linked _ _ _ _ right]
    · intro j e he
      exact (List.mem_append.mp he).elim (fun h => by simp [uses,hx.ids _ _ h]) (fun h => by simp [uses,hy.ids _ _ h])
  | @ifEq x y a b s _ _ _ _ _ ih =>
    obtain ⟨xs,hx⟩ := ih
    exact ⟨_,forkSpelling (.eq x y) a b (by simpa only [Fork.bit,decide_eq_true_eq] using hx)⟩
  | @ifLt x y a b s _ _ _ _ _ ih =>
    obtain ⟨xs,hx⟩ := ih
    exact ⟨_,forkSpelling (.lt x y) a b (by simpa only [Fork.bit,decide_eq_true_eq] using hx)⟩
  | @choose a b s _ _ _ _ bit _ ih =>
    obtain ⟨xs,hx⟩ := ih
    exact ⟨_,forkSpelling (.guess bit) a b hx⟩
  | whileDone guard =>
    exact ⟨[(none,tick w)],⟨fun _ _ _ _ H => by rw [loopHead H]; rfl,fun _ _ h => by simp at h⟩⟩
  | whileStep guard first tail ih1 ih2 =>
    obtain ⟨xs,hx⟩ := ih1
    obtain ⟨ys,hy⟩ := ih2
    refine ⟨(none,tick w)::(xs++ys),⟨?_,?_⟩⟩
    · intro main lab start finish H
      have body := loopChild H
      rw [loopHead H,ite_eq_left guard,trace_append (linkedPrefix first body),hx.linked _ _ _ _ body,hy.linked _ _ _ _ H]
    · intro j e he
      rcases List.mem_cons.mp he with h | h
      · cases h
      · exact (List.mem_append.mp h).elim (hx.ids _ _) (hy.ids _ _)

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
