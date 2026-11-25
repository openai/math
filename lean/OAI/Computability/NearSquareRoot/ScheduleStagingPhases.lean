import OAI.Computability.NearSquareRoot.ScheduleChunkPhases
import OAI.Computability.NearSquareRoot.ScheduleChunkCalleeSpace

/-! # Raw digit-call interface for the fenced multiplier

The controller places delimiter-separated MSF digits on register one. A
returned MSF bit stream is encoded there before the accumulation phase. The
fixed conversions charge every bit and preserve the record on register zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingPhases

open IntegerMultiplication IntegerMultiplication.Code
open Schoolbook (raw)

open private Does.br Does.push Does.pop from OAI.Computability.IntegerMultiplication.Interface

private def unparseFirst : Cmd :=
  .look 0 fun v => .join (.pop 0) <| match v with
  | some .node =>
    .look 0 fun v => .join (.pop 0) <| match v with
    | some (.bit b) => .join (.again 0) (.push 0 (.bit b))
    | _ => .pass
  | _ => .join Schoolbook.unloadCmd (.push 0 .sep)

private theorem unparseFirst_run (x y : List Bool) (E : Env) :
    Prog.Run (unparseFirst::E) unparseFirst (raw ((send x).spell ++ (send y).spell))
      (13+12*(x.length+y.length)) (raw (x.map Ltr.bit ++ .sep :: y.map Ltr.bit)) := by
  induction x with
  | nil =>
    change Prog.Run _ unparseFirst (raw (.bit false :: (send y).spell)) (13+12*(0+y.length))
      (raw (.sep :: y.map Ltr.bit))
    rw [show 13+12*(0+y.length) = 1+(1+1+1+(1+(6+12*y.length)+1+1)) by omega]
    apply Does.br (.bit false)
    exact Prog.Run.join (Schoolbook.unload_run y _) (Does.push ..)
  | cons b x ih =>
    have loop := Prog.Run.again (i:=0) (Γ:=unparseFirst::E) (c:=unparseFirst) (by simp) ih
    have run := Prog.Run.join loop (Does.push _ (Ltr.bit b) _)
    rw [List.length_cons]
    rw [show 13+12*(x.length+1+y.length) =
      1+(1+1+1+(1+(1+1+1+(1+(1+(13+12*(x.length+y.length)))+1+1)))) by omega]
    apply Does.br .node
    apply Does.br (.bit b)
    exact run

/-- Convert the encoded pair in place to a delimiter-separated MSF tape. -/
def unparsePair : Cmd := .join (.pop 0) (.tie unparseFirst)

theorem unparsePair_run (x y : List Bool) (E : Env) :
    Prog.Run E unparsePair (raw (send (x,y)).spell) (17+12*(x.length+y.length))
      (raw (x.map Ltr.bit ++ .sep :: y.map Ltr.bit)) := by
  rw [show 17+12*(x.length+y.length) = 1+1+1+(1+(13+12*(x.length+y.length))) by omega]
  exact Prog.Run.join (Does.pop _ .node _) (Prog.Run.tie (unparseFirst_run x y E))


open IntegerMultiplication.Bits ChunkTask ChunkLoop
open ChunkPhases (input record digitQuery digitReply output Runs Bundle)

open private codeY inList_cost Ybase from OAI.Computability.IntegerMultiplication.Interface

/-- Reuse P192's parser for a single binary list ending at the empty stack. -/
def parseWord : Cmd := .tie codeY

theorem parseWord_run (z : Word) (e : Env) :
    Prog.Run e parseWord (raw (z.map Ltr.bit)) (6+11*z.length) (raw (send z).spell) := by
  have h := inList_cost _ _ [] [] 5 e (Ybase e) z
  rw [show 6+11*z.length = 1+(11*z.length+5) by omega]
  apply Prog.Run.tie (c := codeY)
  change Prog.Run (codeY :: e) codeY (raw (z.map Ltr.bit ++ [])) _ (raw ((send z).spell ++ [])) at h
  simpa only [List.append_nil] using h

def request (w : Operands) := w.1.map Ltr.bit ++ .sep :: w.2.map Ltr.bit

/-- Park the live record on register zero and the raw call data on register one. -/
def slot (b : Bundle) (s : List Ltr) : Reg Ltr := Function.update (raw (send b).spell) 1 s

private theorem lift_slot {c : Cmd} {x y : List Ltr} {t : ℕ} (b : Bundle)
    (h : Prog.Run [] c (raw x) t (raw y)) :
    Prog.Run [] (c.rename Nat.succ) (slot b x) t (slot b y) := by
  simpa only [slot, List.map_nil, ChunkCalleeSpace.paint_succ_raw] using
    h.rename Nat.succ_injective (raw (send b).spell)

theorem unparse_digit (b : Bundle) (q : Operands) :
    Prog.Run [] (unparsePair.rename Nat.succ) (ChunkPhases.frame b (send q))
      (17+12*(q.1.length+q.2.length)) (slot b (request q)) :=
  lift_slot b (unparsePair_run q.1 q.2 [])

theorem parse_digit (b : Bundle) (z : Word) :
    Prog.Run [] (parseWord.rename Nat.succ) (slot b (z.map Ltr.bit))
      (6+11*z.length) (ChunkPhases.frame b (send z)) :=
  lift_slot b (parseWord_run z [])

theorem slot_height (b : Bundle) (s : List Ltr) (i : ℕ) :
    (slot b s i).length ≤ max (size b) s.length := by
  by_cases h : i = 1
  · simp [slot,h]
  · rw [slot,Function.update_of_ne h]
    exact (ChunkPhases.raw_height _ _).trans ((Tree.spell_length _).le.trans (le_max_left _ _))

theorem request_height (m : Operands → Word) (p : Input) (i : ℕ) (hi : i ≤ p.count) (j : ℕ) :
    (slot (p.bundle m i) (request (digitQuery m p i)) j).length ≤ 32*(p.n+1) := by
  apply (slot_height ..).trans (max_le _ _)
  · have := p.bundle_size m i hi
    omega
  · have hq := p.query_width m i
    have := p.width_le
    simp only [request, digitQuery, List.length_append, List.length_map, List.length_cons,
      hq.1, hq.2]
    omega

theorem result_height (m : Operands → Word) (p : Input) (i : ℕ) (hi : i ≤ p.count)
    (w : (digitReply m p i).length = 2*p.u) (j : ℕ) :
    (slot (p.bundle m i) ((digitReply m p i).map Ltr.bit) j).length ≤ 32*(p.n+1) := by
  apply (slot_height ..).trans (max_le _ _)
  · have := p.bundle_size m i hi
    omega
  · rw [List.length_map,w]
    have := p.width_le
    omega

structure Calls (load test prepare collect emit : Cmd) (C : ℕ) (m : Operands → Word)
    (p : Input) (result : List Ltr := output m p) : Prop where
  load_run : Runs load (C*(p.n+1)) (raw (input p)) (raw (record m p 0))
  test_run : ∀ t ≤ p.count, Runs test (C*(p.n+1)) (raw (record m p t))
    (raw (.bit (decide (t=p.count)) :: record m p t))
  prepare_run : ∀ t < p.count, Runs prepare (C*(p.n+1)) (raw (record m p t))
    (slot (p.bundle m t) (request (digitQuery m p t)))
  collect_run : ∀ t < p.count, (digitReply m p t).length = 2*p.u →
    Runs collect (C*(p.n+1)) (slot (p.bundle m t) ((digitReply m p t).map Ltr.bit))
      (raw (record m p (t+1)))
  emit_run : Runs emit (C*(p.n+1)) (raw (record m p p.count)) (raw result)

theorem adapt {load test prep collect emit : Cmd} {C : ℕ} {m : Operands → Word}
    {p : Input} {result : List Ltr} (h : ChunkPhases.Calls load test prep collect emit C m p result) :
    Calls load test (prep.join (unparsePair.rename Nat.succ))
      ((parseWord.rename Nat.succ).join collect) emit (C+32) m p result := by
  have small : C*(p.n+1) ≤ (C+32)*(p.n+1) := Nat.mul_le_mul_right _ (by omega)
  have widen {src dest c} (hr : Runs c (C*(p.n+1)) src dest) :
      Runs c ((C+32)*(p.n+1)) src dest := by
    obtain ⟨t,ht,hr⟩ := hr
    exact ⟨t,ht.trans small,hr⟩
  refine ⟨widen h.load_run, fun i hi => widen (h.test_run i hi), ?_, ?_, widen h.emit_run⟩
  · intro i hi
    obtain ⟨t,ht,hr⟩ := h.prepare_run i hi
    have rest := unparse_digit (p.bundle m i) (digitQuery m p i)
    refine ⟨_, ?_, hr.join rest⟩
    have hq := p.query_width m i
    have := p.width_le
    rw [digitQuery, hq.1,hq.2, Nat.add_mul]
    omega
  · intro i hi hwidth
    obtain ⟨t,ht,hr⟩ := h.collect_run i hi hwidth
    have first := parse_digit (p.bundle m i) (digitReply m p i)
    refine ⟨_, ?_, first.join hr⟩
    have := p.width_le
    rw [hwidth,Nat.add_mul]
    omega

/-- The five finite programs and their absolute cost constant are independent
of the callee and of all input and split parameters. -/
theorem controllers :
    ∃ (load test prepare collect emit : Cmd) (C : ℕ),
      ∀ (m : Operands → Word) (p : Input), Calls load test prepare collect emit C m p := by
  obtain ⟨load,test,prep,collect,emit,C,h⟩ := ChunkPhases.controllers
  exact ⟨_,_,_,_,_,_, fun m p => adapt (h m p)⟩

end StagingPhases

end NearSquareRoot
end Computability
end OAI
