import OAI.Computability.NearSquareRoot.ScheduleChunkSetup
import OAI.Computability.NearSquareRoot.ScheduleSchoolIO

/-!
# Fixed register programs for the fenced product controller

The cursor test, digit query, and returned digit product have explicit stack
layouts. The query or answer is staged on register one, leaving the working
record on register zero throughout the digit call.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkPhases

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkTask ChunkLoop
open Schoolbook (raw)

abbrev Bundle := Operands × ChunkLoop.State

def input (p : Input) := (send (tally p.k, (p.x,p.y))).spell
def record (m : Operands → Word) (p : Input) (t : ℕ) := (send (p.bundle m t)).spell
def digitQuery (m : Operands → Word) (p : Input) (t : ℕ) := query (p.bundle m t)
def digitReply (m : Operands → Word) (p : Input) (t : ℕ) := m (digitQuery m p t)
def output (m : Operands → Word) (p : Input) := (send (p.state m p.count).2.reverse).spell

def frame (b : Bundle) (q : Tree) : Reg Ltr :=
  Function.update (raw (send b).spell) 1 q.spell

abbrev Runs (c : Cmd) (cost : ℕ) (x y : Reg Ltr) := ∃ t ≤ cost, Prog.Run [] c x t y

private theorem program {X : Type} {b : X → ℕ} {q a : X → Tree} (h : Task b q a) :
    ∃ c : Cmd, ∃ C : ℕ, ∀ x, Runs c (C*(b x+1)) (raw (q x).spell) (raw (a x).spell) := by
  obtain ⟨c,C,hc⟩ := h
  refine ⟨c,C,fun x => ?_⟩
  obtain ⟨t,ht,run⟩ := hc x [] (fun _ => [])
  exact ⟨t,ht,by simpa only [Schoolbook.letters_pile_empty] using run⟩

private theorem pop_root (x : List Ltr) (a : Ltr) :
    Prog.Run [] (.pop 0) (raw (a::x)) 1 (raw x) := by
  convert (Prog.Run.pop (Γ := []) (r := raw (a::x)) (i := 0)) using 1
  funext i
  cases i <;> simp [Schoolbook.raw]

private theorem push_root (x : List Ltr) :
    Prog.Run [] (.push 0 .node) (raw x) 1 (raw (.node::x)) := by
  convert (Prog.Run.push (Γ := []) (r := raw x) (i := 0) (x := .node)) using 1
  funext i
  cases i <;> simp [Schoolbook.raw]

private theorem letters_stacked (q b : Tree) :
    letters (pile 0 q (pile 0 b (fun _ => []))) = raw (q.spell ++ b.spell) := by
  rw [letters_pile, Schoolbook.letters_pile_empty]
  funext i
  cases i <;> simp [Schoolbook.raw]

private theorem letters_frame (q : Tree) (b : Bundle) :
    letters (pile 1 q (pile 0 (send b) (fun _ => []))) = frame b q := by
  rw [letters_pile, Schoolbook.letters_pile_empty]
  change Function.update _ 1 (q.spell ++ []) = _
  rw [List.append_nil]
  rfl

private theorem move_out (b : Bundle) (q : Tree) :
    Runs (move 0 1 2) (42*q.count) (raw (q.spell ++ (send b).spell)) (frame b q) := by
  obtain ⟨t,ht,run⟩ := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide)
    q [] (pile 0 (send b) (fun _ => []))
  exact ⟨t,ht,by simpa only [letters_stacked,letters_frame] using run⟩

private theorem move_in (b : Bundle) (q : Tree) :
    Runs (move 1 0 2) (42*q.count) (frame b q) (raw (q.spell ++ (send b).spell)) := by
  obtain ⟨t,ht,run⟩ := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide)
    q [] (pile 0 (send b) (fun _ => []))
  exact ⟨t,ht,by simpa only [letters_stacked,letters_frame] using run⟩

private theorem cost_bound {t C s k n B : ℕ} (ht : t ≤ C*(s+1))
    (hs : s+1 ≤ k*(n+1)) (hB : C*k+3 ≤ B) : t+3 ≤ B*(n+1) := by
  have h := Nat.mul_le_mul_left C hs
  rw [← Nat.mul_assoc] at h
  exact (by nlinarith only [ht,h,Nat.zero_le n] : t+3 ≤ (C*k+3)*(n+1)).trans
    (Nat.mul_le_mul_right _ hB)

private theorem moved_bound {t tm C s k n B : ℕ} (ht : t ≤ C*(s+1))
    (hs : s+1 ≤ k*(n+1)) (hm : tm ≤ 200*(n+1)) (hB : C*k+205 ≤ B) :
    t+tm+5 ≤ B*(n+1) := by
  have h := Nat.mul_le_mul_left C hs
  rw [← Nat.mul_assoc] at h
  exact (by nlinarith only [ht,h,hm,Nat.zero_le n] :
    t+tm+5 ≤ (C*k+205)*(n+1)).trans (Nat.mul_le_mul_right _ hB)

private def tag (b : Bundle) := (ChunkCursor.exhausted b.2.1,b)
private def preparePair (b : Bundle) := (query b,b)
private def collectPair (p : Word × Bundle) : Bundle := (p.2.1, update (p.2.2,p.1))
private def unwrap (b : Bundle) := b.2.2.reverse

private theorem tag_easy : Easy tag :=
  ((show Easy (fun b : Bundle => b.2.1) by fun_prop).compose ChunkCursor.easy_exhausted).pair
    Easy.identity

private theorem collect_easy : Easy collectPair :=
  (show Easy (fun p : Word × Bundle => p.2.1) by fun_prop).pair
    ((show Easy (fun p : Word × Bundle => (p.2.2,p.1)) by fun_prop).compose easy_update)

private theorem encoded_input_length (p : Input) : (input p).length ≤ 6*p.n+5 := by
  have hk : p.k ≤ p.n := (Nat.le_of_lt Nat.lt_two_pow_self).trans p.fits
  change (send (tally p.k,(p.x,p.y))).spell.length ≤ _
  rw [Tree.spell_length]
  change size (tally p.k,(p.x,p.y)) ≤ _
  simp [size_tally, size_word, p.same, Input.n] at *
  omega

theorem record_length (m : Operands → Word) (p : Input) (t : ℕ) (ht : t ≤ p.count) :
    (record m p t).length ≤ 24*p.n+17 := by
  simpa only [record, Tree.spell_length, Code.size] using p.bundle_size m t ht

theorem query_length (m : Operands → Word) (p : Input) (t : ℕ) :
    (send (digitQuery m p t)).spell.length ≤ 4*p.n+3 := by
  rw [Tree.spell_length]
  change size (query (p.bundle m t)) ≤ _
  rw [size_prod, size_word, size_word, (p.query_width m t).1, (p.query_width m t).2]
  have := p.width_le
  omega

theorem reply_length (m : Operands → Word) (p : Input) (t : ℕ)
    (h : (digitReply m p t).length = 2*p.u) :
    (send (digitReply m p t)).spell.length ≤ 4*p.n+1 := by
  rw [Tree.spell_length]
  change size (digitReply m p t) ≤ _
  rw [size_word,h]
  have := p.width_le
  omega

theorem raw_height (s : List Ltr) (i : ℕ) : (raw s i).length ≤ s.length := by
  cases i <;> simp [Schoolbook.raw]

theorem frame_height (b : Bundle) (q : Tree) (i : ℕ) :
    (frame b q i).length ≤ max (size b) q.count := by
  by_cases h : i = 1
  · subst i
    simp [frame]
  · rw [frame,Function.update_of_ne h]
    exact (raw_height _ _).trans ((Tree.spell_length _).le.trans (le_max_left _ _))

theorem input_length (p : Input) : (input p).length ≤ 32*(p.n+1) := by
  have := encoded_input_length p
  omega

theorem query_count (m : Operands → Word) (p : Input) (t : ℕ) :
    (send (digitQuery m p t)).count ≤ 32*(p.n+1) := by
  have h := query_length m p t
  rw [Tree.spell_length] at h
  omega

theorem reply_count (m : Operands → Word) (p : Input) (t : ℕ)
    (h : (digitReply m p t).length = 2*p.u) :
    (send (digitReply m p t)).count ≤ 32*(p.n+1) := by
  have h := reply_length m p t h
  rw [Tree.spell_length] at h
  omega

theorem frame_length (m : Operands → Word) (p : Input) (t : ℕ) (ht : t ≤ p.count)
    (q : Tree) (hq : q.count ≤ 32*(p.n+1)) (i : ℕ) :
    (frame (p.bundle m t) q i).length ≤ 32*(p.n+1) := by
  apply (frame_height ..).trans (max_le _ hq)
  have := p.bundle_size m t ht
  omega

theorem query_frame_height (m : Operands → Word) (p : Input) (t : ℕ) (ht : t ≤ p.count) :
    ∀ i, (frame (p.bundle m t) (send (digitQuery m p t)) i).length ≤ 32*(p.n+1) :=
  frame_length m p t ht _ (query_count m p t)

theorem reply_frame_height (m : Operands → Word) (p : Input) (t : ℕ) (ht : t ≤ p.count)
    (hz : (digitReply m p t).length = 2*p.u) :
    ∀ i, (frame (p.bundle m t) (send (digitReply m p t)) i).length ≤ 32*(p.n+1) :=
  frame_length m p t ht _ (reply_count m p t hz)

/-- A rejected dyadic request can be recognized without allocating its streams. -/
theorem checked_none_iff (k n : Tally) :
    Uniform.Dyadic.checked (k,n) = none ↔ n.length < 2 ^ k.length := by
  by_cases h : 2 ^ k.length ≤ n.length
  · simp [Uniform.Dyadic.checked, h, Nat.not_lt_of_ge h]
  · simp [Uniform.Dyadic.checked, h, Nat.lt_of_not_ge h]

/-- Stack layouts and actual register-program cost of each controller call. -/
structure Calls (load test prepare collect emit : Cmd) (C : ℕ) (m : Operands → Word)
    (p : Input) (result : List Ltr := output m p) : Prop where
  load_run : Runs load (C*(p.n+1)) (raw (input p)) (raw (record m p 0))
  test_run : ∀ t ≤ p.count, Runs test (C*(p.n+1)) (raw (record m p t))
    (raw (.bit (decide (t=p.count)) :: record m p t))
  prepare_run : ∀ t < p.count, Runs prepare (C*(p.n+1)) (raw (record m p t))
    (frame (p.bundle m t) (send (digitQuery m p t)))
  collect_run : ∀ t < p.count, (digitReply m p t).length = 2*p.u →
    Runs collect (C*(p.n+1)) (frame (p.bundle m t) (send (digitReply m p t)))
      (raw (record m p (t+1)))
  emit_run : Runs emit (C*(p.n+1)) (raw (record m p p.count)) (raw result)

/-- All five programs and the constant in their linear cost bounds are fixed
before choosing the digit multiplier, the split, or even the input length. -/
theorem controllers :
    ∃ (load test prepare collect emit : Cmd) (C : ℕ),
      ∀ (m : Operands → Word) (p : Input), Calls load test prepare collect emit C m p := by
  obtain ⟨load,A,hl⟩ := program (setup (fun _ => []))
  obtain ⟨test,B,ht⟩ := program tag_easy
  obtain ⟨prep,D,hp⟩ := program (show Easy preparePair from easy_query.pair Easy.identity)
  obtain ⟨collect,E,hc⟩ := program collect_easy
  obtain ⟨emit,F,he⟩ := program (show Easy unwrap from easy_reverse Easy.snd.sndCompose)
  let C := 50*(A+B+D+E+F)+210
  refine ⟨load,.join test (.pop 0),(Prog.join prep (.pop 0)).join (move 0 1 2),
    (move 1 0 2).join (.join (.push 0 .node) collect),
    emit,C,fun m p => ?_⟩
  constructor
  · obtain ⟨t,ht,run⟩ := hl p
    exact ⟨t, ht.trans (Nat.mul_le_mul_right _ (show A ≤ C by dsimp [C]; omega)), run⟩
  · intro i hi
    let b := p.bundle m i
    obtain ⟨t,ht,run⟩ := ht b
    have hr : Prog.Run [] test (raw (record m p i)) t
        (raw (.node :: .bit (decide (i=p.count)) :: record m p i)) := by
      change Prog.Run [] test (raw (record m p i)) t
        (raw (.node :: .bit (ChunkCursor.exhausted (p.state m i).1) :: record m p i)) at run
      rwa [p.done_test m i hi] at run
    refine ⟨_, ?_, Prog.Run.join hr (pop_root _ _)⟩
    have hs : size b ≤ 24*p.n+17 := p.bundle_size _ _ hi
    have h := cost_bound (k := 25) ht (n := p.n) (by omega) (B := C) (by dsimp [C]; omega)
    omega
  · intro i hi
    let b := p.bundle m i
    obtain ⟨t,ht,run⟩ := hp b
    change Prog.Run [] prep (raw (record m p i)) t
      (raw (.node :: ((send (digitQuery m p i)).spell ++ record m p i))) at run
    let q := digitQuery m p i
    obtain ⟨tm,hm,mv⟩ := move_out b (send q)
    refine ⟨_, ?_, Prog.Run.join (Prog.Run.join run (pop_root _ _)) mv⟩
    have hs : size b ≤ 24*p.n+17 := p.bundle_size _ _ hi.le
    have hq := p.query_width m i
    change q.1.length = p.u ∧ q.2.length = p.u at hq
    change tm ≤ 42 * size q at hm
    rw [size_prod, size_word, size_word, hq.1, hq.2] at hm
    have hu := p.width_le
    have h := moved_bound (k := 25) ht (n := p.n) (by omega)
      (tm := tm) (by omega) (B := C) (by dsimp [C]; omega)
    omega
  · intro i hi hwidth
    let b := p.bundle m i
    let z := digitReply m p i
    obtain ⟨t,ht,run⟩ := hc (z,b)
    change Prog.Run [] collect
      (raw (.node :: ((send z).spell ++ record m p i)))
      t (raw (send (p.operands, step m p.operands (p.state m i))).spell) at run
    obtain ⟨tm,hm,mv⟩ := move_in b (send z)
    have hs : size b ≤ 24*p.n+17 := p.bundle_size _ _ hi.le
    have hz : z.length = 2*p.u := hwidth
    have hu := p.width_le
    have grow : size (z,b)+1 ≤ 32*(p.n+1) := by
      change size z + size b + 1 + 1 ≤ _
      rw [size_word, hz]
      omega
    change tm ≤ 42 * size z at hm
    rw [size_word, hz] at hm
    have h := moved_bound ht grow (tm := tm) (by omega) (B := C) (by dsimp [C]; omega)
    refine ⟨1+tm+1+(1+1+1+t), by omega, ?_⟩
    simpa only [b, z, record, Input.bundle, Input.state, Function.iterate_succ_apply']
      using Prog.Run.join mv (Prog.Run.join (push_root _) run)
  · let b := p.bundle m p.count
    obtain ⟨t,ht,run⟩ := he b
    have hs : size b ≤ 24*p.n+17 := p.bundle_size _ _ le_rfl
    have h := cost_bound (k := 25) ht (n := p.n) (by omega) (B := C) (by dsimp [C]; omega)
    exact ⟨t,by omega,run⟩

end ChunkPhases

end NearSquareRoot
end Computability
end OAI
