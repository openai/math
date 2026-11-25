import OAI.Computability.NearSquareRoot.PrecisionProductDriver
import OAI.Computability.NearSquareRoot.ScheduleSchoolDispatch
import OAI.Computability.NearSquareRoot.ScheduleSchoolSegments
import OAI.Computability.NearSquareRoot.ScheduleSchoolRelease
import OAI.Computability.IntegerMultiplication.Code.List
import Mathlib.Tactic

/-! # Reusing scratch tapes over a scanned array of records

At each call boundary only the unprocessed operand list and the accumulated
result list are live. The maximum stack height during a call is bounded by
its starting height plus that single call's time. The controller returns
to dispatch with an empty return stack after each call.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductDriver

open IntegerMultiplication Code Schoolbook

variable {A B : Type} [Codec A] [Codec B]

private theorem head_marker (xs : List A) (ys : List B) :
    (letters (packet xs ys) 0).head? = some .node := rfl

private theorem cons_tag (x : A) (xs : List A) (ys : List B) :
    (letters (packet (x :: xs) ys) 0)[1]? = some .node := rfl

private theorem nil_tag (ys : List B) :
    (letters (packet ([] : List A) ys) 0)[1]? = some (.bit false) := rfl

private theorem boundarySize (p : Dispatch.Programs) (xs : List A) (ys : List B) {V : ℕ}
    (hx : size xs ≤ V) (hy : size ys ≤ V) (j : Prog.Ix p.area) :
    ((p.ready (letters (packet xs ys))).stack j).length ≤ V + 2 := by
  cases j with
  | none => exact Nat.zero_le _
  | some j =>
    change ((letters (packet xs ys) j.val).map Sum.inl).length ≤ V + 2
    rw [List.length_map]
    by_cases h₀ : j.val = 0
    · simp only [h₀, packet, ready, letters_here, Tree.spell_length, List.length_append,
        Tree.count]
      simp [letters, pile, show size xs = (send xs).count from rfl] at hx ⊢
      omega
    by_cases h₁ : j.val = 1
    · rw [h₁]
      unfold packet ready
      rw [pile_far _ _ (by decide), letters_here]
      simpa [letters, size] using hy.trans (Nat.le_add_right _ 2)
    · unfold packet ready
      rw [pile_far _ _ (Ne.symm h₀), pile_far _ _ (Ne.symm h₁)]
      simp [letters]

private theorem reverseSize {A : Type} [Codec A] (xs : List A) : size xs.reverse = size xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h := size_append_right xs.reverse [x]
    simp only [List.reverse_cons, size_cons, size_nil, ih] at *
    omega

private theorem process (p : Dispatch.Programs) {f : A → B} {b : A → ℕ} (C : ℕ)
    (step : ∀ x xs out, Fits [] p.step (packet (x::xs) out) (packet xs (f x::out))
      (C*(b x + size (f x) + 1)))
    (xs : List A) (out : List B) (V W : ℕ) (hx : size xs ≤ V)
    (hy : size ((xs.map f).reverse ++ out) ≤ V)
    (hw : ∀ x ∈ xs, b x + size (f x) + 1 ≤ W) :
    ∃ ticks ≤ xs.length * (2 + C*W),
      Segment p.rule (p.ready (letters (packet xs out))) ticks
        (p.ready (letters (packet ([] : List A) ((xs.map f).reverse ++ out)))) (V+2+(2+C*W)) := by
  have ho : size out ≤ V := by
    have := size_append_right (xs.map f).reverse out
    have := size_pos (xs.map f).reverse
    omega
  induction xs generalizing out with
  | nil =>
    refine ⟨0, by simp, ?_⟩
    simp only [List.map_nil, List.reverse_nil, List.nil_append]
    exact (Segment.of_cost (Trace.nil _) (boundarySize p _ _ hx ho) (le_refl _)).mono (by omega)
  | cons x xs ih =>
    have hxt : size xs ≤ V := by simp only [size_cons] at hx; omega
    have hyt : size ((xs.map f).reverse ++ f x :: out) ≤ V := by simpa using hy
    have hopt : size (f x :: out) ≤ V := by
      have := size_append_right (xs.map f).reverse (f x :: out)
      have := size_pos (xs.map f).reverse
      omega
    obtain ⟨t,ht,h⟩ := step x xs out
    have hh : 2 + t ≤ 2 + C * W := by
      have := Nat.mul_le_mul_left C (hw x List.mem_cons_self)
      omega
    have s₁ := Segment.of_cost (p.run_step (r := letters (packet (x::xs) out))
      (head_marker _ _) (cons_tag _ _ _) h) (boundarySize p _ _ hx ho) hh
    obtain ⟨s,hs,s₂⟩ := ih (f x :: out) hxt hyt
      (fun z hz => hw z (List.mem_cons_of_mem _ hz)) hopt
    refine ⟨(2+t)+s, ?_, ?_⟩
    · rw [List.length_cons, Nat.succ_mul]
      omega
    · simpa using s₁.trans s₂

/-- Actual stack-machine implementation of a whole mapped pass. The input
preparation command may also scan or repack the two original streams.
Its budget and both array volumes are charged once. -/
theorem mapStack {I : Type} {f : A → B} {b : A → ℕ} (call : Computes b f)
    {V W : I → ℕ} {q : I → Tree} {xs : I → List A}
    (prep : Task V q (fun i => send (xs i)))
    (hq : ∀ i, (q i).count ≤ V i) (hx : ∀ i, size (xs i) ≤ V i)
    (hy : ∀ i, size ((xs i).map f) ≤ V i)
    (hw : ∀ i, ∀ x ∈ xs i, b x + size (f x) + 1 ≤ W i) :
    ∃ p : Dispatch.Programs, ∃ D : ℕ, ∀ i,
      ∃ t ≤ D*(V i + (xs i).length * W i + 1),
        Segment p.rule (SM.origin p.start p.output ((q i).spell.map Sum.inl)) t
          (p.done (raw (send ((xs i).map f)).spell)) (D*(V i+W i+1)) := by
  obtain ⟨c,C,hc⟩ := exists_step call
  have rev : Easy (fun l : List A => l.reverse) := Easy.reverse
  have first := prep.compose (rev.on xs)
  obtain ⟨a,P,ha⟩ := first
  let p : Dispatch.Programs := ⟨a.join loadCmd, c, emitCmd⟩
  let D := 1000 + 5*P + 5*C
  refine ⟨p, D, fun i => ?_⟩
  let v := V i
  let w := W i
  let l := xs i
  have hinit := (ha i [] (fun _ => [])).join (fits_load (Y := B) l.reverse _ [])
  obtain ⟨s,hs,load⟩ := hinit
  rw [letters_pile_empty] at load
  have hin : size l ≤ v := hx i
  have hout : size (l.map f) ≤ v := hy i
  have hs' : s ≤ (2*P + 202) * (v+1) := by
    change s ≤ P*(V i+size l+1)+200*(size l.reverse+1)+2 at hs
    rw [reverseSize] at hs
    have hp := Nat.mul_le_mul_left P (show V i+size l+1 ≤ 2*(v+1) by dsimp [v] at *; omega)
    nlinarith
  have start := Segment.of_cost (p.run_load load) (fun j =>
    (p.initial_height (q i).spell j).trans (by simpa using hq i)) hs'
  have step' x ys out := hc x ys out (fun _ => []) []
  have hout' : (l.reverse.map f).reverse ++ [] = l.map f := by simp
  obtain ⟨t,ht,run⟩ := process p C step' l.reverse [] v w
    (by rwa [reverseSize]) (by simpa only [hout'] using hout)
    (fun x hx' => hw i x (by simpa [l] using hx'))
  rw [hout'] at run
  obtain ⟨u,hu,emit⟩ := fits_emit (X := A) (l.map f) (fun _ => []) []
  rw [letters_pile_empty] at emit
  have hu' : 2+u ≤ 202*(v+1) := by
    have := Nat.mul_le_mul_left 200 (Nat.succ_le_succ hout)
    omega
  have final := Segment.of_cost (p.run_emit (r := letters (packet ([] : List A) (l.map f)))
    (head_marker _ _) (nil_tag _) emit)
    (boundarySize p _ _ ((show size ([] : List A) = 1 from rfl) ▸ (size_pos l).trans_le hin) hout) hu'
  have ds : v + (2*P+202)*(v+1) ≤ D*(v+w+1) := by unfold D; nlinarith
  have dm : v+2+(2+C*w) ≤ D*(v+w+1) := by unfold D; nlinarith
  have de : v+2+202*(v+1) ≤ D*(v+w+1) := by unfold D; nlinarith
  have all := ((start.mono ds).trans (run.mono dm)).trans (final.mono de)
  rw [p.initial_origin] at all
  refine ⟨_, ?_, all⟩
  have hlen : l.length ≤ v := by have := costSum_le_length_size l; omega
  simp only [List.length_reverse] at ht
  have ht' : t ≤ 2*v+C*(l.length*w) := by
    have : l.length*(2+C*w) = 2*l.length+C*(l.length*w) := by ring
    omega
  change s+t+(2+u) ≤ D*(v+l.length*w+1)
  let localWork := l.length*w
  change t ≤ 2*v+C*localWork at ht'
  change _ ≤ (1000+5*P+5*C)*(v+localWork+1)
  ring_nf at hs' hu' ht' ⊢
  omega

end ProductDriver

end NearSquareRoot
end Computability
end OAI
