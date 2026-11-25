import OAI.Computability.NearSquareRoot.PrecisionProductMap

/-! # Physical release of a bounded-space record pass

The input is a single loaded encoded tree. The stack simulation and the
final copy onto the output tape are included in the time and space bounds.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductDriver

open IntegerMultiplication Code Schoolbook

/-- Initial configuration of an array pass with its query serialized in full. -/
noncomputable def loadedQuery {A Q J : Type} (start : Q) (input : J)
    (encode : Ltr → A) (blank : A) (q : Tree) : TM.Config A Q J := by
  classical
  exact ⟨start, fun j => if j = input then TM.Tape.loaded blank (q.spell.map encode)
    else TM.Tape.loaded blank []⟩

/-- A single fixed physical implementation of the indexed stream transformation.
The time and space constants are independent of the query. -/
def TapePass {I : Type*} (time space : I → ℕ) (query reply : I → Tree) : Prop :=
  ∃ (A Q J : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite J)
    (encode : Ltr → A) (blank : A) (input output : J) (start : Q) (m : TM.Rule A Q J)
    (C S : ℕ), Function.Injective encode ∧ (∀ a, encode a ≠ blank) ∧ input ≠ output ∧
    ∀ i, let init := loadedQuery start input encode blank (query i)
    ∃ t finish, Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
      TM.whole blank ((reply i).spell.map encode) (finish.tape output) ∧
      t ≤ C * time i ∧ VisitsAtMost m init t (S * space i)

/-- Absorb fixed constants from one pass's time and space estimates. -/
theorem TapePass.scale {I : Type*} {time space time' space' : I → ℕ}
    {q r : I → Tree} (h : TapePass time space q r) (D E : ℕ)
    (ht : ∀ i, time i ≤ D * time' i) (hs : ∀ i, space i ≤ E * space' i) :
    TapePass time' space' q r := by
  obtain ⟨A, Q, J, hA, hQ, hJ, code, blank, inp, out, start, m, C, S,
    hinj, hblank, hio, run⟩ := h
  refine ⟨A, Q, J, hA, hQ, hJ, code, blank, inp, out, start, m, C*D, S*E,
    hinj, hblank, hio, fun i => ?_⟩
  obtain ⟨t, z, tr, hz, word, cost, cells, bound, contains⟩ := run i
  refine ⟨t, z, tr, hz, word, ?_, cells, ?_, contains⟩
  · rw [Nat.mul_assoc]
    exact cost.trans (Nat.mul_le_mul_left C (ht i))
  · rw [Nat.mul_assoc]
    exact bound.trans (Nat.mul_le_mul_left S (hs i))

theorem mapOnTapes {A B I : Type} [Codec A] [Codec B] {f : A → B} {b : A → ℕ}
    (call : Computes b f) {V W : I → ℕ} {q : I → Tree} {xs : I → List A}
    (prep : Task V q (fun i => send (xs i)))
    (hq : ∀ i, (q i).count ≤ V i) (hx : ∀ i, size (xs i) ≤ V i)
    (hy : ∀ i, size ((xs i).map f) ≤ V i)
    (hw : ∀ i, ∀ x ∈ xs i, b x + size (f x) + 1 ≤ W i) :
    TapePass (fun i => V i + (xs i).length * W i + 1) (fun i => V i + W i + 1)
      q (fun i => send ((xs i).map f)) := by
  classical
  obtain ⟨p, D, run⟩ := mapStack call prep hq hx hy hw
  let J := Prog.Ix p.area
  let Γ := Prog.Sym p.area
  let : Fintype J := Fintype.ofFinite J
  let encode : Ltr → Option Γ := fun a => some (.inl a)
  let K := Fintype.card (Option J)
  refine ⟨Option Γ, Option (SM.PC Γ p.Control J), Option J, inferInstance, inferInstance,
    inferInstance, encode, none, some p.output, none, some (.inl p.start),
    SM.complete p.output p.rule, 2*D+2, K*(4*D+5), ?_, by simp [encode], by simp, ?_⟩
  · exact fun _ _ h => Sum.inl.inj (Option.some.inj h)
  intro i
  obtain ⟨t, ht, seg⟩ := run i
  obtain ⟨done, complete, halt, whole, visited⟩ :=
    complete_run_space (k := p.output) seg.run (p.halt _) seg.height
  rw [p.done_output, List.length_map, Tree.spell_length] at complete visited
  rw [p.done_output] at whole
  let ticks := 2*t+1+size ((xs i).map f)
  refine ⟨ticks, done, ?_, halt, ?_, ?_, ?_⟩
  · simpa only [loadedQuery, List.map_map, encode, Function.comp_def, J, Γ, ticks, size] using complete
  · simpa only [List.map_map, encode, Function.comp_def, J, Γ] using whole
  · have h := hy i
    dsimp [ticks]
    nlinarith [ht]
  · obtain ⟨cells, hcount, contains⟩ := visited
    refine ⟨cells, hcount.trans ?_, ?_⟩
    · change K * (4 * (D * (V i + W i + 1)) + 5) ≤ K * (4*D + 5) * (V i + W i + 1)
      rw [Nat.mul_assoc]
      apply Nat.mul_le_mul_left
      nlinarith
    · simpa only [loadedQuery, List.map_map, encode, Function.comp_def, J, Γ, ticks, size] using contains

end ProductDriver

end NearSquareRoot
end Computability
end OAI
