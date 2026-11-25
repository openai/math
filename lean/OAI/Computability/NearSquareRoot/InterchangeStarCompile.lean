import OAI.Computability.NearSquareRoot.InterchangeStarFamily
import OAI.Computability.NearSquareRoot.InterchangeStarGather
import OAI.Computability.NearSquareRoot.InterchangeStarOrder
import OAI.Computability.NearSquareRoot.InterchangePivot

/-!
# Compiling batches of rational field operations

After moving the common source to the first position, or the common
destination to the last, each addition is an earlier-controlled shift.
Two swaps restore the layout. The six-call upper bound counts physical
cross-wing pivots and does not depend on the number of shifts in a batch.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open IntegerMultiplication.Port Matrix

variable {I J : Type} [DecidableEq J] [DecidableEq I] [Fintype I] {p : ℕ}

/-- One program works for all prime-power digit widths. This property
requires the action on unselected occupied address fields as well. -/
def CompilesOn (slot : I → Spot J) (rank : J → ℕ) (cost : ℕ)
    (M : (f : ℕ) → Matrix I I (Tower p f)) : Prop :=
  ∃ program : List (Lag J p), (∀ v ∈ program, v.legal rank) ∧
    (program.map Lag.prices).sum ≤ cost ∧
    ∀ f (x : Duplex J (Tower p f)),
      let y := program.foldl (Lag.fire f) x
      (∀ i : I, hear y (slot i) = (M f *ᵥ (fun j => hear x (slot j))) i) ∧
      (∀ w, (∀ i, w ≠ slot i) → hear y w = hear x w)

theorem compile_star (slot : I → Spot J) (inj : Function.Injective slot)
    (rank : J → ℕ) (jr : Function.Injective rank)
    (code : ℚ → Pinpoint p) (s : List (TransvectionStruct I ℚ)) (hstar : IsStar s) :
    CompilesOn slot rank 6 (fun f => (s.map (encodedTransvection code f)).prod) := by
  suffices h : ∃ a b : Spot J, ∀ t ∈ s,
      Lag.early rank (Equiv.swap a b (slot t.j)) (Equiv.swap a b (slot t.i)) by
    obtain ⟨a,b,ho⟩ := h
    obtain ⟨l,hl,hc,he⟩ := InterchangePivot.compile (p := p) rank a b
    exact gatherProgram_conjugate slot inj rank code s a b l hl hc he ho
  obtain ⟨i, ht⟩ | ⟨j, ht⟩ := hstar
  · obtain ⟨b, hb⟩ := exists_last_swap slot rank i inj jr
    refine ⟨slot i,b,fun t hm => ?_⟩
    have h := ht t hm
    simpa [← h] using hb t.j (h ▸ t.hij.symm)
  · obtain ⟨b, hb⟩ := exists_first_swap slot rank j inj jr
    refine ⟨slot j,b, fun t hm => ?_⟩
    have h := ht t hm
    simpa [← h] using hb t.i (h ▸ t.hij)

namespace CompilesOn

variable {slot : I → Spot J} {rank : J → ℕ}

omit [DecidableEq I] in
theorem mono {c d} {A : (f : ℕ) → Matrix I I (Tower p f)} (ha : CompilesOn slot rank c A)
    (hcd : c ≤ d) : CompilesOn slot rank d A := by
  obtain ⟨l,hl,hc,he⟩ := ha
  exact ⟨l,hl,hc.trans hcd,he⟩

theorem one : CompilesOn slot rank 0 (fun f => (1 : Matrix I I (Tower p f))) := by
  exact ⟨[], by simp, by simp, by simp⟩

omit [DecidableEq I] in
/-- A matrix product is executed in reverse order. -/
theorem mul {c d : ℕ} {A B : (f : ℕ) → Matrix I I (Tower p f)}
    (ha : CompilesOn slot rank c A) (hb : CompilesOn slot rank d B) :
    CompilesOn slot rank (c+d) (fun f => A f * B f) := by
  obtain ⟨l,hl,hc,he⟩ := ha
  obtain ⟨k,hk,hd,hg⟩ := hb
  refine ⟨k++l, fun v hv => (List.mem_append.mp hv).elim (hk v) (hl v), ?_, ?_⟩
  · simp only [List.map_append, List.sum_append]
    omega
  · intro f x
    dsimp only
    rw [List.foldl_append]
    let y := k.foldl (Lag.fire f) x
    have hx := hg f x
    have hy := he f y
    have hmain : (fun i => hear y (slot i)) = B f *ᵥ (fun j => hear x (slot j)) := funext hx.1
    constructor
    · intro i
      exact (hy.1 i).trans (by rw [hmain, Matrix.mulVec_mulVec])
    · intro w hw
      exact (hy.2 w hw).trans (hx.2 w hw)

end CompilesOn

/-- Concatenate the schedules in reverse to execute a product of star batches. -/
theorem compile_stars (slot : I → Spot J) (inj : Function.Injective slot)
    (rank : J → ℕ) (jr : Function.Injective rank) (code : ℚ → Pinpoint p)
    (s : List (List (TransvectionStruct I ℚ))) (h : ∀ b ∈ s, IsStar b) :
    CompilesOn slot rank (6*s.length) (fun f => (s.flatten.map (encodedTransvection code f)).prod) := by
  induction s with
  | nil => simpa using (CompilesOn.one (slot := slot) (rank := rank) (p := p))
  | cons b s ih =>
    have hb := compile_star slot inj rank jr code b (h b (.head ..))
    have hs := ih (fun u hu => h u (.tail _ hu))
    simpa [Nat.mul_add, Nat.add_comm] using hb.mul hs

private def diagProgram (slot : I → Spot J) (d : I → Span p) (s : List I) : List (Lag J p) :=
  s.map fun i => Lag.width (slot i) (d i)

omit [Fintype I] in
private theorem diagProgram_effect (slot : I → Spot J) (inj : Function.Injective slot)
    (d : I → Span p) (s : List I) (hs : s.Nodup) (f : ℕ) (x : Duplex J (Tower p f)) :
    let y := (diagProgram slot d s).foldl (Lag.fire f) x
    (∀ i, hear y (slot i) =
      if i ∈ s then (d i).land f * hear x (slot i) else hear x (slot i)) ∧
    (∀ w, (∀ i, w ≠ slot i) → hear y w = hear x w) := by
  induction s generalizing x with
  | nil => simp [diagProgram]
  | cons j s ih =>
    obtain ⟨hj,hs'⟩ := List.nodup_cons.mp hs
    specialize ih hs' (Lag.fire f x (.width (slot j) (d j)))
    refine ⟨?_, ?_⟩
    · intro i
      by_cases e : i = j
      · subst i
        simpa [diagProgram, hj, Lag.fire] using ih.1 j
      · simpa [diagProgram, e, inj.ne e, Lag.fire] using ih.1 i
    · intro w hw
      simpa [diagProgram, Lag.fire, hw] using ih.2 w hw

/-- Scaling individual occupied fields does not require any interchange. -/
theorem compile_diagonal (slot : I → Spot J) (inj : Function.Injective slot)
    (rank : J → ℕ) (d : I → Span p) :
    CompilesOn slot rank 0 (fun f => diagonal (fun i => (d i).land f)) := by
  classical
  let s : List I := Finset.univ.toList
  refine ⟨diagProgram slot d s, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
    exact trivial
  · simp [diagProgram, List.map_map, Function.comp_def, Lag.prices]
  · intro f x
    obtain ⟨hm,ho⟩ := diagProgram_effect slot inj d s (Finset.nodup_toList _) f x
    exact ⟨fun i => by simpa [s, Matrix.mulVec, diagonal_dotProduct] using hm i, ho⟩

/-- Choose one radix for a whole finite collection of address matrices.
Every resulting change of coordinates has a single physical instruction
list acting at all field widths, and uses at most eighteen recursive
cross-wing interchanges per selected field. -/
theorem compile_matrix_family {T : Type*} [Fintype T] (W : ℕ) (extra : Finset ℚ)
    (A : T → Matrix I I ℚ) (hA : ∀ t, IsUnit (A t)) :
    ∃ b : ℕ, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ x ∈ extra, (code x = none ↔ x = 0) ∧ ∀ f, Token x ((code x).stamp f)) ∧
      ∀ t, ∃ M : (f : ℕ) → Matrix I I (Tower b f),
        (∀ f, MatrixToken (A t) (M f)) ∧
        ∀ {J : Type} [DecidableEq J] (slot : I → Spot J) (_ : Function.Injective slot)
          (rank : J → ℕ) (_ : Function.Injective rank), CompilesOn slot rank (18*Fintype.card I) M := by
  obtain ⟨b, hb, hw, code, hex, hall⟩ := exists_star_family W extra A hA
  refine ⟨b, hb, hw, code, hex, fun t => ?_⟩
  obtain ⟨l,r,d,hl,hr,hc,he⟩ := hall t
  refine ⟨_, he, fun {J} _ slot inj rank jr => ?_⟩
  obtain lprog := compile_stars slot inj rank jr code l hl
  obtain rprog := compile_stars slot inj rank jr code r hr
  have dprog := compile_diagonal slot inj rank d
  apply ((lprog.mul dprog).mul rprog).mono
  omega

end Interchange

end NearSquareRoot
end Computability
end OAI
