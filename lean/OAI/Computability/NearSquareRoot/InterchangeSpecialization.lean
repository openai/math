import OAI.Computability.IntegerMultiplication.Port.Span

/-!
# A single radix for the rational address instructions

The instruction set is finite once the shape of a stage is fixed. The prime
chosen here works for all positive field widths at once. Products,
inverse identities and zero entries of the address matrices are preserved.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open IntegerMultiplication.Port Finset Matrix

variable {I J K : Type*} {R : Type} [CommRing R]

/-- Entrywise interpretation with invertible denominators in the addressed ring. -/
def MatrixToken (A : Matrix I J ℚ) (B : Matrix I J R) : Prop :=
  ∀ i j, Token (A i j) (B i j)

private theorem token_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (g : ι → R)
    (h : ∀ i ∈ s, Token (f i) (g i)) : Token (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Token.zero : Token 0 (0 : R))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (mem_insert_self ..)).add (ih (fun j hj => h j (mem_insert_of_mem hj)))

namespace MatrixToken

theorem unique {A : Matrix I J ℚ} {B C : Matrix I J R}
    (h : MatrixToken A B) (g : MatrixToken A C) : B = C := by
  ext i j
  exact (h i j).unique (g i j)

theorem one [DecidableEq I] : MatrixToken (1 : Matrix I I ℚ) (1 : Matrix I I R) := by
  intro i j
  by_cases h : i = j
  · simpa [Matrix.one_apply, h] using (Token.unit : Token 1 (1 : R))
  · simpa [Matrix.one_apply, h] using (Token.zero : Token 0 (0 : R))

theorem mul [Fintype J] {A : Matrix I J ℚ} {B : Matrix J K ℚ}
    {A' : Matrix I J R} {B' : Matrix J K R} (hA : MatrixToken A A') (hB : MatrixToken B B') :
    MatrixToken (A * B) (A' * B') := by
  intro i k
  apply token_sum
  exact fun j _ => (hA i j).mul (hB j k)

theorem prod [Fintype I] [DecidableEq I] {T : Type*} (s : List T)
    (A : T → Matrix I I ℚ) (A' : T → Matrix I I R) (h : ∀ a ∈ s, MatrixToken (A a) (A' a)) :
    MatrixToken ((s.map A).prod) ((s.map A').prod) := by
  induction s with
  | nil => exact one
  | cons a s ih =>
    exact mul (h a (.head ..)) (ih (fun b hb => h b (.tail _ hb)))

end MatrixToken

/-- One finite catalog and one prime suffice for every exponent and every
address matrix in a fixed local program. Positive rational coefficients need
not be integral and the exponent may change between recursive calls. -/
theorem exists_instruction_radix {T I : Type*} [Fintype T] [Fintype I] [DecidableEq I]
    (W : ℕ) (A : T → Matrix I I ℚ) :
    ∃ b : ℕ, b.Prime ∧ W < b ∧ ∀ f : ℕ,
      ∃ A' : T → Matrix I I (ZMod (b^f)),
        (∀ a, MatrixToken (A a) (A' a)) ∧
        (∀ a i j, A a i j = 0 → A' a i j = 0) ∧
        (∀ a i j, A a i j ≠ 0 → IsUnit (A' a i j)) ∧
        (∀ s t : List T, (s.map A).prod = (t.map A).prod →
          (s.map A').prod = (t.map A').prod) := by
  classical
  let vals := (Finset.univ : Finset (T × I × I)).image fun v => A v.1 v.2.1 v.2.2
  obtain ⟨b, hb, _, hbound⟩ := eventually (insert (W : ℚ) vals)
  have hW := (hbound _ (mem_insert_self ..)).2
  have ha (a : T) (i j : I) := hbound (A a i j)
    (mem_insert_of_mem (s := vals)
      (Finset.mem_image.mpr ⟨(a,i,j), mem_univ _, rfl⟩))
  refine ⟨b, hb, by simpa using hW, fun f => ?_⟩
  let A' : T → Matrix I I (ZMod (b^f)) := fun a i j => read b f (A a i j)
  have hA (a : T) : MatrixToken (A a) (A' a) := fun i j =>
    match_denom hb f (A a i j) (ha a i j).1
  refine ⟨A', hA, ?_, ?_, ?_⟩
  · intro a i j hz
    have hi := hA a i j
    rw [hz] at hi
    exact hi.unique Token.zero
  · intro a i j hn
    exact recorded hb f (A a i j) (ha a i j).1 (ha a i j).2 hn
  · intro s t heq
    have hs := MatrixToken.prod s A A' (fun a _ => hA a)
    rw [heq] at hs
    exact hs.unique (MatrixToken.prod t A A' (fun a _ => hA a))

/-- The finite program can store a single signed numerator/denominator pair
per rational entry. Its P192 interpretation is valid at every recursive width.
The option is empty precisely for rational zero, so invertible diagonals
supply a `Span` directly. -/
theorem exists_instruction_pinpoints (W : ℕ) (coeff : Finset ℚ) :
    ∃ b : ℕ, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      ∀ x ∈ coeff, (code x = none ↔ x = 0) ∧ ∀ f, Token x ((code x).stamp f) := by
  classical
  obtain ⟨b, hb, _, hbound⟩ := eventually (insert (W : ℚ) coeff)
  have hW := (hbound _ (mem_insert_self ..)).2
  have hlookup (x : ℚ) (hx : x ∈ coeff) : ∃ c : Pinpoint b,
      (c = none ↔ x = 0) ∧ ∀ f, Token x (c.stamp f) := by
    by_cases hz : x = 0
    · subst x
      exact ⟨none, by simp, fun _ => Token.zero⟩
    have he := hbound x (mem_insert_of_mem hx)
    obtain ⟨c,hc⟩ := Pinpoint.from_rat x hb he.1 he.2
    refine ⟨c, ?_, hc⟩
    suffices c ≠ none by simp [this,hz]
    intro hc0
    have hr := recorded hb 1 x he.1 he.2 hz
    have hu := (hc 1).unique (match_denom hb 1 x he.1)
    rw [hc0] at hu
    have hb' : 1 < b^1 := by simpa using hb.one_lt
    have : Fact (1 < b^1) := ⟨hb'⟩
    rw [← hu] at hr
    exact not_isUnit_zero hr
  let code (x : ℚ) : Pinpoint b := if hx : x ∈ coeff then (hlookup x hx).choose else none
  refine ⟨b, hb, by simpa using hW, code, fun x hx => ?_⟩
  simpa [code, hx] using (hlookup x hx).choose_spec

end Interchange

end NearSquareRoot
end Computability
end OAI
