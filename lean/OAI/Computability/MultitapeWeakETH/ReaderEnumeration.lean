import OAI.Computability.MultitapeWeakETH.CompressionCounts

/-! # Deterministic enumeration of the compressor's self-delimiting choices

Parse each fixed-length candidate once and accept only zero padding. This
gives a streaming sum even when valid codes have different lengths. The
canonical-padding check prevents repeated contributions to an exact count.
-/

namespace OAI.Computability.MultitapeWeakETH.ReaderEnumeration

open VPVNP.CompressorRecords Finset
variable {J R : Type} (parser : ChoiceReader J)

def padded (L : ℕ) (j : J) :=
  parser.encode j ++ List.replicate (L-(parser.encode j).length) false

/-- The concrete acceptance test compares the suffix with zeroes. -/
def decode (bits : List Bool) : Option J :=
  (parser.read bits).bind fun (j,tail) =>
    if tail = List.replicate tail.length false then some j else none

theorem decode_iff {bits : List Bool} {j : J} :
    decode parser bits = some j ↔ (parser.encode j).length ≤ bits.length ∧
      bits = padded parser bits.length j := by
  unfold decode
  cases h : parser.read bits with
  | none =>
    simp only [Option.bind_none,reduceCtorEq,false_iff,not_and]
    intro _ eq
    have parse := (parser.read_iff bits j _).mpr eq
    rw [h] at parse
    contradiction
  | some pair =>
    obtain ⟨i,tail⟩ := pair
    have eq := (parser.read_iff _ _ _).mp h
    have len := congrArg List.length eq
    rw [List.length_append] at len
    constructor
    · intro ok
      simp only [Option.bind_some] at ok
      split at ok
      · rename_i zeros
        obtain rfl := Option.some.inj ok
        refine ⟨by omega,?_⟩
        unfold padded
        rw [show bits.length-(parser.encode i).length = tail.length by omega]
        exact eq.trans (congrArg (parser.encode i ++ ·) zeros)
      · contradiction
    · rintro ⟨_,matchBits⟩
      have read := (parser.read_iff bits j _).mpr matchBits
      rw [h] at read
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
      simp

/-- Exhaust the Boolean tree with one callback per complete word. -/
def treeSum [AddCommMonoid R] (term : List Bool → R) (k : ℕ) (acc : List Bool) : R :=
  match k with
  | 0 => term acc
  | n+1 => treeSum term n (false::acc) + treeSum term n (true::acc)

theorem treeSum_eq [AddCommMonoid R] (term : List Bool → R) (k : ℕ) (acc : List Bool) :
    treeSum term k acc = ∑ word : Fin k → Bool, term ((List.ofFn word) ++ acc) := by
  induction k generalizing acc with
  | zero => simp [treeSum]
  | succ k ih =>
    rw [treeSum,ih,ih]
    let e := Fin.snocEquiv (fun _ : Fin (k+1) => Bool)
    symm
    rw [← e.sum_comp, Fintype.sum_prod_type, Fintype.sum_bool,add_comm]
    have snoc (x : Fin k → Bool) (b : Bool) : List.ofFn (e (b,x)) = List.ofFn x ++ [b] := by
      change List.ofFn (Fin.snoc x b) = _
      rw [List.ofFn_succ',List.concat_eq_append]
      simp
    simp only [snoc,List.append_assoc,List.cons_append,List.nil_append]

open scoped Classical in
theorem sum_decode [Fintype J] [AddCommMonoid R] (L : ℕ) (bound : ∀ j, (parser.encode j).length ≤ L)
    (term : J → R) :
    treeSum (fun bits => (decode parser bits).elim 0 term) L [] = ∑ j, term j := by
  let key (j : J) : Fin L → Bool := fun i =>
    (padded parser L j)[i.val]'(by simp [padded,bound j])
  have repr (j : J) : List.ofFn (key j) = padded parser L j := by
    apply List.ext_getElem <;> simp [key,padded,bound j]
  have exactly (w : Fin L → Bool) (j : J) : decode parser (List.ofFn w) = some j ↔ w = key j := by
    rw [decode_iff,List.length_ofFn, and_iff_right (bound j),← repr j]
    exact List.ofFn_injective.eq_iff
  rw [treeSum_eq]; simp only [List.append_nil]
  calc
    _ = ∑ w : Fin L → Bool, ∑ j, if w = key j then term j else 0 := by
      apply sum_congr rfl
      intro w _
      simp_rw [← exactly]
      cases h : decode parser (List.ofFn w) with
      | none => simp
      | some j =>
        simp only [Option.some.injEq,Option.elim_some]
        rw [sum_eq_single j]
        · simp
        · intro i _ ne; simp [Ne.symm ne]
        · simp
    _ = _ := by rw [sum_comm]; simp

end OAI.Computability.MultitapeWeakETH.ReaderEnumeration
