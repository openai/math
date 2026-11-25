import OAI.Computability.NearSquareRoot.CommonTapes
import OAI.Computability.NearSquareRoot.BoundedProgramCompile

/-! # A shared physical tape index set for register-bounded programs

A finite candidate can have arbitrarily many control locations. The number of its
physical tape heads is bounded by the data-register names used in its syntax plus a
return-address tape and a separate output tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonRegisters

open IntegerMultiplication IntegerMultiplication.Prog
variable {A : Type}

/-- Every data instruction refers to a register below the common cutoff. -/
def Within (R : ℕ) : Prog A → Prop
  | .push i _ | .pop i => i < R
  | .look i f => i < R ∧ ∀ a, Within R (f a)
  | .join p q => Within R p ∧ Within R q
  | .tie p => Within R p
  | .pass | .again _ => True

private theorem touched_lt {c : Prog A} {R : ℕ} (hR : 0 < R) (h : Within R c) :
    touched c < R := by
  cases c <;> simp_all [touched, Within]

theorem sites_within [Fintype A] {R : ℕ} (hR : 0 < R) (c : Prog A) (Γ : Scope A)
    (h : Within R c) : ∀ u ∈ sites Γ c, touched u.2 < R := by
  intro u hu
  induction c generalizing Γ with
  | pass | push | pop | again =>
    rw [sites.eq_def] at hu
    simp only [List.mem_singleton] at hu
    subst u
    exact touched_lt hR h
  | look i f ih =>
    rw [sites.eq_def] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact h.1
    · obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp hu
      exact ih x _ (h.2 x) hx
  | join p q hp hq =>
    rw [sites.eq_def] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hR
    · rcases List.mem_append.mp hu with hu | hu
      · exact hp _ h.1 hu
      · exact hq _ h.2 hu
  | tie p ih =>
    rw [sites.eq_def] at hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hR
    · exact ih _ h hu

theorem used_lt [Fintype A] {R : ℕ} (hR : 0 < R) {p : Prog A} (hp : Within R p)
    {i : ℕ} (hi : i ∈ used (sites [] p)) : i < R := by
  rcases List.mem_cons.mp hi with rfl | hi
  · exact hR
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
    exact sites_within hR p [] hp s hs

/-- Raw machine tapes are the bounded data registers, one return stack, and the output. -/
def indexEmbedding [Fintype A] {R : ℕ} (hR : 0 < R) {p : Prog A} (hp : Within R p) :
    Option (Ix (sites [] p)) ↪ Option (Option (Fin R)) :=
  (Function.Embedding.optionMap (Function.Embedding.optionMap
    ⟨fun i => ⟨i.val, used_lt hR hp i.property⟩, fun _ _ e => Subtype.ext (congrArg Fin.val e)⟩))


/-- A family of programs satisfying the same register cutoff can use identical tape indices.
The literal input and output stay on their designated tapes, including all necessary blanks.
The fixed physical space multiplier accounts for the stationary spare heads. -/
theorem bounded_release_common [Fintype A] {R : ℕ} (hR : 0 < R) {p : Prog A}
    (hp : Within R p) :
    let I := Option (Option (Fin R))
    ∃ (X Q : Type) (_ : Finite X) (_ : Finite Q) (sym : A → X) (blank : X)
      (inp out : I) (start : Q) (m : TM.Rule X Q I) (K : ℕ),
      Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
      ∀ (input : List A) (r : Reg A) (n cap depth : ℕ),
        Space.BoundedRun cap depth [] p (fun i => if i = 0 then input else []) n r →
        ∃ (load : I → TM.Tape X) (done : TM.Config X Q I),
          load inp = TM.Tape.loaded blank (input.map sym) ∧
          (∀ i, i ≠ inp → load i = TM.Tape.loaded blank []) ∧
          Trace (TM.advance m) ⟨start, load⟩ (2*n+1+(r 0).length) done ∧
          TM.advance m done = none ∧ TM.whole blank ((r 0).map sym) (done.tape out) ∧
          VisitsAtMost m ⟨start, load⟩ (2*n+1+(r 0).length) (K * (4 * max cap depth + 5)) := by
  classical
  let J := Option (Option (Fin R))
  let e := indexEmbedding hR hp
  obtain ⟨X,Q,finX,finQ,_,s,b,i,o,q,M,K,si,sb,io,run⟩ := Space.bounded_release_indexed p
  refine ⟨X,Q,finX,finQ,s,b,e i,e o,q,CommonTapes.rule e M,K + Fintype.card J,
    si,sb,e.injective.ne io,?_⟩
  intro input regs n cap depth valid
  obtain ⟨load,done,hl,he,ht,hh,hw,hv⟩ :=
    CommonTapes.run_on_common_tapes e M b i o q _ _ _ _ (run input regs n cap depth valid)
  refine ⟨load,done,hl,he,ht,hh,hw,?_⟩
  obtain ⟨F,size,covers⟩ := hv
  refine ⟨F,size.trans ?_,covers⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _

end CommonRegisters

end NearSquareRoot
end Computability
end OAI
