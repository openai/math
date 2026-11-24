import OAI.Computability.VPVNP.RankQueryGramScalar
import OAI.Computability.VPVNP.RankQueryTagSpace

/-!
# Storage of a signed weighted Gram coefficient call

The two input-matrix reads may take singly exponential time. Their stack
space bound is reused for each read. The fixed binary index program and
finite-field operations add polynomial storage independently of the time
spent inside either input query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.GramScalar

open RAMTape BurstRAM Dispatch Engine UniversalCountStack

/-- Peak stack height for a signed Gram coefficient, reusing the same read cap `S` for both
entries and allowing for index dispatch from height `A` and local field arithmetic. -/
def space (w v e A S : ℕ) :=
  max (A + Operation.gram.clock w) S + SliceArithmetic.MultiplyCall.callCap e v + 7*(e*v)+3 +
    (5*(e*v)+2+SliceArithmetic.AddCall.callCap e v+1)

variable {K : Type} [DecidableEq K] {p e n m w v B S A d : ℕ} [Fact p.Prime] [NeZero e]
  {c : SliceArithmetic.Vector p e}

theorem machine_bounded (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v) (hw₁ : 1 ≤ w) (hp : (d+1)*widthFactor ≤ w)
    (i j : Fin n) (z : ℕ) (neg : Bool) (persist : Word w) (rs : Registers w)
    (he : ∀ a, gramInput i j z m a < 2^d) (hr : ∀ a, (rs (Code.inReg capacity a)).val = gramInput i j z m a)
    (aux : Stacks K) (hs : ready aux)
    (start : ∀ a, (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux a).length ≤ A) :
    ∃ t ≤ clock w v e B, ∃ rs' aux', ready aux' ∧
      (∀ a, rs' (Code.inReg capacity a) = rs (Code.inReg capacity a)) ∧
      (machine read neg).BoundedRun (space w v e A S) t
        (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux)
        (bank (wordBank persist rs') (GramRead.arithmeticBank v c []
          (scalar v (if neg then -weightedGramEntryCoeff M i j z else weightedGramEntryCoeff M i j z))) aux') := by
  let A₀ := A + Operation.gram.clock w
  let A₁ := max A₀ S + SliceArithmetic.MultiplyCall.callCap e v
  let A₂ := A₁ + 7*(e*v)+3
  have h01 : A₀ ≤ A₁ := (le_max_left ..).trans (Nat.le_add_right ..)
  have h12 : A₁ ≤ A₂ := by dsimp [A₂]; omega
  have h2 : A₂ ≤ space w v e A S := Nat.le_add_right ..
  obtain ⟨t₀,ht₀,regs,h₀,hkeep,hout⟩ := Operation.gram.run _ rs hp he hr Fin.elim0 persist
  let rb := wordBank persist regs
  have load : (Operation.gram.machine.onPorts (Port.words (K := K))).Runs t₀
      (bank (wordBank persist rs) (GramRead.arithmeticBank v c [] []) aux)
      (bank rb (GramRead.arithmeticBank v c [] []) aux) := by
    apply Operation.gram.machine.runs_onPorts_framed (fun _ _ h => Port.words.inj h) h₀
    · intro k; rfl
    · intro k; rfl
    · intro k hk; cases k <;> first | rfl | exact (hk _ rfl).elim
  have hload := spaceRun_of_steps (cap := A₀) load (fun k => Nat.add_le_add (start k) ht₀)
  have words (a : Fin 6) : rb (.reg (Code.outReg capacity a)) =
      UniversalCountStack.digits w (Operation.gram.tree.eval (gramInput i j z m) a) := by
    change wordBits (regs _) = _
    rw [raw_word,hout]
  simp only [gram_words] at words
  by_cases hvalid : i.val+2 ≤ z ∧ z-i.val-2 < m
  · simp only [hvalid] at words
    let k : Fin m := ⟨z-i.val-2,hvalid.2⟩
    let x := M i k * M j k
    have readIn (a : GramRead.Port K) :
        bank rb (GramRead.arithmeticBank v c [] []) aux (reads a) =
          GramRead.bank w i j k (GramRead.arithmeticBank v c [] []) aux a := by
      cases a <;> first | rfl | exact words _
    obtain ⟨t₁,ht₁,s₁,hs₁,h₁⟩ := GramRead.machine_bounded (A := A₀) read M hc hw i j k aux hs
      (fun a => by rw [← readIn]; exact hload.final_cap (reads a))
    have arm : (branch read 1).BoundedRun A₁ t₁
        (bank rb (GramRead.arithmeticBank v c [] []) aux)
        (bank rb (GramRead.arithmeticBank v c [] (scalar v x)) s₁) := by
      change ((GramRead.machine read).onPorts reads).BoundedRun _ _ _ _
      apply FiniteRoutine.BoundedRun.framed reads_injective h₁ (fun a => (hload.final_cap a).trans h01) readIn
      · intro a; cases a <;> first | rfl | exact words _
      · intro a ha; cases a with
        | mul a => exact (ha (.arithmetic a) rfl).elim
        | aux a => exact (ha (.aux a) rfl).elim
        | _ => rfl
    have hselected := TagRouter.digits_bounded (outWord 0) (branch read) hw₁ (by decide : 1 < 2^1) _ _ (words 0) arm
    obtain ⟨t₂,ht₂,h₂⟩ := sign_runs hw neg x rb s₁
    have hsign := spaceRun_of_steps (cap := space w v e A S) h₂
      (fun a => Nat.add_le_add ((arm.final_cap a).trans h12) ht₂)
    refine ⟨t₀+(2*1+t₁)+t₂,by unfold clock; omega,regs,s₁,hs₁,hkeep,?_⟩
    have hx : weightedGramEntryCoeff M i j z = x := by simp [weightedGramEntryCoeff,hvalid.1,hvalid.2,k,x]
    rw [hx]
    exact (((FiniteRoutine.BoundedRun.enlarge hload h01).followedBy hselected).enlarge (h12.trans h2)).followedBy hsign
  · simp only [hvalid,ite_false] at words
    have zero := zero_runs (c := c) hw rb aux
    have arm : (branch read 0).BoundedRun A₂ (7*(e*v)+3)
        (bank rb (GramRead.arithmeticBank v c [] []) aux)
        (bank rb (GramRead.arithmeticBank v c [] (scalar v (0 : Scalar c))) aux) :=
      spaceRun_of_steps zero (fun a => by have h := (hload.final_cap a).trans h01; dsimp [A₂]; omega)
    have hselected := TagRouter.digits_bounded (outWord 0) (branch read) hw₁ (by decide : 0 < 2^1) _ _ (words 0) arm
    obtain ⟨t₂,ht₂,h₂⟩ := sign_runs hw neg (0 : Scalar c) rb aux
    have hsign := spaceRun_of_steps (cap := space w v e A S) h₂ (fun a => Nat.add_le_add (arm.final_cap a) ht₂)
    refine ⟨t₀+(2*1+(7*(e*v)+3))+t₂,by unfold clock; omega,regs,aux,hs,hkeep,?_⟩
    have hx : weightedGramEntryCoeff M i j z = 0 := by simp [weightedGramEntryCoeff,hvalid]
    rw [hx]
    exact (((FiniteRoutine.BoundedRun.enlarge hload (h01.trans h12)).followedBy hselected).enlarge h2).followedBy hsign

end RankQuery.Stack.GramScalar

end VPVNP
end Computability
end OAI
