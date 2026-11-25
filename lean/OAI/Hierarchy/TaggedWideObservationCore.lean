import OAI.Hierarchy.TaggedShorterControlUnique

namespace OAI
/-! # Observed terminal words of an arbitrary native control verifier -/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical BigOperators

/-- Twenty-eight address-width slices suffice for the seven words of
the native record at width 2h+1, including its exposed-machine extension. -/
theorem linear_record_fits {h m : ℕ} (hh : 0<h) (padded : h ≤ m) :
    TaggedShorterHistoryOrder.RecordWidth ((2*h+1)+1) ≤ 28*m := by
  rw [TaggedShorterHistoryOrder.recordWidth_eq]
  omega

/-- The same 28 shorter-tagged sorts suffice for an arbitrary native
word width, including the actual geometric controller's fixed overhead. -/
theorem record_fits_width {W m : ℕ} (pad : W+1≤4*m) :
    TaggedShorterHistoryOrder.RecordWidth (W+1) ≤ 28*m := by
  rw [TaggedShorterHistoryOrder.recordWidth_eq]
  omega

/-- The native sort/CPU tensor with its observed final-memory words summed
against a scalar, and its sort holes filled by width-one predicates. -/
def observationSum {F : Type*} [CommRing F] {w p r k S f u m : ℕ} (a : ℕ)
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (addr : Fin u → Word w) (header : ℕ → Word w) (hs : S≤2^w) (clock : f+u≤2^(w+1))
    (φ : (Fin u → Word (w+1)) → F) : F :=
  let high : S≤2^(w+1) := hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  ∑ raw : TaggedShorterClock.Pin w r f → Bool, ∑ seen : Fin u → Word (w+1),
    (∑ z : Hole m a → Bool,
      TypedWiring.value (network (F:=F) M hw hp st high clock (wide ∘ addr))
        (Sum.elim (controls (wide ∘ header) raw seen) z) *
          ∏ b : Fin a, Tagged.coeff F m m (fun j => z (b,j))) * φ seen

/-- A weight can jointly inspect the acceptance flag, every mask and common
ID, and the scalar/site fields of the whole finite menu. Closing the actual
tagged sort holes and summing the guessed history and output words returns
this weight evaluated at the actual checked machine post-state. -/
theorem observed_weight {F : Type*} [CommRing F] {w p r k S f u t m a : ℕ}
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (addr : Fin u → Word w) (header : ℕ → Word w) (hs : S≤2^w)
    (clock : f+u≤2^(w+1)) (fits : S+(f+u)≤2^m) (positive : 0<a)
    (room : TaggedShorterHistoryOrder.RecordWidth (w+1)≤a*m)
    (done : Config w p r) (out : Memory w) (result : Option (Word w))
    (inside : t<f)
    (ran : RAM.advance M.program t (M.program.start st) (initialMemory S header)=some (done,out))
    (halt : M.program.step done=.finish result)
    (φ : (Fin u → Word (w+1)) → F) :
    observationSum (m:=m) a M hw hp st addr header hs clock φ = φ (fun i => wide (out (addr i).val)) := by
  unfold observationSum
  let high : S≤2^(w+1) := hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  let expected := fun i => wide (out (addr i).val)
  obtain ⟨witness,unique⟩ := unique_native M hw hp st S f addr header hs done out result inside ran halt
  calc
    _ = ∑ raw : TaggedShorterClock.Pin w r f → Bool, ∑ seen : Fin u → Word (w+1),
        if raw=witness ∧ seen=expected then φ seen else 0 := by
      apply Finset.sum_congr rfl
      intro raw _
      apply Finset.sum_congr rfl
      intro seen _
      rw [contract M hw hp st high clock (wide ∘ addr) fits positive room (wide ∘ header) raw seen,
        unique raw seen]
      by_cases live : raw=witness ∧ seen=expected <;> simp only [expected] at live ⊢ <;> simp [live]
    _ = φ expected := by
      rw [Finset.sum_eq_single witness]
      · simp
      · intro other _ distinct
        simp [distinct]
      · simp

end Hierarchy.TaggedShorterControlHistory

end
end OAI
