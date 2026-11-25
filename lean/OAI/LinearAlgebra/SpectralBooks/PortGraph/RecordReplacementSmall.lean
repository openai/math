import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementSmallShape
import OAI.LinearAlgebra.SpectralBooks.BoundedPatchReplacementSmall

/-! # The one-role patch coefficient and its circuit

The coefficient of the unique role is the entire old patch evaluated at the
named boundary tuple. The common word width can exceed the old stub width.
Out-of-range tuples read a zero entry from the same batch circuit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators
namespace PortGraph.ReplacementTemplate

open PlanarPatch Arithmetic

variable {B : Type} (direction : B → Bool) {q D : ℕ} {R : Type*}

/-- A boundary tuple in the common wire alphabet selects an old entry exactly
when all its coordinates lie in the old alphabet. -/
def padStubs [Zero R] (U : (B → Fin q) → R) (x : B → Fin D) : R :=
  if h : ∀ b, (x b).val < q then U (fun b => ⟨(x b).val,h b⟩) else 0

@[simp] theorem padStubs_castLE [Zero R] (hq : q ≤ D) (U : (B → Fin q) → R)
    (x : B → Fin q) : padStubs U (fun b => (x b).castLE hq) = U x := by
  exact dite_eq_left (fun b => (x b).isLt)

/-- The coefficient on the numbered ports at the single role. -/
def singleCoefficient [Zero R] (U : (B → Fin q) → R) (v : Unit)
    (a : LocalPort (singleRole direction) v → Fin D) : R :=
  padStubs U (fun b => a ((singlePortEquiv direction v).symm b))

/-- The same coefficient with separate arguments for internal and boundary ports,
as required by open contraction. -/
def singleTable [Zero R] (U : (B → Fin q) → R) :
    (singleRole direction).graph.StubTable (singleRole direction).attach (Fin D) R :=
  fun v a s => singleCoefficient direction U v (Sum.elim a s)

/-- Summing over the empty internal wiring and multiplying over the single
role evaluates its table at the given stub tuple. -/
theorem single_openValue [CommSemiring R] (U : (B → Fin q) → R) (x : B → Fin D) :
    (singleRole direction).graph.openValue (singleRole direction).attach
      (singleTable direction U) x = padStubs U x := by
  change (∑ _y : Empty → Fin D, ∏ _v : Unit, padStubs U x) = padStubs U x
  simp

/-- At embedded boundary indices, replacing the old patch by the one-role
template preserves its open contraction over any commutative semiring. -/
theorem single_openValue_old {V E : Type*} [Fintype V] [Fintype E] [CommSemiring R]
    (G : PortGraph V E) (attach : B → V) (U : G.StubTable attach (Fin q) R)
    (hq : q ≤ D) (x : B → Fin q) :
    (singleRole direction).graph.openValue (singleRole direction).attach
      (singleTable direction (G.openValue attach U)) (fun b => (x b).castLE hq) =
      G.openValue attach U x :=
  (single_openValue direction (G.openValue attach U) (fun b => (x b).castLE hq)).trans
    (padStubs_castLE hq _ x)

variable {V E F I : Type*} [Fintype V] [Fintype E] [Field F]
  (G : PortGraph V E) (attach : B → V)

/-- Every padded coefficient comes from the direct open-tensor formula or
from the constant zero formula. -/
theorem singleCoefficient_hasFormula (U : G.StubTable attach (Fin q) (MvPolynomial I F))
    (hU : ∀ v a s, HasFormula 1 (U v a s)) (v : Unit)
    (a : LocalPort (singleRole direction) v → Fin D) :
    HasFormula ((Fintype.card (E → Fin q) + 1) * (Fintype.card V + 1))
      (singleCoefficient direction (G.openValue attach U) v a) := by
  unfold singleCoefficient padStubs
  split
  · exact G.small_stub_formula attach q U hU _
  · exact (show HasFormula 1 (0 : MvPolynomial I F) by simpa using HasFormula.const (I := I) (0 : F)).mono
      (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

/-- A common exponential bound on every role coefficient for patches of at
most `K` vertices and degree at most four. -/
theorem singleCoefficient_hasFormula_bound [Fintype B] {K w : ℕ}
    (hK : Fintype.card V ≤ K)
    (hdeg : ∀ v, Fintype.card (G.Port v) + Fintype.card {b // attach b = v} ≤ 4)
    (U : G.StubTable attach (Fin (2^w)) (MvPolynomial I F))
    (hU : ∀ v a s, HasFormula 1 (U v a s)) (v : Unit)
    (a : LocalPort (singleRole direction) v → Fin D) :
    HasFormula (2^((5*K+5)*(w+1))) (singleCoefficient direction (G.openValue attach U) v a) := by
  apply (singleCoefficient_hasFormula direction G attach U hU v a).mono
  have he : Fintype.card E ≤ 4*K := by
    have h := (G.closed_size_bounds attach hK hdeg).2
    rw [Fintype.card_sum] at h
    omega
  have hr : 2^(w*(4*K))+1 ≤ 2^(w*(4*K)+1) := by
    rw [pow_succ]; have := Nat.two_pow_pos (w*(4*K)); omega
  calc
    _ = (2^(w*Fintype.card E)+1) * (Fintype.card V+1) := by simp [pow_mul]
    _ ≤ 2^(w*(4*K)+1) * 2^(K+1) := Nat.mul_le_mul
      ((Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w he)) 1).trans hr)
      ((Nat.succ_le_succ hK).trans Nat.lt_two_pow_self.le)
    _ ≤ _ := by rw [← pow_add]; apply Nat.pow_le_pow_right (by decide); nlinarith

/-- One program computes the role coefficient at every padded input. Reusing
the old batch circuit requires only a constant register for illegal tuples. -/
theorem singleCoefficient_program [Fintype B] {K w : ℕ} (hK : Fintype.card V ≤ K)
    (hdeg : ∀ v, Fintype.card (G.Port v) + Fintype.card {b // attach b = v} ≤ 4)
    (hsmall : Fintype.card B ≤ 3)
    (U : G.StubTable attach (Fin (2^w)) (MvPolynomial I F))
    (hU : ∀ v a s, HasFormula 1 (U v a s)) :
    ∃ (r : ℕ) (P : Program F I r)
      (out : (v : Unit) → (LocalPort (singleRole direction) v → Fin D) → Fin r),
      (∀ v a, registerPolynomial P (out v a) =
        singleCoefficient direction (G.openValue attach U) v a) ∧
      P.cost ≤ 2^((5*K+5)*(w+1)) := by
  obtain ⟨r,P,o,hp,hc⟩ := G.small_stub_program attach hK hdeg hsmall U hU
  let x (v : Unit) (a : LocalPort (singleRole direction) v → Fin D) (b : B) :=
    a ((singlePortEquiv direction v).symm b)
  let out (v : Unit) (a : LocalPort (singleRole direction) v → Fin D) : Fin (r+1) :=
    if h : ∀ b, (x v a b).val < 2^w then (o (fun b => ⟨_,h b⟩)).succ else 0
  refine ⟨r+1,P.step (.constant 0),out,?_,?_⟩
  · intro v a
    change registerPolynomial _ (out v a) = padStubs _ (x v a)
    unfold out padStubs
    split
    · exact hp _
    · simp [gatePolynomial]
  · simpa [Program.cost_step, Gate.cost] using hc

end PortGraph.ReplacementTemplate

end

end SpectralBooks
end LinearAlgebra
end OAI
