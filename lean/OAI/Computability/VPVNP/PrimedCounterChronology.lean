import OAI.Computability.VPVNP.PrimedCounterChronologySlots
import OAI.Computability.VPVNP.PrimedCounterSiteLoop
import OAI.Computability.VPVNP.PrimedInputRAMLayoutExecution

/-!
# Exact coefficient count of chronological pair-counter tapes

The cursor visits the two input rectangles, then the sites in row-major order,
and finally all nominated histogram entries. A raw path has one list of branch
bits at every absolute cursor position. Recovering the shared choices at the
first-pass owners and the parse choices in the node slots is parsimonious.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Chronology

open BurstRAM PrimedInputRAM
open scoped Classical

variable {L : Lengths} {n r H s w T : ℕ}

/-- An assignment to all internal primed bits shared by the two groups, including bits read at
several endpoints. -/
abbrev Bits (L : Lengths) (r H w : ℕ) := Internal L r H w → Bool
/-- One private choice list per cursor slot across the two input passes, all site parses and
the final nomination comparisons. -/
abbrev PairTape (n r T : ℕ) :=
  Tape (PrimedInputRAM.positions n r + PrimedInputRAM.positions n r) (2 * 2^r) n (2*n-1) T

/-- One singleton at each designated first-pass owner and an empty list at
every other first-pass position and every copy position. -/
def inputCalls (Q : Layout L n r H w) (bits : Bits L r H w) :
    Fin (PrimedInputRAM.positions n r + PrimedInputRAM.positions n r) → List Bool := fun i =>
  let pass := Q.twoPass (encodeBit w)
  (pass.ops i).bits (bitAt (pass.assignmentEquiv (Q.assignment bits)) i)

private theorem itemBits_injective {M : ℕ} (ops : Fin M → Item w) :
    Function.Injective (fun f : Assignment (fun i => (ops i).owns) =>
      fun i => (ops i).bits (bitAt f i)) := by
  intro a b h
  funext i
  simpa [Item.bits, bitAt, i.property] using congrFun h i.val

theorem inputCalls_injective (Q : Layout L n r H w) : Function.Injective (inputCalls Q) := by
  intro a b h
  let pass := Q.twoPass (encodeBit w)
  have he := (itemBits_injective pass.ops) h
  have ha := pass.assignmentEquiv.injective he
  funext i
  simpa [Layout.assignment] using congrFun ha (Q.internalOwner i)

/-- Primed processor inputs, reindexed in the order of the parse loop. -/
def rowInput (Q : Layout L n r H w) (hdr : Header L → Bool)
    (bits : Bits L r H w) (v : Fin (2 * 2^r)) : Fin n → Bool :=
  input Q.program Q.fits hdr bits (finProdFinEquiv.symm v)

/-- Branch-tape condition tested by the input, site and comparison phases. -/
def Accepts (Q : Layout L n r H w) (hdr : Header L → Bool)
    (d : Fin n) (root : Fin s) (μ : Label n n (Fin s) →₀ ℕ) (raw : PairTape n r T) : Prop :=
  ∃ bits : Bits L r H w, inputPart raw = inputCalls Q bits ∧ AdminEmpty raw ∧
    runSites w d root (rowInput Q hdr bits) (fun v => List.ofFn (nodePart raw v))
      (List.finRange (2 * 2^r)) 0 = some μ

private noncomputable def pathFiberEquiv {I : Type*} {S : ℕ} (hn : n ≤ 2^w) (hs : s ≤ 2^w)
    (d : Fin n) (root : Fin s) (x : I → Fin S → Fin n → Bool)
    (μ : Label n n (Fin s) →₀ ℕ) :
    (Σ a : I, {b : (v : Fin S) → SitePaths w (x a v) d root //
        ∑ v, siteHistogram hn hs hn (x a v) d root (b v) = μ}) ≃
      {b : PairPaths w d root x // totalHistogram hn hs hn d root x b = μ} where
  toFun b := ⟨⟨b.1,b.2.val⟩,b.2.property⟩
  invFun b := ⟨b.val.1,⟨b.val.2,b.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def rowLoopEquiv {K S : ℕ} (hn : n ≤ 2^w) (hs : s ≤ 2^w)
    (d : Fin n) (root : Fin s) (hK : K = 2*d.val + 1)
    (x : Fin S → Fin n → Bool) (μ : Label n n (Fin s) →₀ ℕ) :
    {raw : Fin S → Fin K → List Bool //
        runSites w d root x (fun v => List.ofFn (raw v)) (List.finRange S) 0 = some μ} ≃
      {b : (v : Fin S) → SitePaths w (x v) d root //
        ∑ v, siteHistogram hn hs hn (x v) d root (b v) = μ} := by
  subst K
  exact siteLoopEquiv hn hn hs d root x μ

/-- Extract the shared assignment and all local parses from a complete tape.
The inverse places each choice back at its absolute chronological position. -/
noncomputable def pathEquiv (Q : Layout L n r H w) (hdr : Header L → Bool)
    (d : Fin n) (root : Fin s) (hsize : d.val + 1 = n) (hn : n ≤ 2^w) (hs : s ≤ 2^w)
    (μ : Label n n (Fin s) →₀ ℕ) :
    {raw : PairTape n r T // Accepts Q hdr d root μ raw} ≃
      {b : PairPaths w d root (rowInput Q hdr) //
        totalHistogram hn hs hn d root (rowInput Q hdr) b = μ} := by
  let e := acceptedSlotsEquiv (m := n) (T := T) (inputCalls Q) (inputCalls_injective Q)
    (fun bits (nodes : Fin (2 * 2^r) → Fin (2*n-1) → List Bool) =>
      runSites w d root (rowInput Q hdr bits) (fun v => List.ofFn (nodes v))
        (List.finRange (2 * 2^r)) 0 = some μ)
  have hK : 2*n-1 = 2*d.val + 1 := by omega
  exact (e.trans (Equiv.sigmaCongrRight fun a => rowLoopEquiv hn hs d root hK (rowInput Q hdr a) μ)).trans
    (pathFiberEquiv hn hs d root (rowInput Q hdr) μ)

/-- The raw path count is the integer coefficient on the actual primed
inputs of both groups, including all internal bit assignments. -/
theorem count (Q : Layout L n r H w) (hdr : Header L → Bool)
    (d : Fin n) (root : Fin s) (hsize : d.val + 1 = n) (hn : n ≤ 2^w) (hs : s ≤ 2^w)
    (μ : Label n n (Fin s) →₀ ℕ) :
    (Nat.card {raw : PairTape n r T // Accepts Q hdr d root μ raw} : ℤ) =
      (PairCoefficient.jointPolynomial d root (input Q.program Q.fits hdr)).coeff μ := by
  rw [Nat.card_congr (pathEquiv Q hdr d root hsize hn hs μ),
    pairPath_count hn hs hn d root hsize (rowInput Q hdr) μ]
  apply congrArg (fun P : MvPolynomial (Label n n (Fin s)) ℤ => P.coeff μ)
  apply Finset.sum_congr rfl
  intro a _
  exact finProdFinEquiv.symm.prod_comp (fun u : Site r => labelQuery d root (input Q.program Q.fits hdr a u))

end PrimedCounter.Chronology

end VPVNP
end Computability
end OAI
