import OAI.Hierarchy.DescentSignedStageRates
import OAI.Hierarchy.DescentSelectedDonorRateNumbers

namespace OAI
/-! # The two age exponents for the actual signed return procedure -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree DescentDatedAddressBook
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- The material source reads cost at most 88 operations. The physical peer query
also scans the next degree, which ranges over the fixed round schedule. -/
def signedSnippetRate (t : ℕ) := ∑j : Fin (maximumDegree t+1),max (ordinaryDegree j.val) 88

private theorem snippet_le_total {n : ℕ} (cost : Fin n → ℕ) (j : Fin n) :
    cost j ≤ ∑ i, cost i :=
  Finset.single_le_sum (s := Finset.univ) (f := cost) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

private theorem snippet_paid (J t D : ℕ) (room : D≤ maximumDegree t) :
    max (ordinaryDegree D) 88 ≤ scale J (signedSnippetRate t) := by
  let j : Fin (maximumDegree t+1):=⟨D,Nat.lt_succ_of_le room⟩
  have col : max (ordinaryDegree D) 88 ≤ signedSnippetRate t :=
    snippet_le_total (fun i : Fin (maximumDegree t+1) => max (ordinaryDegree i.val) 88) j
  exact col.trans (Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_mul_of_pos_right _ (Nat.succ_pos J))))

structure SignedRates (G : PoweredGadget F) (t f g reset : ℕ) where
  amount : ℕ
  controls : ℕ
  bounds : ∀ J D cap H H' groups payload : ℕ,D≤ maximumDegree t →
    cap≤2^(8+capRate G t g*((t+1)*J)) →
    let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
    let q : SignedStage:=⟨k,D,cap,ordinaryDegree D,2^gainExponent 20 D*G.b*cap,H,H',groups,G.b,G.C,G.k⟩
    q.unit ≤ scale J amount ∧ (q.format payload).feedFactor (max q.newDegree 88) ≤ scale J controls

def signedRates (G : PoweredGadget F) (t f g reset : ℕ) : SignedRates G t f g reset := by
  have rates:=SignedStage.uniform t (hostRate t reset) (capRate G t g) (cutRate t f g) (maximumDegree t)
    G.b G.C G.k (signedSnippetRate t)
  refine ⟨rates.choose,rates.choose_spec.choose,?_⟩
  intro J D cap H H' groups payload hD hc
  exact rates.choose_spec.choose_spec J D cap (max (ordinaryDegree D) 88) H H' groups payload hD hc
    (snippet_paid J t D hD)

end
end Hierarchy.DescentSixParty.Chronology

end OAI
