import OAI.ThreeFlat.Diagonal.HistogramPartyAdmission
import OAI.ThreeFlat.Diagonal.MotifSelectorChecks
import OAI.ThreeFlat.Diagonal.MotifBinaryPacking

namespace OAI
/-! # The histogram admission gate on the actual selector half-port bits -/

namespace ThreeFlat.Diagonal.MotifOuterTerms

noncomputable section

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector TraceCircuit MotifBinaryPacking
open scoped Classical BigOperators

variable {F H J S : Type*} [CommRing F] [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype J] [Nonempty J] [Fintype S] {r k e h : ℕ}

/-- The library gives one fixed number to each selector symbol. -/
def numberHistogram (id : H ≃ Fin h) (v : Histogram H r) : Histogram (Fin h) r :=
  ⟨fun j => v.val (id.symm j), (id.symm.sum_comp (fun a => (v.val a).val)).trans v.property⟩

omit [Nonempty H] in
private theorem number_histogram (id : H ≃ Fin h) (f : Fin r → H) :
    numberHistogram id (histogram f) = histogram (fun i => id (f i)) := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  change (∑ i, if f i = id.symm j then 1 else 0) = ∑ i, if id (f i) = j then 1 else 0
  simp only [Equiv.eq_symm_apply]

omit [DecidableEq H] [Nonempty H] in
private theorem number_inj (id : H ≃ Fin h) : Function.Injective (numberHistogram (r:=r) id) := by
  intro a b h
  apply Subtype.ext
  funext i
  simpa [numberHistogram] using congrFun (congrArg Subtype.val h) (id i)

variable (G : Supply J S) (j : J) (portsAt : Fin e ≃ (ports G).Port j)
    (id : H ≃ Fin h) (code : H ↪ Fin (2^k))

def selectorBits (raw : (ports G).Port j → Fin r → Fin (2^k)) (i : Fin r) : Fin (e*k) → Bool :=
  blocks e k (fun p => (word k).symm (raw (portsAt p) i))

private def ownerWord (z : Fin (e*k) → Bool) (p : (ports G).Port j) : Fin (2^k) :=
  word k (fun bit => z (finProdFinEquiv (portsAt.symm p,bit)))

omit [Fintype J] [Nonempty J] [Fintype S] in
private theorem ownerWord_at (raw : (ports G).Port j → Fin r → Fin (2^k)) (i : Fin r) (p : (ports G).Port j) :
    ownerWord G j portsAt (selectorBits G j portsAt raw i) p = raw p i := by
  simp [ownerWord,selectorBits]

def headerGood (z : Fin (e*k) → Bool) : Prop :=
  let vals := ownerWord G j portsAt z
  (∀ p, vals p = vals (anchorPort G j)) ∧ ∃ t, code t = vals (anchorPort G j)

noncomputable def headerLetter (z : Fin (e*k) → Bool) :=
  id (Function.invFun code (ownerWord G j portsAt z (anchorPort G j)))

noncomputable def admissionNetwork (C : BitNetwork F (r+(r+r))) (v : Histogram H r) : BitNetwork F (r*(e*k)) :=
  MotifSelectorChecks.network (headerGood G j portsAt code) (headerLetter G j portsAt id code) C (numberHistogram id v)

private theorem indicator_congr (P Q : Prop) [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1:F) else 0) = if Q then 1 else 0 := by
  by_cases hp : P
  · simp only [ite_eq_left hp,ite_eq_left (h.mp hp)]
  · simp only [ite_eq_right hp,ite_eq_right (fun hq => hp (h.mpr hq))]

omit [Fintype J] [Nonempty J] [Fintype S] in
/-- The network's pins are the selector headers at every incident port in
copy-major order. Every copy-local agreement, code-membership and histogram
check is included, including the invalid-code branch. -/
theorem admission_eval (C : BitNetwork F (r+(r+r))) (v : Histogram H r)
    (hC : ∀ M X Y, C.eval (Fin.append M (Fin.append X Y)) = if Y = Routing.StableCompaction.compact M X then 1 else 0)
    (raw : (ports G).Port j → Fin r → Fin (2^k)) :
    (admissionNetwork G j portsAt id code C v).eval (blocks r _ (selectorBits G j portsAt raw)) =
      if (∀ i, copyGood G j code raw i) ∧ histogram (readLetter G j code raw) = v then 1 else 0 := by
  rw [admissionNetwork,MotifSelectorChecks.eval _ _ _ _ hC]
  apply indicator_congr
  simp only [headerGood,headerLetter,ownerWord_at,copyGood]
  apply and_congr_right
  intro _
  let s := readLetter G j code raw
  have numbered := number_histogram id s
  exact ⟨fun h => number_inj id (numbered.trans h.symm),
    fun h => (congrArg (numberHistogram id) h.symm).trans numbered⟩

end

end ThreeFlat.Diagonal.MotifOuterTerms

end OAI
