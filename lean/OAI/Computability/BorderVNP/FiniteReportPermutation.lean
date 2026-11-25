import OAI.Computability.BorderVNP.FiniteScalarRoundCell
import OAI.Computability.BorderVNP.DiagonalTallyReportModel

/-! # Guessing bit-major field claims with the native count-bit loop

The native report loop guesses a flat word of fresh bits. The ordinary
gadget-major row decoder and the finite-field bit-major row decoder index
that same word in different rectangular shapes. Their bijection is exact
for every field cardinality and every subtotal width, including width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteScalarRounds

open DiagonalTallyCellReports

/-- Rectangular index change that preserves the actual flat ordinal. -/
def reorder (m n : ℕ) : (Fin m × Fin n) ≃ (Fin n × Fin m) :=
  finProdFinEquiv.trans ((finCongr (Nat.mul_comm m n)).trans finProdFinEquiv.symm)

/-- Interpret a bit-major count table in the indices expected by the native report
guess loop. The map permutes coordinates, preserving every possible choice word. -/
def nativeCounts (m n : ℕ) : (Fin m → Fin n → Bool) ≃ (Fin m → Fin n → Bool) where
  toFun f := fun i j => let a := reorder m n (i,j); f a.2 a.1
  invFun f := fun i j => let a := (reorder m n).symm (j,i); f a.1 a.2
  left_inv f := by funext i j; simp
  right_inv f := by funext i j; simp

private theorem ordinal {m n : ℕ} (i : Fin m) (j : Fin n) :
    (finProdFinEquiv (i,j)).val = i.val*n+j.val := by change _+_*_=_; ring

/-- Chronological row-major reading of the permuted counts gives exactly the
bit-major physical field payload accepted by the scalar tape table. -/
theorem nativeCounts_flatten (F : Type*) [Fintype F] {d : ℕ} (c : Index F → Fin d → Bool) :
    (List.ofFn fun v : Index F => List.ofFn ((nativeCounts (Fintype.card F) d c) v)).flatten = stream F c := by
  let q := Fintype.card F
  let read (k : Fin (q*d)) := let z : Fin d × Fin q := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm q d) k); c z.2 z.1
  have first : (List.ofFn fun v : Fin q => List.ofFn ((nativeCounts q d c) v)).flatten = List.ofFn read := by
    rw [List.ofFn_mul]
    congr 2
    funext v
    apply congrArg List.ofFn
    funext j
    change read (finProdFinEquiv (v,j)) = read ⟨v.val*d+j.val,_⟩
    exact congrArg read (Fin.ext (ordinal v j))
  rw [first,List.ofFn_mul',stream]
  congr 2
  funext j
  apply congrArg List.ofFn
  funext v
  have fits : q*j.val+v.val < q*d := by
    simpa only [ordinal,Nat.mul_comm j.val q,Nat.mul_comm d q] using (finProdFinEquiv (j,v)).isLt
  have same : Fin.cast (Nat.mul_comm q d) (⟨q*j.val+v.val,fits⟩ : Fin (q*d)) = finProdFinEquiv (j,v) := by
    apply Fin.ext
    change q*j.val+v.val = _
    rw [ordinal,Nat.mul_comm q j.val]
  simp only [read,same,Equiv.symm_apply_apply]

/-- In the finite-field branch, all the native count guesses give the one canonical
bit-major exterior suffix. Empty weighted-use fields contribute no extra bits. -/
theorem report_bits {F : Type*} [Fintype F] (l : ReportLayout) (r : ReportCell l) (g : l.gadgets=Fintype.card F)
    (c : Index F → Fin l.countWidth → Bool)
    (counts : ∀ v j, r.counts v j=nativeCounts (Fintype.card F) l.countWidth c (Fin.cast g v) j)
    (use : ∀ b ∈ r.bundles, b.useCount=0) : r.bits = stream F c := by
  have empty : (r.bundles.flatMap (fun b => List.ofFn b.uses)) = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [List.length_flatMap]
    apply List.sum_eq_zero_iff.mpr
    intro k hk
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hk
    rw [List.length_ofFn]; exact use _ hb
  rw [ReportCell.bits,empty,List.append_nil,←nativeCounts_flatten F c]
  apply congrArg List.flatten
  simpa only [List.ofFn_congr g,Fin.cast_cast,Fin.cast_refl,id] using congrArg List.ofFn (show
    (fun v : Fin l.gadgets => List.ofFn (r.counts v)) =
      (fun v : Fin l.gadgets => List.ofFn ((nativeCounts (Fintype.card F) l.countWidth c) (Fin.cast g v))) from
    funext fun v => congrArg List.ofFn (funext (counts v)))

end FiniteScalarRounds

end BorderVNP
end Computability
end OAI
