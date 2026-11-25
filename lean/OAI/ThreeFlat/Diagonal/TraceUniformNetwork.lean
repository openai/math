import OAI.ThreeFlat.Diagonal.TraceUniformPackets
import OAI.ThreeFlat.Diagonal.TracePacketArray

namespace OAI
/-! # One trivalent network for every setting of the open program and input bits -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM TraceRows TraceRowPackets TraceCompose TraceProgram

variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

def copyBits (w p k d : ℕ) : (Fin (2^d) → Text w p k → Bool) ≃ (Fin (CopyCount w p k d) → Bool) where
  toFun x a := let b := finProdFinEquiv.symm a; x b.1 (finProdFinEquiv.symm b.2)
  invFun x v j := x (copyOrdinal v j)
  left_inv x := by funext v j; simp [copyOrdinal]
  right_inv x := by
    funext a
    obtain ⟨⟨v,i⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨j,rfl⟩ := finProdFinEquiv.surjective i
    simp only [copyOrdinal,Equiv.symm_apply_apply]

@[simp] theorem copyBits_at (x : Fin (2^d) → Text w p k → Bool) (v : Fin (2^d)) (j : Text w p k) :
    copyBits w p k d x (copyOrdinal v j)=x v j := by
  change x (finProdFinEquiv.symm (finProdFinEquiv (v,finProdFinEquiv j))).1
    (finProdFinEquiv.symm (finProdFinEquiv.symm (finProdFinEquiv (v,finProdFinEquiv j))).2)=_
  simp only [Equiv.symm_apply_apply]

noncomputable def allBits (w p r k f d : ℕ) :
    ((CpuBits w r f × SortBits d (w+1)) × (Fin (2^d) → Text w p k → Bool)) ≃
      (Fin (SharedCount w p r k d f) → Bool) :=
  ((TracePhysical.ordinalBits w r f d).prodCongr (copyBits w p k d)).trans (Fin.appendEquiv ..)

theorem addresses_at (hw : 2 ≤ w+1) (v : Fin (2^d)) (header : Fin S → Word w)
    (cpu : CpuBits w r f) (z : SortBits d (w+1)) (c : Fin (2^d) → Text w p k → Bool) (j : Port w p r k d) :
    (addresses hw S f v j).read (allBits w p r k f d ((cpu,z),c)) (TracePhysical.headerPins header) =
      valuation hw v header cpu z c j := by
  cases j with
  | inl a => simpa [addresses,allBits,Fin.appendEquiv,valuation] using TracePhysical.address_read hw v header cpu z a
  | inr q =>
    obtain ⟨b,j⟩ := q
    cases b with
    | false => simp [addresses,allBits,Fin.appendEquiv,valuation,BitSource.read,copyBits_at]
    | true => by_cases h : v.val+1<2^d <;>
        simp [addresses,allBits,Fin.appendEquiv,valuation,h,BitSource.read,copyBits_at]

noncomputable def network (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k d : ℕ) : BitNetwork F (S*w) :=
  TracePacketArray.network (fun v : Fin (2^d) => check (r:=r) (k:=k) hF hw hp hp0 base st hs hf v) coefficient
    (addresses (by omega) S f)

/-- The operand mapping reads only the physically routed row values.
Eliminate private gate outputs before summing the shared binary trace. -/
theorem network_eval (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (header : Fin S → Word w) :
    (network hF hw hp hp0 base st hs hf r k d).eval (TracePhysical.headerPins header) =
      ∑ cpu : CpuBits w r f, ∑ z : SortBits d (w+1), ∑ c : Fin (2^d) → Text w p k → Bool,
        ∏ v : Fin (2^d), ∏ j : Check F w p k, coefficient j ((check hF hw hp hp0 base st hs hf v j).2.eval
          (valuation (by omega) v header cpu z c)) := by
  classical
  rw [network,TracePacketArray.eval,← (allBits w p r k f d).sum_comp]
  simp only [Fintype.sum_prod_type,addresses_at]

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
