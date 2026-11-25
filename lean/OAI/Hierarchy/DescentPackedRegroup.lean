import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # In-place regrouping of adjacent little-endian occurrence records -/

namespace Hierarchy.DescentSIMDLookup
open ThreeFlat.Routing
open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section

private theorem blocks_le (J M t : ℕ) (hm : 0<M) : chunks J M≤t ↔ J≤t*M := by
  change (J+M-1)/M≤t ↔ _
  rw [show (J+M-1)/M≤t ↔ (J+M-1)/M<t+1 from by omega,Nat.div_lt_iff_lt_mul hm,Nat.add_mul]
  simp only [Nat.one_mul]
  omega

/-- Packing r successive occurrences into one record leaves every physical
row boundary in place, including the last, partially occupied row. -/
theorem chunks_group (J M r : ℕ) (hm : 0<M) (hr : 0<r) : chunks (J*r) (M*r)=chunks J M := by
  have paid:=Nat.mul_pos hm hr
  apply Nat.le_antisymm
  · apply (blocks_le _ _ _ paid).mpr
    have h:=(blocks_le J M _ hm).mp (Nat.le_refl (chunks J M))
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right r h
  · apply (blocks_le _ _ _ hm).mpr
    have h:=(blocks_le (J*r) (M*r) _ paid).mp (Nat.le_refl (chunks (J*r) (M*r)))
    exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_assoc] using h) hr

/-- A nested local encoding is the very same natural number in the
register that previously stored the consecutive smaller records. -/
theorem encode_group (a M r : ℕ) (x : Fin (M*r)→Cell a) :
    (encode a (M*r) x).val =
      (encode (a*r) M (fun i=>encode a r (fun j=>x (finProdFinEquiv (i,j))))).val := by
  change (∑q : Fin (M*r),(x q).val*(2^a)^q.val)=
    ∑i : Fin M,(∑j : Fin r,(x (finProdFinEquiv (i,j))).val*(2^a)^j.val)*(2^(a*r))^i.val
  rw [←finProdFinEquiv.sum_comp (fun q : Fin (M*r)=>(x q).val*(2^a)^q.val),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change (x _).val*(2^a)^(j.val+r*i.val)=(x _).val*(2^a)^j.val*(2^(a*r))^i.val
  rw [pow_add,pow_mul,(pow_mul 2 a r)]
  ac_rfl

def groupedRows {H J r a : ℕ} (x : Fin H→Fin (J*r)→Cell a) (v : Fin H) (g : Fin J) : Cell (a*r) :=
  encode a r (fun i=>x v (finProdFinEquiv (g,i)))

theorem data_group {J M r H a : ℕ} (_hr : 0<r)
    (x : Fin H→Fin (J*r)→Cell a) (p : Row H J M) (p' : Row H (J*r) (M*r))
    (host : p.1=p'.1) (panel : p.2.val=p'.2.val) :
    (data x p').val=(data (groupedRows x) p).val := by
  unfold data
  rw [encode_group]
  apply congrArg (fun f : Fin M→Cell (a*r)=>(encode (a*r) M f).val)
  funext i
  by_cases alive : p.2.val*M+i.val<J
  · rw [dite_eq_left alive]
    apply congrArg (encode a r)
    funext j
    have coord : p'.2.val*(M*r)+(finProdFinEquiv (i,j)).val=(p.2.val*M+i.val)*r+j.val := by
      change p'.2.val*(M*r)+(j.val+r*i.val)=_
      rw [←panel]
      ring
    have good : p'.2.val*(M*r)+(finProdFinEquiv (i,j)).val<J*r := by
      rw [coord]
      calc
        _ < (p.2.val*M+i.val)*r+r := Nat.add_lt_add_left j.isLt _
        _ = (p.2.val*M+i.val+1)*r := by ring
        _ ≤ _ := Nat.mul_le_mul_right r alive
    rw [dite_eq_left good]
    have same : (⟨_,good⟩ : Fin (J*r))=finProdFinEquiv (⟨_,alive⟩,j) := by
      apply Fin.ext
      exact coord.trans (show (p.2.val*M+i.val)*r+j.val=j.val+r*(p.2.val*M+i.val) by ring)
    rw [same,host]
  · rw [dite_eq_right alive]
    have zero (j : Fin r) : ¬p'.2.val*(M*r)+(finProdFinEquiv (i,j)).val<J*r := by
      have h:=Nat.mul_le_mul_right r (Nat.le_of_not_gt alive)
      change ¬p'.2.val*(M*r)+(j.val+r*i.val)<J*r
      rw [←panel]
      nlinarith
    simp only [dite_eq_right (zero _)]
    apply Fin.ext
    change (∑j : Fin r,(0 : ℕ)*(2^a)^j.val)=0
    simp

/-- Reusing the original read address suffices for every reblocked host.
There are no instructions, copy buffers or trailing-pad writes. -/
theorem regroup_read {J M r H a w : ℕ} (hm : 0<M) (hr : 0<r) (start : ℕ)
    (mem : Memory w) (x : Fin H→Fin (J*r)→Cell a)
    (old : ∀p : Row H (J*r) (M*r),mem (start+(row H (J*r) (M*r) p).val)=((data x p).val:Word w))
    (p : Row H J M) :
    mem (start+(row H J M p).val)=((data (groupedRows x) p).val:Word w) := by
  let h:=chunks_group J M r hm hr
  let before : Row H (J*r) (M*r):=(p.1,Fin.cast h.symm p.2)
  have address : (row H (J*r) (M*r) before).val=(row H J M p).val := by
    change p.2.val+chunks (J*r) (M*r)*p.1.val=p.2.val+chunks J M*p.1.val
    rw [h]
  rw [←address,old,data_group hr x p before rfl rfl]

end
end Hierarchy.DescentSIMDLookup

end OAI
