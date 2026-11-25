import OAI.Hierarchy.ProbeStagePhysicalDirectory

namespace OAI
/-! # Distinct mutable cells for blocks, colors, rows, and chunks -/

namespace Hierarchy.ProbeStage.Native
noncomputable section

theorem blockNumber_injective {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (π : Equiv.Perm (Fin (2^h))) :
    Function.Injective (blockNumber hd j π) := by
  intro x y eq
  have val := congrArg Fin.val eq
  have same := finProdFinEquiv.injective (Fin.ext val :
    finProdFinEquiv ((history h d π j.val).encode x.1,x.2)=
    finProdFinEquiv ((history h d π j.val).encode y.1,y.2))
  obtain ⟨g,off⟩ := Prod.mk.inj same
  exact Prod.ext ((history h d π j.val).encode.injective g) off

private theorem digits {n a b : ℕ} (x y : Fin n) (eq : a*n+x.val=b*n+y.val) :
    a=b ∧ x=y := by
  have pos : 0<n := Nat.zero_lt_of_lt x.isLt
  have div := congrArg (fun z => z/n) eq
  rw [Nat.mul_comm a n,Nat.mul_comm b n] at div
  simp only [Nat.mul_add_div pos,Nat.div_eq_of_lt x.isLt,Nat.div_eq_of_lt y.isLt,Nat.add_zero] at div
  subst b
  exact ⟨rfl,Fin.ext (Nat.add_left_cancel eq)⟩

theorem countTag_eq_iff {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (l : Bool)
    {b e : Fin (groupBlocks h d j.val)} {c z : Fin (radix h d)} :
    countTag hd j l b c=countTag hd j l e z ↔ b=e ∧ c=z := by
  constructor
  · intro eq
    have offset := congrArg Fin.val (Cell.area.inj eq).2
    obtain ⟨be,cz⟩ := digits c z offset
    exact ⟨Fin.ext be,cz⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem maskTag_eq_iff {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (l : Bool)
    {b e : Fin (groupBlocks h d j.val)} {r t : MaskIndex (radix h d)} {k u : Fin (fieldChunks h)} :
    maskTag hd j l b r k=maskTag hd j l e t u ↔ b=e ∧ r=t ∧ k=u := by
  constructor
  · intro eq
    have off := congrArg Fin.val (Cell.area.inj eq).2
    let B := radix h d
    let C := fieldChunks h
    change b.val*(B^4*C)+rowCode r*C+k.val=e.val*(B^4*C)+rowCode t*C+u.val at off
    have pack (a c s : ℕ) : (a*B^4+c)*C+s=a*(B^4*C)+c*C+s := by ring
    have sorted : (b.val*B^4+rowCode r)*C+k.val=(e.val*B^4+rowCode t)*C+u.val :=
      (pack ..).trans (off.trans (pack ..).symm)
    obtain ⟨w,ku⟩ := digits k u sorted
    let rr : Fin (B^4) := ⟨rowCode r,rowCode_lt r⟩
    let tt : Fin (B^4) := ⟨rowCode t,rowCode_lt t⟩
    obtain ⟨be,id⟩ := digits rr tt w
    have code : rowCode r=rowCode t := congrArg (fun i : Fin (B^4) => i.val) id
    exact ⟨Fin.ext be,finProdFinEquiv.injective (Fin.ext code),ku⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

theorem countTag_ne_of_block_ne {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (l : Bool)
    {b e : Fin (groupBlocks h d j.val)} (different : b≠e) (c z : Fin (radix h d)) :
    countTag hd j l b c≠countTag hd j l e z := fun eq => different ((countTag_eq_iff hd j l).mp eq).1

theorem maskTag_ne_of_block_ne {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (l : Bool)
    {b e : Fin (groupBlocks h d j.val)} (different : b≠e) (r t : MaskIndex (radix h d))
    (k u : Fin (fieldChunks h)) : maskTag hd j l b r k≠maskTag hd j l e t u :=
  fun eq => different ((maskTag_eq_iff hd j l).mp eq).1

end
end Hierarchy.ProbeStage.Native

end OAI
