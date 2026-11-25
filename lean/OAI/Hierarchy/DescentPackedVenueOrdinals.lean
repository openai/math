import OAI.Hierarchy.DescentHostDirectory

namespace OAI
/-! # The arithmetic address of every legal dyadic venue -/

namespace Hierarchy.DescentHostDirectory
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V]

theorem codes_valid {k d i : ℕ} (valid : (d,i)∈codes k) : d≤k ∧ i<2^d := by
  induction k with
  | zero =>
    obtain ⟨rfl,rfl⟩ : d=0 ∧ i=0 := by simpa [codes,Prod.ext_iff] using valid
    decide
  | succ k ih =>
    rcases Finset.mem_union.mp valid with last|added
    · exact ⟨(ih last).1.step,(ih last).2⟩
    · obtain ⟨p,bound,equal⟩ := Finset.mem_image.mp added
      cases equal
      exact ⟨le_rfl,Finset.mem_range.mp bound⟩

def nodeNumber (d j : ℕ) := 2^d-1+j
theorem node_range {d j : ℕ} (room : j<2^d) :
    2^d-1≤nodeNumber d j ∧ nodeNumber d j<2^(d+1)-1 := by
  unfold nodeNumber
  rw [pow_succ]
  have := Nat.two_pow_pos d
  omega

theorem node_inj {d e j i : ℕ} (hj : j<2^d) (hi : i<2^e)
    (same : nodeNumber d j=nodeNumber e i) : (d,j)=(e,i) := by
  have eqd : d=e := by
    rcases lt_trichotomy d e with lt|yes|lt
    · have bound : (2:ℕ)^(d+1)≤2^e := Nat.pow_le_pow_right (by decide) lt
      have := (node_range hj).2
      have := (node_range hi).1
      omega
    · exact yes
    · have bound : (2:ℕ)^(e+1)≤2^d := Nat.pow_le_pow_right (by decide) lt
      have := (node_range hi).2
      have := (node_range hj).1
      omega
  subst e
  exact Prod.ext rfl (Nat.add_left_cancel same)

def packedNumber (rank : V→ℕ) (k slots : ℕ) (u : Key V) :=
  (rank u.1*2^(k+1)+nodeNumber u.2.1.1 u.2.1.2)*slots+u.2.2

theorem packed_room {rank : V→ℕ} {k slots places : ℕ} (bounded : ∀v,rank v<places)
    (u : Key V) (ok : u∈keys k slots) : packedNumber rank k slots u<places*2^(k+1)*slots := by
  obtain ⟨_,hs⟩ := Finset.mem_product.mp ok
  obtain ⟨h,sl⟩ := Finset.mem_product.mp hs
  have valid : u.2.1.1≤k ∧ u.2.1.2<2^u.2.1.1 := codes_valid h
  have sn : u.2.2<slots := Finset.mem_range.mp sl
  have nr : nodeNumber u.2.1.1 u.2.1.2<2^(u.2.1.1+1)-1 := (node_range valid.2).2
  have lim : 2^(u.2.1.1+1)≤(2:ℕ)^(k+1) := Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ valid.1)
  have room := nr.trans_le ((Nat.sub_le _ _).trans lim)
  have first : rank u.1*2^(k+1)+nodeNumber u.2.1.1 u.2.1.2<places*2^(k+1) := by
    calc
      _ < rank u.1*2^(k+1)+2^(k+1) := Nat.add_lt_add_left room _
      _ = (rank u.1+1)*2^(k+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (bounded _)
  calc
    _ < (rank u.1*2^(k+1)+nodeNumber u.2.1.1 u.2.1.2)*slots+slots := Nat.add_lt_add_left sn _
    _ = (rank u.1*2^(k+1)+nodeNumber u.2.1.1 u.2.1.2+1)*slots := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ first

theorem packed_inj {rank : V→ℕ} {k slots : ℕ} (inj : Function.Injective rank)
    {u v : Key V} (hu : u∈keys k slots) (hv : v∈keys k slots)
    (eq : packedNumber rank k slots u=packedNumber rank k slots v) : u=v := by
  let side (x : Key V) := rank x.1*2^(k+1)+nodeNumber x.2.1.1 x.2.1.2
  have room (x : Key V) (h : x∈keys k slots) :
      x.2.1.2<2^x.2.1.1 ∧ nodeNumber x.2.1.1 x.2.1.2<2^(k+1) ∧ x.2.2<slots := by
    obtain ⟨c,i⟩ := Finset.mem_product.mp (Finset.mem_product.mp h).2
    have info : x.2.1.1≤k ∧ x.2.1.2<2^x.2.1.1 := codes_valid c
    obtain ⟨d,j⟩ := info
    have lim := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.succ_le_succ d)
    have nr := (node_range j).2
    exact ⟨j,((node_range j).2).trans_le ((Nat.sub_le _ _).trans lim),Finset.mem_range.mp i⟩
  have x := room u hu
  have y := room v hv
  have hpair {m a b c d : ℕ} (b0 : b<m) (d0 : d<m) (h : a*m+b=c*m+d) : a=c ∧ b=d := by
    have p : 0<m := by omega
    exact ⟨by simpa [Nat.mul_comm a m,Nat.mul_comm c m,Nat.mul_add_div p,Nat.div_eq_of_lt b0,Nat.div_eq_of_lt d0] using congrArg (·/m) h,
      by simpa [Nat.add_mod,Nat.mod_eq_of_lt b0,Nat.mod_eq_of_lt d0] using congrArg (·%m) h⟩
  have a0 := hpair x.2.2 y.2.2 eq
  have a1 := hpair x.2.1 y.2.1 a0.1
  exact Prod.ext (inj a1.1) (Prod.ext (node_inj x.1 y.1 a1.2) a0.2)

/-- Concrete finite code for any geometric subgroup whose actual address
passes the host bounds. Padding slots need no witness or enumeration. -/
def packedEmbedding {S : Type} {places k slots : ℕ} (rank : V↪Fin places)
    (coord : S↪Key V) (within : ∀x,coord x∈keys k slots) : S↪Fin (places*2^(k+1)*slots) where
  toFun x := ⟨packedNumber (fun v=>(rank v).val) k slots (coord x),
    packed_room (fun v=>(rank v).isLt) _ (within x)⟩
  inj' := by
    intro x y same
    apply coord.injective
    apply packed_inj (fun _ _ t=>rank.injective (Fin.ext t)) (within x) (within y)
    exact congrArg Fin.val same

@[simp] theorem packedEmbedding_val {S : Type} {places k slots : ℕ} (rank : V↪Fin places)
    (coord : S↪Key V) (within : ∀x,coord x∈keys k slots) (x : S) :
    (packedEmbedding rank coord within x).val=packedNumber (fun v=>(rank v).val) k slots (coord x) := rfl

end
end Hierarchy.DescentHostDirectory

end OAI
