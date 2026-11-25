import OAI.Hierarchy.DescentRosterOrder
import OAI.Hierarchy.DescentBadBundles
import OAI.Hierarchy.DescentBaseReservations
import OAI.Hierarchy.DescentOutputSlots
import OAI.Hierarchy.DescentResetIntervalAddress

namespace OAI
/-! # Block-independent physical row reservations for potential rotor contacts -/

namespace Hierarchy.DescentCanonicalPorts
open DescentColonies DescentBaseProfile DescentGL
open scoped BigOperators Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k m Y g Δ K : ℕ}
variable (near : V→Finset V) (b : V→ℕ) (low : ∀v,m≤b v) (top : ∀v,b v≤k)
variable (cap : V→V→ℝ) (S : ℝ) (positive : 0<S) (nonneg : ∀v w,0≤cap v w)
variable (total : ∀v a,(∑w∈near v,∑_j∈touching (b v) (b w) a,cap v w)≤2*S)
variable (smooth : ∀v w,w∈near v→b w≤b v+g) (degree : ∀v,(near v).card≤Δ)
variable (bounded : Δ*2^g≤K) (space : 4*K≤Y)

abbrev relative (v : V) := b v-m
abbrev Potential (v : V) (localID : ℕ) := PotentialContact near (relative (m:=m) b) v localID

include low in
omit [Fintype V] [DecidableEq V] in
theorem relative_counts (v w : V) : relative (m:=m) b w-relative (m:=m) b v=b w-b v := by
  unfold relative
  have := low v
  have := low w
  omega

include low positive nonneg total smooth degree bounded space in
omit [Fintype V] [DecidableEq V] in
theorem relative_room (v : V) (a : ℕ) :
    (∑z : Potential (m:=m) near b v a,rowCount Y S (cap v z.1.val))≤Y := by
  apply output_room _ positive (fun _=>nonneg _ _)
  · have h := total v 0
    simp only [Potential,PotentialContact,Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_coe]
    rw [Finset.sum_coe_sort (near v) (fun w=>(touching (relative (m:=m) b v) (relative (m:=m) b w) a).card • cap v w)]
    simpa only [Finset.sum_const,touching_card,relative_counts b low] using h
  · have sr (v w : V) (hw : w∈near v) : relative (m:=m) b w≤relative (m:=m) b v+g := by
      have := smooth v w hw
      have := low v
      unfold relative
      omega
    have h := touching_degree near (relative (m:=m) b) sr degree bounded v a
    rw [show Fintype.card (Potential (m:=m) near b v a)=
      ∑w∈near v,(touching (relative (m:=m) b v) (relative (m:=m) b w) a).card by
        simp only [Potential,PotentialContact,Fintype.card_sigma,Fintype.card_coe]
        exact Finset.sum_coe_sort (near v) (fun w=>(touching (relative (m:=m) b v) (relative (m:=m) b w) a).card)]
    exact (Nat.mul_le_mul_left 4 h).trans space

def span (v w : V) := rowCount Y S (cap v w)
abbrev Socket (v : V) (localID : ℕ) :=
  Σz : Potential (m:=m) near b v localID,Fin (span (Y:=Y) cap S v z.1.val)

/-- The local numbering sees every potential neighbor and relative interval,
in one common order, so the socket of a missing contact is still reserved. -/
def potentialNumber (vertex : V↪ℕ) (v : V) (a : ℕ) :
    Potential (m:=m) near b v a ↪ ℕ where
  toFun p := Nat.pair (vertex p.1.val) p.2.val
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eqn
    obtain ⟨host,id⟩:=Nat.pair_eq_pair.mp eqn
    obtain rfl : i=j := Subtype.ext (vertex.injective host)
    exact congrArg (Sigma.mk i) (Subtype.ext id)

def slots (vertex : V↪ℕ) (v : V) (a : ℕ) : Socket (m:=m) (Y:=Y) near b cap S v a ↪ Fin Y :=
  ((ProtocolRAMPortRanks.enumerate _ (potentialNumber near b vertex v a)
      (potentialNumber near b vertex v a).injective).toEmbedding).trans
    (Fin.castLEEmb (relative_room near b low cap S positive nonneg total smooth degree bounded space v a))

omit [Fintype V] [DecidableEq V] in
theorem slots_read (vertex : V↪ℕ) (v : V) (a : ℕ) (p : Socket (m:=m) (Y:=Y) near b cap S v a) :
    (slots near b low cap S positive nonneg total smooth degree bounded space vertex v a p).val =
      (∑z ∈ Finset.univ.filter (fun z : Potential (m:=m) near b v a =>
        potentialNumber (m:=m) near b vertex v a z < potentialNumber (m:=m) near b vertex v a p.1),
        rowCount Y S (cap v z.1.val))+p.2.val := rfl

theorem block_div {d : ℕ} (small : m≤d) (large : d≤k) (x : Block k) :
    group d x/2^(d-m)=group m x := by
  unfold group width
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add,show k-d+(d-m)=k-m by omega]

theorem block_mod {d : ℕ} (small : m≤d) (large : d≤k) (x : Block k) :
    group d x%2^(d-m)=group (d-m) (⟨x.val%2^(k-m),Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Block (k-m)) := by
  change x.val / 2^(k-d) % 2^(d-m) = (x.val % 2^(k-m)) / 2^(k-m-(d-m))
  have sizes : 2^(k-m)=2^(k-d)*2^(d-m) := by rw [←Nat.pow_add,show k-d+(d-m)=k-m by omega]
  rw [show k-m-(d-m)=k-d by omega,sizes,Nat.mod_mul_right_div_self]

def short (p : BaseId b) := (p.1,p.2.val%2^relative (m:=m) b p.1)
def coarse (p : BaseId b) := p.2.val/2^relative (m:=m) b p.1

omit [Fintype V] [DecidableEq V] in
theorem recover {p q : BaseId b} (hi : coarse (m:=m) b p=coarse (m:=m) b q)
    (lo : short (m:=m) b p=short (m:=m) b q) : p=q := by
  rcases p with ⟨v,a⟩
  rcases q with ⟨w,c⟩
  have place : v=w := congrArg Prod.fst lo
  subst w
  apply congrArg (Sigma.mk v)
  apply Fin.ext
  have lo' := congrArg Prod.snd lo
  let unit := 2^relative (m:=m) b v
  change a.val/unit=c.val/unit at hi
  change a.val%unit=c.val%unit at lo'
  calc a.val=a.val%unit+unit*(a.val/unit) := (Nat.mod_add_div ..).symm
       _=c.val := by rw [lo',hi,Nat.mod_add_div]

include low in
omit [Fintype V] [DecidableEq V] in
theorem base_div (L : Layout k) (v : V) (x : Block k) :
    coarse (m:=m) b (baseOf b top L (v,x))=group m (rearrange L x) := by
  simp only [coarse,relative,baseOf,layout_id]
  exact block_div (low v) (top v) _

include low in
omit [Fintype V] [DecidableEq V] in
theorem base_mod (L : Layout k) (v : V) (x : Block k) :
    (short (m:=m) b (baseOf b top L (v,x))).2 =
      group (relative (m:=m) b v) (⟨(rearrange L x).val%2^(k-m),Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Block (k-m)) := by
  simp only [short,relative,baseOf,layout_id]
  exact block_mod (low v) (top v) _

abbrev AllSockets := Σp : V×ℕ,Socket (m:=m) (Y:=Y) near b cap S p.1 p.2

def rowName (vertex : V↪ℕ) : AllSockets (m:=m) (Y:=Y) near b cap S ↪ (V×ℕ)×Fin Y where
  toFun p := (p.1,slots near b low cap S positive nonneg total smooth degree bounded space vertex p.1.1 p.1.2 p.2)
  inj' := by
    rintro ⟨a,x⟩ ⟨a',x'⟩ eq
    have aa : a=a' := congrArg Prod.fst eq
    subst a'
    apply congrArg (Sigma.mk a)
    exact (slots near b low cap S positive nonneg total smooth degree bounded space vertex a.1 a.2).injective
      (congrArg Prod.snd eq)

def wireName : AllSockets (m:=m) (Y:=Y) near b cap S ↪ (V×ℕ)×((V×ℕ)×ℕ) where
  toFun p := (p.1,((p.2.1.1.val,p.2.1.2.val),p.2.2.val))
  inj' := by
    rintro ⟨a,⟨⟨⟨w,hw⟩,⟨j,hj⟩⟩,p⟩⟩ ⟨a',⟨⟨⟨w',hw'⟩,⟨j',hj'⟩⟩,q⟩⟩ eq
    have aa : a=a' := congrArg Prod.fst eq
    subst a'
    have ww : w=w' := congrArg (fun z=>z.2.1.1) eq
    subst w'
    have jj : j=j' := congrArg (fun z=>z.2.1.2) eq
    subst j'
    have pq : p=q := Fin.ext (congrArg (fun z=>z.2.2) eq)
    subst q
    rfl

include low in
omit [Fintype V] [DecidableEq V] in
/-- If the original two addresses lie on the same old physical block, their
short labels represent touching intervals in the same newly exposed block. -/
theorem physical_touch (L : Layout k) (v w : V) (x : Block k) :
    (short (m:=m) b (baseOf b top L (w,x))).2∈touching (relative (m:=m) b v) (relative (m:=m) b w)
      (short (m:=m) b (baseOf b top L (v,x))).2 := by
  rw [base_mod b low top L w x,base_mod b low top L v x]
  exact actual_touch (Nat.sub_le_sub_right (top v) m) (Nat.sub_le_sub_right (top w) m)
    ⟨(rearrange L x).val % 2^(k-m),Nat.mod_lt _ (Nat.two_pow_pos _)⟩

end
end Hierarchy.DescentCanonicalPorts

end OAI
