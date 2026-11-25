import OAI.Hierarchy.DescentObservedReservations
import OAI.Hierarchy.DescentBaseReservations

namespace OAI
/-! # Paying only the real observed pairs out of each dyadic reservation -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentGL DescentColonies DescentBaseProfile
open private label_injective from OAI.Hierarchy.DescentBadVolume
open scoped Classical BigOperators
noncomputable section
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] {k : ℕ} (D : Dyadic V I k)
variable (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
variable (localEdge : ∀i : D.Paid,(D.old true i.val).1∈near (D.old false i.val).1)
variable (same : ∀i : D.Paid,(D.old true i.val).2=(D.old false i.val).2)

include sym localEdge in
private theorem old_near (s : Bool) (a : D.Pairs) : (D.endAt (!s) a).val.1∈near (D.endAt s a).val.1 := by
  rcases a with ⟨a,ok⟩
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ok
  cases s with
  | false => exact localEdge p
  | true => exact (sym _ _).mp (localEdge p)

include same in
private theorem old_touch (s : Bool) (a : D.Pairs) :
    (D.endAt (!s) a).val.2.val∈touching (D.b (D.endAt s a).val.1) (D.b (D.endAt (!s) a).val.1)
      (D.endAt s a).val.2.val := by
  rcases a with ⟨a,ok⟩
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ok
  cases s <;>
    dsimp [endAt,ordered,endpoint,DescentChosenRouter.base,baseOf] <;>
    rw [layout_id,layout_id,same p] <;>
    exact actual_touch (D.hk _) (D.hk _) (rearrange D.L (D.old false p.val).2)

/-- The reservation ID at a fixed base remembers the opposite base's
physical position and dyadic block number. Hence it is injective. -/
def observedAt (s : Bool) (g : D.G) : D.Incident s g ↪ PotentialContact near D.b g.val.1 g.val.2.val where
  toFun a := ⟨⟨(D.endAt (!s) a.val).val.1,by simpa [a.property] using D.old_near near sym localEdge s a.val⟩,
    ⟨(D.endAt (!s) a.val).val.2.val,by
      have host := congrArg (fun e : D.G=>e.val.1) a.property
      have block := congrArg (fun e : D.G=>e.val.2.val) a.property
      change (D.endAt s a.val).val.1=g.val.1 at host
      change (D.endAt s a.val).val.2.val=g.val.2.val at block
      simpa only [host,block] using D.old_touch same s a.val⟩⟩
  inj' a b eq := by
    have first := congrArg (fun p : PotentialContact near D.b g.val.1 g.val.2.val=>p.1.val) eq
    have second := congrArg (fun p : PotentialContact near D.b g.val.1 g.val.2.val=>p.2.val) eq
    have other : D.endAt (!s) a.val=D.endAt (!s) b.val := Subtype.ext
      (label_injective D.b (Prod.ext first second))
    have here := a.property.trans b.property.symm
    apply Subtype.ext
    apply Subtype.ext
    cases s with
    | false => exact Prod.ext here other
    | true => exact Prod.ext other here

variable {scale : ℝ} {K : ℕ} (mean : V→V→ℝ)
def pairCap (a : D.Pairs) := pairCapacity k (D.b a.val.1.val.1) (D.b a.val.2.val.1)
  (mean a.val.1.val.1 a.val.2.val.1) scale K

/-- Source and destination use the same amount on a common contact, even
if the two base depths differ. -/
theorem capacity_read (mean_sym : ∀v w,mean v w=mean w v) (s : Bool) (g : D.G) (a : D.Incident s g) :
    D.pairCap (scale:=scale) (K:=K) mean a.val =
      contactCapacity near D.b g.val.1 g.val.2.val k K mean scale
        (D.observedAt near sym localEdge same s g a) := by
  rcases a with ⟨a,rfl⟩
  cases s with
  | false => rfl
  | true =>
    let v := a.val.1.val.1
    let w := a.val.2.val.1
    change pairCapacity k (D.b v) (D.b w) (mean v w) scale K =
      pairCapacity k (D.b w) (D.b v) (mean w v) scale K
    unfold pairCapacity
    rw [max_comm (D.b v) (D.b w),mean_sym v w]

include sym localEdge same in
theorem observed_degree {g Δ K Y : ℕ}
    (smooth : ∀v w,w∈near v→D.b w≤D.b v+g) (degree : ∀v,(near v).card≤Δ)
    (quota : Δ*2^g≤K) (slots : 4*K≤Y) (s : Bool) (p : D.G) :
    4*Fintype.card (D.Incident s p)≤Y := by
  have sub := Fintype.card_le_of_embedding (D.observedAt near sym localEdge same s p)
  have cap : Fintype.card (PotentialContact near D.b p.val.1 p.val.2.val)≤K := by
    simp only [PotentialContact,Fintype.card_sigma,Fintype.card_coe]
    rw [Finset.sum_coe_sort (near p.val.1)
      (fun w=>(touching (D.b p.val.1) (D.b w) p.val.2.val).card)]
    exact touching_degree near D.b smooth degree quota p.val.1 p.val.2.val
  exact (Nat.mul_le_mul_left 4 (sub.trans cap)).trans slots

include sym localEdge same in
theorem observed_budget (mean_sym : ∀v w,mean v w=mean w v)
    (pos : ∀v w,0≤ mean v w) (hs : 0≤ scale)
    (budget : ∀v id,(∑w∈near v,∑_j∈touching (D.b v) (D.b w) id,
      pairCapacity k (D.b v) (D.b w) (mean v w) scale K)≤2*scale)
    (s : Bool) (g : D.G) :
    (∑a : D.Incident s g,D.pairCap (scale:=scale) (K:=K) mean a.val)≤2*scale := by
  let inj := D.observedAt near sym localEdge same s g
  let price := contactCapacity near D.b g.val.1 g.val.2.val k K mean scale
  have nonneg (z) : 0≤price z := by
    exact add_nonneg (mul_nonneg (by positivity) (pos _ _)) (div_nonneg hs (Nat.cast_nonneg _))
  have total : (∑z,price z)≤2*scale := by
    rw [Fintype.sum_sigma]
    let cost (w : V) := pairCapacity k (D.b g.val.1) (D.b w) (mean g.val.1 w) scale K
    change (∑w : near g.val.1,∑_ : touching (D.b g.val.1) (D.b w.val) g.val.2.val,cost w.val)≤_
    simp_rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe]
    rw [Finset.sum_coe_sort (near g.val.1)
      (fun w=>(touching (D.b g.val.1) (D.b w) g.val.2.val).card • cost w)]
    simpa only [Finset.sum_const,cost] using budget g.val.1 g.val.2.val
  have paid : (∑a : D.Incident s g,price (inj a))≤∑z,price z := by
    rw [←Finset.sum_map Finset.univ inj price]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _=>nonneg z)
  simp_rw [D.capacity_read near sym localEdge same mean mean_sym]
  exact paid.trans total

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
