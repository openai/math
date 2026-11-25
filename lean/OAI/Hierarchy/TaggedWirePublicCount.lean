import OAI.Hierarchy.TaggedWirePublicPorts
import OAI.Hierarchy.TaggedWireIncidentDegree

namespace OAI
/-! # Size of the immutable signed-turn role directory -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets
open scoped BigOperators Classical
set_option synthInstance.maxSize 512
variable {h W k attempts : ℕ} (S : PurchaseSampler)

def paidSite : PaidPorts S h W k attempts→Site h (2^W) k :=
  Sum.elim (fun t=>Incident.choose (freeEnds t.1) t.2) physicalSite

def site : Public S h W k attempts→Site h (2^W) k := Sum.elim (paidSite S) (Sum.elim goodsSite catSite)

theorem goods_card (v : Site h (2^W) k) : Fintype.card (Incident.Fiber (goodsSite (h:=h) (W:=W) (k:=k)) v)≤1+2*k := by
  let key : Incident.Fiber (goodsSite (h:=h) (W:=W) (k:=k)) v→Unit⊕(Fin k×Bool) :=
    fun t=>Sum.elim (fun _=>.inl ()) (fun x=>.inr x.2) t.val
  have inj : Function.Injective key := by
    rintro ⟨(⟨p,s⟩|⟨u,l⟩),ht⟩ ⟨(⟨q,r⟩|⟨u',l'⟩),hz⟩ eq
    · have cols := congrArg Prod.fst (ht.trans hz.symm)
      apply Subtype.ext
      cases s <;> cases r <;> simp [goodsSite] at cols ⊢ <;> exact cols
    · exact (Sum.inl_ne_inr eq).elim
    · exact (Sum.inr_ne_inl eq).elim
    · have cols : u=u' := Sum.inl.inj (Sum.inr.inj (congrArg Prod.fst (ht.trans hz.symm)))
      exact Subtype.ext (congrArg Sum.inr (Prod.ext cols (Sum.inr.inj eq)))
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective key inj

theorem catalyst_card (v : Site h (2^W) k) :
    Fintype.card (Incident.Fiber (catSite (h:=h) (W:=W) (k:=k)) v)≤1 := by
  apply Fintype.card_le_one_iff.mpr
  rintro ⟨⟨⟨c,i⟩,b⟩,hh⟩ ⟨⟨⟨d,j⟩,s⟩,ht⟩
  have pair := hh.trans ht.symm
  have ax : (i,b)=(j,s) := Option.some.inj (congrArg Prod.snd pair)
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj ax
  obtain rfl : c=d := congrArg Prod.fst pair
  rfl

private theorem fiber_sum {I J V : Type} [Finite I] [Finite J] (l : I→V) (r : J→V) (x : V) :
    Nat.card (Incident.Fiber (Sum.elim l r) x) =
      Nat.card (Incident.Fiber l x) + Nat.card (Incident.Fiber r x) :=
  (Nat.card_congr (Incident.split l r x)).trans Nat.card_sum

/-- Public local pool size, including the virtual source legs before final routing. -/
theorem site_card (v : Site h (2^W) k) :
    Fintype.card (Incident.Fiber (site S (attempts:=attempts)) v) ≤ Incident.room k S.degree attempts + (1+2*k)+1 := by
  let f := fun t : Free S h (2^W) k × Bool=>Incident.choose (freeEnds t.1) t.2
  let pos := physicalSite (h:=h) (W:=W) (k:=k) (attempts:=attempts)
  have free := Incident.free_card S v
  have positive := Incident.positive_card (attempts:=attempts) v
  have good := goods_card v
  have cat := catalyst_card v
  simp only [←Nat.card_eq_fintype_card] at free positive good cat
  have bill := Nat.add_le_add (Nat.add_le_add free positive) (Nat.add_le_add good cat)
  have eqn : Nat.card (Incident.Fiber (site S (attempts:=attempts)) v) =
      (Nat.card (Incident.Fiber f v)+Nat.card (Incident.Fiber pos v))+
      (Nat.card (Incident.Fiber goodsSite v)+Nat.card (Incident.Fiber catSite v)) :=
    (fiber_sum (paidSite S) (Sum.elim goodsSite catSite) v).trans
      (congrArg₂ Nat.add (fiber_sum f pos v) (fiber_sum goodsSite catSite v))
  refine Nat.card_eq_fintype_card.symm.le.trans (eqn.le.trans (bill.trans ?_))
  unfold Incident.room
  omega

theorem public_count :
    Fintype.card (Public S h W k attempts) ≤ Fintype.card (Site h (2^W) k)*(Incident.room k S.degree attempts+(1+2*k)+1) := by
  let pool:=site (h:=h) (W:=W) (k:=k) (attempts:=attempts) S
  let : Fintype (Public S h W k attempts) := publicFintype S h W k attempts
  let : ∀v : Site h (2^W) k,Fintype {x : Public S h W k attempts // pool x=v} :=
    fun _=>inferInstance
  let bound := Incident.room k S.degree attempts+(1+2*k)+1
  calc
    _ = ∑v : Site h (2^W) k,Fintype.card {x : Public S h W k attempts // pool x=v} :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv pool)).symm.trans Fintype.card_sigma
    _ ≤ ∑ _v : Site h (2^W) k,bound :=
      Finset.sum_le_sum (fun v _=>site_card (h:=h) (W:=W) (k:=k) (attempts:=attempts) S v)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,bound]

theorem public_bit_count (cap : ℕ) :
    Fintype.card (Public S h W k attempts × Fin cap) ≤
      Fintype.card (Site h (2^W) k)*(Incident.room k S.degree attempts+(1+2*k)+1)*cap := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    Nat.mul_le_mul_right cap (public_count (h:=h) (W:=W) (k:=k) (attempts:=attempts) S)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles
end

end OAI
