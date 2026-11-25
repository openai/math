import OAI.Hierarchy.TaggedWirePublicCount
import OAI.Hierarchy.TaggedWireIncidentDegree
import OAI.Hierarchy.TaggedWireRowGraph
import OAI.Hierarchy.TaggedWireGoodsDistinct

namespace OAI
/-! # The fixed sockets of every paid, live commodity, and catalyst half-edge -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical BigOperators

variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
  (marked : Marks h W k attempts) (unique : Exclusive marked)

/-- Transfer from the original core/bought row partition to precisely the
public private or stage socket banks; public port positions do not depend on tags. -/
def labelled : Catalogue S π depth marked ≃ Free S h (2^W) k ⊕ ReportSockets.Row S π depth marked where
  toFun
    | .inl (.inl f)=>.inl f
    | .inl (.inr ((p,t),l))=>.inr (.inl ((t,p),l))
    | .inr j=>.inr (.inr j)
  invFun
    | .inl f=>.inl (.inl f)
    | .inr (.inl ((t,p),l))=>.inl (.inr ((p,t),l))
    | .inr (.inr j)=>.inr j
  left_inv := by rintro ((f|⟨⟨p,t⟩,l⟩)|j) <;> rfl
  right_inv := by rintro (f|(⟨⟨t,p⟩,l⟩|j)) <;> rfl

def paid : Catalogue S π depth marked × Bool ↪ PaidPorts S h W k attempts :=
  (((labelled S π depth marked).prodCongr (Equiv.refl Bool)).trans (Equiv.sumProdDistrib _ _ _)).toEmbedding.trans
    ((Function.Embedding.refl _).sumMap (locate S π depth marked unique))

theorem paid_site (e : Catalogue S π depth marked) (s : Bool) :
    paidSite S (paid S π depth marked unique (e,s))=Incident.choose (actualEnds S π depth marked e) s := by
  rcases e with (f|⟨⟨p,t⟩,l⟩)|⟨a,p⟩
  · rfl
  · cases s <;> rfl
  · change ((.inr (.inl (allStripColumns S π depth (marked a) (unique a) (p,probeEnds depth s))),none) : Site h (2^W) k)=_
    rw [allStripColumns_single]
    cases s <;> rfl

def goods : Commodity (Fin (2^h)) (Stages h (2^W)) k × Bool ↪ GoodPorts h W k where
  toFun
    | (.inl p,false)=>.inl (p,false)
    | (.inl p,true)=>.inl (π p,true)
    | (.inr ((p,t),l),s)=>.inr (⟨t,occupiedStagePort π t (p,s)⟩,l)
  inj' := by
    rintro ⟨(p|⟨⟨p,t⟩,l⟩),s⟩ ⟨(p'|⟨⟨p',t'⟩,l'⟩),s'⟩ eq
    · cases s <;> cases s'
      · exact Prod.ext (congrArg Sum.inl (congrArg Prod.fst (Sum.inl.inj eq))) rfl
      · exact Bool.noConfusion (show false=true from congrArg Prod.snd (Sum.inl.inj eq))
      · exact Bool.noConfusion (show true=false from congrArg Prod.snd (Sum.inl.inj eq))
      · exact Prod.ext (congrArg Sum.inl (π.injective (congrArg Prod.fst (Sum.inl.inj eq)))) rfl
    · cases s <;> contradiction
    · cases s' <;> contradiction
    · have both := Sum.inr.inj eq
      obtain ⟨rfl,ports⟩ := Sigma.mk.inj_iff.mp (congrArg Prod.fst both)
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj ((occupiedStagePort π t).injective (eq_of_heq ports))
      obtain rfl : l=l' := congrArg Prod.snd both
      rfl

theorem goods_site (i : Commodity (Fin (2^h)) (Stages h (2^W)) k) (s : Bool) :
    goodsSite (goods π (i,s))=Incident.choose (commodityEnds π i) s := by
  rcases i with p|⟨⟨p,t⟩,l⟩ <;> cases s <;> rfl

abbrev Source := Catalogue S π depth marked ⊕
  (Commodity (Fin (2^h)) (Stages h (2^W)) k ⊕ (Columns h (2^W)×Fin k))

def physicalEnds : Source S π depth marked→Site h (2^W) k × Site h (2^W) k :=
  Sum.elim (actualEnds S π depth marked) (Sum.elim (commodityEnds π) (fun c=>((c.1,some (c.2,false)),(c.1,some (c.2,true)))))

def physical : Source S π depth marked × Bool ↪ Public S h W k attempts :=
  (Equiv.sumProdDistrib _ _ _).toEmbedding.trans ((paid S π depth marked unique).sumMap
    ((Equiv.sumProdDistrib _ _ _).toEmbedding.trans ((goods π).sumMap (Function.Embedding.refl _))))

theorem physical_site (e : Source S π depth marked) (s : Bool) :
    site S (physical S π depth marked unique (e,s))=Incident.choose (physicalEnds S π depth marked e) s := by
  rcases e with e|e|c
  · exact paid_site S π depth marked unique e s
  · exact goods_site π e s
  · cases s <;> rfl

theorem physical_distinct (e : Source S π depth marked) :
    (physicalEnds S π depth marked e).1≠(physicalEnds S π depth marked e).2 := by
  rcases e with e|e|c
  · exact actual_distinct S π depth marked e
  · exact goods_different π e
  · simp [physicalEnds]

def sorted (e : Source S π depth marked) :=
  orderedChord (name (physicalEnds S π depth marked e).1) (name (physicalEnds S π depth marked e).2)
    (name.injective.ne (physical_distinct S π depth marked e))

def swap (e : Source S π depth marked) (b : Bool) :=
  if name (physicalEnds S π depth marked e).1<name (physicalEnds S π depth marked e).2 then b else !b

def orient : Source S π depth marked × Bool ≃ Source S π depth marked × Bool where
  toFun x := (x.1,swap S π depth marked x.1 x.2)
  invFun x := (x.1,swap S π depth marked x.1 x.2)
  left_inv := by rintro ⟨e,b⟩;by_cases hi:name (physicalEnds S π depth marked e).1<name (physicalEnds S π depth marked e).2 <;> simp [swap,hi]
  right_inv := by rintro ⟨e,b⟩;by_cases hi:name (physicalEnds S π depth marked e).1<name (physicalEnds S π depth marked e).2 <;> simp [swap,hi]

def named {N : ℕ} (rows : Fin N≃Source S π depth marked) : Fin N×Bool ↪ Public S h W k attempts :=
  ((rows.prodCongr (Equiv.refl Bool)).trans (orient S π depth marked)).toEmbedding.trans (physical S π depth marked unique)

theorem named_site {N : ℕ} (rows : Fin N≃Source S π depth marked) (j : Fin N) (b : Bool) :
    name (site S (named S π depth marked unique rows (j,b)))=
      (portGraph _).vertex (sorted S π depth marked (rows j)) b := by
  change name (site S (physical S π depth marked unique (rows j,swap S π depth marked (rows j) b)))=_
  rw [physical_site]
  by_cases hi:name (physicalEnds S π depth marked (rows j)).1<name (physicalEnds S π depth marked (rows j)).2 <;>
    cases b <;> simp [sorted,orderedChord,Incident.choose,swap,hi,portGraph,PortGraph.vertex]

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
