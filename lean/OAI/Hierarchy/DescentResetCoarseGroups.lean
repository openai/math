import OAI.Hierarchy.DescentCommonResetLinks

namespace OAI
/-! # Each installed bank cable stays in the actual surviving coarse block -/

namespace Hierarchy.DescentChosenRouter
open DescentGL DescentColonies DescentContacts DescentCanonicalPorts DescentRelativeContacts
open scoped Classical
noncomputable section
variable {V I H A : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A]
    {k n : ℕ} (P : Placement V I H A k (2^n)) (m : ℕ) (code : H ↪ V×Endpoint (2^n))
def coarseName (m : ℕ) (z : V×Endpoint (2^n)) := z.2.1.2/2^(z.2.1.1-m)
def Placement.siteGroup : P.Site→ℕ
  | .inl g => DescentCanonicalPorts.coarse (m:=m) P.b g.val
  | .inr t => coarseName m (code t)

def Placement.CommonGroups := ∀c : P.Contact,P.siteGroup m code (P.owner false c)=P.siteGroup m code (P.owner true c)

theorem common_groups_of_records (low : ∀v,m≤P.b v)
    (same : ∀i,(P.old false i).2=(P.old true i).2)
    (origin : ∀a : A,∃p : {i // useRotor P.b P.depth P.L P.keys P.hub P.old i},
      ∀s,P.ends s a=base P.b P.depth P.L P.keys P.hub P.old p s)
    (fall : ∀s i,coarseName m (code (P.fall s (P.old s i)))=group m (rearrange P.L (P.old s i).2)) :
    P.CommonGroups m code := by
  rintro (⟨a,j⟩|p)
  · obtain ⟨i,hit⟩ := origin a
    change DescentCanonicalPorts.coarse (m:=m) P.b (P.ends false a).val=
      DescentCanonicalPorts.coarse (m:=m) P.b (P.ends true a).val
    rw [hit false,hit true]
    have read (s : Bool) : DescentCanonicalPorts.coarse (m:=m) P.b
        (base P.b P.depth P.L P.keys P.hub P.old i s).val=group m (rearrange P.L (P.old s i.val).2) :=
      base_div P.b low P.depth P.L _ _
    rw [read,read,same]
  · obtain ⟨i,_,hit⟩ := Finset.mem_image.mp p.property
    change coarseName m (code p.val.1)=coarseName m (code p.val.2)
    have pair : (P.fall false (P.old false i.val),P.fall true (P.old true i.val))=p.val := hit
    rw [←pair]
    change coarseName m (code (P.fall false (P.old false i.val)))=
      coarseName m (code (P.fall true (P.old true i.val)))
    rw [fall,fall,same]

namespace Dyadic
variable (D : Dyadic V I k)
theorem group_origins (a : D.Pairs) : ∃p : D.Paid,∀s,D.endAt s a=D.endpoint s p := by
  obtain ⟨j,_,hit⟩ := Finset.mem_image.mp a.property
  have same : D.edge j=a := Subtype.ext hit
  exact ⟨j,fun s=>same ▸ D.endAt_edge s j⟩
end Dyadic

end
end Hierarchy.DescentChosenRouter

end OAI
