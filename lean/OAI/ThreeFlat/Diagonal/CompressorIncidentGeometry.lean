import OAI.ThreeFlat.Diagonal.CompressorIncidentVisits
import OAI.ThreeFlat.Diagonal.CompressorIncidentMask
import OAI.ThreeFlat.Diagonal.CompressorOpsMap
import OAI.ThreeFlat.Diagonal.CompressorCandidateCode
import OAI.ThreeFlat.Diagonal.CompressorDemandROM

namespace OAI
/-! # Each native incident probe follows its actual old arc and six party sites -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast Classical

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w t l : ℕ}
variable {S : Graph.Stage} (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l)
variable (ptr : F) (data : Param → Word w) (mem : Memory w) (vs : Fin 1 → Word w)

local notation "V" => Formula.value data mem vs
local notation "g" => oldColumns (Demand.formulaOps 1) ptr

abbrev probe {S : Graph.Stage} (ptr : F) (v : Placement.Site F) (a : Local.Slots S.degree S.colors) :=
  fromChild (Demand.formulaOps 1) (oldColumns (Demand.formulaOps 1) ptr) S.degree a.1 a.2.1.1 a.2.2.1 v
    (.lit a.2.1.2.1.val) (.lit (tagOrdinal S.colors a.2.1.2.2).val) (.lit a.2.2.2.val)

abbrev probeRoles {S : Graph.Stage} (ptr : F) (lay : Bool) (v : Placement.Site F) (a : Local.Slots S.degree S.colors) :=
  roleSites (Demand.formulaOps 1) (oldColumns (Demand.formulaOps 1) ptr) S.degree lay (probe (S:=S) ptr v a)

abbrev present {S : Graph.Stage} (ptr : F) (lay : Bool) (v : Placement.Site F) (a : Local.Slots S.degree S.colors)
    (j : Fin 6) : F := eqSite (Graph.siteAt (probeRoles (S:=S) ptr lay v a) (ShrinkMotif.role lay j)) v

def partyBits (lay : Bool) (v : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (z : P.Motif)
    (j : Fin 6) := decide (partySite P lay z j = v)
def edgeBits (lay : Bool) (v : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (z : P.Motif)
    (j : Fin 8) := partyBits P lay v z (ShrinkMotif.supplySrc j) && partyBits P lay v z (ShrinkMotif.supplyDst j)

private theorem valOps : OpMap (Demand.formulaOps 1) (words mem) V where
  lit _ := rfl
  bin _ _ _ := rfl
  load _ := rfl
  choose _ _ _ _ := by simp [Demand.formulaOps,words,Formula.value,RAM.DescriptorExpr.Comparison.test]

omit [Fintype B] [Fintype H] in
theorem probe_arc (R : ArcReads P E ((g).map V) mem)
    (v : Placement.Site F) (site : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))
    (hsite : v.map V=siteCode E site) (a : Local.Slots S.degree S.colors) :
    (probe (S:=S) ptr v a).map V = encodeEnds P E (Local.incidentArc P a.1 site a.2) := by
  rw [probe,(valOps data mem vs).occurrence,hsite]
  change fromChild (words mem) ((g).map V) S.degree _ _ _ _ _ (((tagOrdinal S.colors _).val:ℕ):Word w) _ = _
  rw [Demand.tag_cast E.colors]
  exact local_arc R _ _ _ _ _ _ _

theorem eqSite_value (a b : Placement.Site F) :
    V (eqSite a b) = if a.map V=b.map V then 1 else 0 := by
  by_cases hb : V a.base=V b.base <;> by_cases ht : V a.tag=V b.tag <;> by_cases hl : V a.lane=V b.lane <;>
    simp [eqSite,Formula.value,RAM.DescriptorExpr.Comparison.test,Placement.Site.map,hb,ht,hl]

omit [Fintype B] in
theorem siteCode_injective (hi : Function.Injective E.base) : Function.Injective (siteCode E) := by
  rintro ⟨a,s,i⟩ ⟨b,z,j⟩ h
  have hb := hi (congrArg Placement.Site.base h)
  have hz := (tagOrdinal t).injective (Fin.ext (congrArg (fun x => x.tag.val) h))
  have hj := (tagOrdinal l).injective (Fin.ext (congrArg (fun x => x.lane.val) h))
  exact Prod.ext hb (Prod.ext hz hj)

private theorem role_map (r : RoleSites F) (i : Fin 3) :
    (Graph.siteAt r i).map V=Graph.siteAt (r.map V) i := by
  fin_cases i <;> rfl

omit [Fintype B] [Fintype H] in
private theorem packed_party (lay : Bool) (z : P.Motif) (j : Fin 6) :
    Graph.siteAt (⟨siteCode E (P.roleA z),siteCode E (P.roleB z),siteCode E (P.roleD lay z),1⟩ :
      RoleSites (Word w)) (ShrinkMotif.role lay j)=siteCode E (partySite P lay z j) := by
  cases lay <;> fin_cases j <;> rfl

omit [Fintype B] [Fintype H] in
theorem probe_roles (R : ArcReads P E ((g).map V) mem) (v : Placement.Site F)
    (site : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (hsite : v.map V=siteCode E site)
    (a : Local.Slots S.degree S.colors) (lay : Bool) (z : P.Motif)
    (arc : Local.incidentArc P a.1 site a.2=z.val) :
    (probeRoles (S:=S) ptr lay v a).map V=
      ⟨siteCode E (P.roleA z),siteCode E (P.roleB z),siteCode E (P.roleD lay z),1⟩ := by
  rw [probeRoles,(valOps data mem vs).parties,probe_arc P E ptr data mem vs R v site hsite a,arc,roles_code R]

omit [Fintype B] [Fintype H] in
theorem present_value (R : ArcReads P E ((g).map V) mem) (hi : Function.Injective E.base)
    (v : Placement.Site F) (site : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l)) (hsite : v.map V=siteCode E site)
    (a : Local.Slots S.degree S.colors) (lay : Bool) (z : P.Motif) (arc : Local.incidentArc P a.1 site a.2=z.val)
    (j : Fin 6) :
    V (present (S:=S) ptr lay v a j)=if partyBits P lay site z j then 1 else 0 := by
  rw [present,eqSite_value,role_map,probe_roles P E ptr data mem vs R v site hsite a lay z arc,
    hsite,packed_party]
  simp only [(siteCode_injective E hi).eq_iff,partyBits,decide_eq_true_eq]

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
