import OAI.ThreeFlat.Diagonal.CompressorIncidentRows
import OAI.ThreeFlat.Diagonal.CompressorResidentInput

namespace OAI
/-! # Incident enumeration directly from the resident, title-addressed old graph -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
open Incidents

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l : ℕ}
variable {S : Graph.Stage} {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {hc : 2≤S.colors} {lay : Bool} {p : Pointers} {cell : Word w} {mem : Memory w}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ} {supply : P.Motif → Fin 8 → ℕ}
variable (I : Input S P b hc lay p cell prior supply mem) (E : Codec B w S.colors t l)
variable (number : ∀u,E.base u=((b u).val:Word w))
variable (add : ∀u v,slotCode (w:=w) P (u+v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (sub : ∀u v,slotCode (w:=w) P (u-v)=BinaryOp.bitXor.eval (slotCode P u) (slotCode P v))
variable (baseFit : N≤2^w) (tagsFit : 2^t<2^w) (lanesFit : 2^l<2^w)
variable (bits : 2^S.colors<2^w) (masks : 8≤w) (cap : Incidents.capacity S<2^w) (offset : 0<p.oldWidths)
variable (K : ℕ) (s : Computability.VPVNP.Compression.Site B (BitWord t) (BitWord l))

local notation "V" => Formula.value (fun _ => cell) mem
local notation "keysHere" => siteKeys (w:=w) P b lay s

include I E number add sub baseFit tagsFit lanesFit bits masks cap offset in
omit [Fintype B] [Fintype H] in
theorem Input.incident_site :
    ∃ order : SiteOrder P b lay s w, (keysHere).length≤Incidents.capacity S ∧
      (∀ (vs : Fin 1 → Word w) (site : Incidents.F), (V vs site).val=Incidents.siteNumber b s →
        (V vs (Incidents.count Template.ptr S K lay site)).val=(keysHere).length) ∧
      (∀ (vs : Fin 1 → Word w) (linear : Incidents.F) (i : Fin (keysHere).length) (field : Fin 6),
        (V vs linear).val=6*(Incidents.capacity S*Incidents.siteNumber b s+i.val)+field.val →
        V vs (Incidents.record Template.ptr S K lay linear)=
          Incidents.descriptor P b Template.ptr (fun _=>cell) mem vs hc K lay s (order.equiv i).val field) ∧
      (∀ (vs : Fin 1 → Word w) (linear : Incidents.F) (i : ℕ) (field : Fin 6),
        (keysHere).length≤ i → i<Incidents.capacity S →
        (V vs linear).val=6*(Incidents.capacity S*Incidents.siteNumber b s+i)+field.val →
        V vs (Incidents.record Template.ptr S K lay linear)=0) := by
  have inj : Function.Injective E.base := by
    intro u v h
    apply b.injective
    apply Fin.ext
    rw [number,number] at h
    have q := congrArg Fin.val h
    rwa [Fin.val_cast_of_lt ((b u).isLt.trans_le baseFit),Fin.val_cast_of_lt ((b v).isLt.trans_le baseFit)] at q
  have keysFit (a) : Demand.key P (baseNat b) a+1<2^w := by
    have bound := (Nat.add_lt_add_left (SlotImage.edgeOrdinal_lt b (Demand.laneOrdinal P)
      (packedAddress.symm a)) p.oldWidths).trans_le I.widthBound
    rw [Demand.edge_address] at bound
    omega
  have tv (vs : Fin 1 → Word w) : (V vs (Template.f tags)).val=2^t := by
    have h : V vs (Template.f tags)=((2^t:ℕ):Word w) := I.hdr.field vs 15
    rw [h,Fin.val_cast_of_lt tagsFit]
  have lv (vs : Fin 1 → Word w) : (V vs (Template.f remaining)).val=2^l := by
    have h : V vs (Template.f remaining)=((2^l:ℕ):Word w) := I.hdr.field vs 14
    rw [h,Fin.val_cast_of_lt lanesFit]
  let vs₀ : Fin 1 → Word w := fun _ => 0
  let v : Placement.Site Incidents.F := ⟨.lit (E.base s.1).val,.lit (tagWord E.tags s.2.1).val,
    .lit (tagWord E.lanes s.2.2).val⟩
  have v0 : v.map (V vs₀)=siteCode E s := by
    simp [v,siteCode,Placement.Site.map,Formula.value,Fin.ofNat_eq_cast]
  obtain ⟨order⟩ := site_order P b lay s E Template.ptr _ mem vs₀ (I.arc E vs₀ number add sub)
    (I.widths E vs₀ number) inj hc bits masks keysFit K v v0
  have length := siteKeys_le P b lay s E Template.ptr _ mem vs₀ (I.arc E vs₀ number add sub)
    (I.widths E vs₀ number) inj hc bits masks K v v0
  refine ⟨order,length,?_,?_,?_⟩
  · intro vs site address
    rw [count_at P b lay s E Template.ptr _ mem vs (I.arc E vs number add sub) (I.widths E vs number)
      inj hc bits masks K (tv vs) (lv vs) site address,Fin.val_cast_of_lt (length.trans_lt cap)]
  · intro vs linear i field address
    exact record_at P b lay s E Template.ptr _ mem vs (I.arc E vs number add sub) (I.widths E vs number)
      inj hc bits masks keysFit K (tv vs) (lv vs) cap order linear i field (i.isLt.trans_le length) address
  · intro vs linear i field past hcap address
    exact record_after P b lay s E Template.ptr _ mem vs (I.arc E vs number add sub) (I.widths E vs number)
      inj hc bits masks K (tv vs) (lv vs) cap linear i field hcap past address


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end

end OAI
