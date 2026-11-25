import OAI.Hierarchy.DescentStageVenueAny

namespace OAI
/-! # Retention of the separate one-bit actor planes at the end of a venue date -/
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentSIMDLookup DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- The final halo tables and the aggregation of the actor bitmap are all
written after the block planes. This frame holds on arbitrary word contents. -/
theorem image_below (B:Sources) (base k H G M D:ℕ) (m:Memory w) (j:ℕ) (low:j<base):
    image B base k H G M D m j=m j:=by
  let ptr:=Venue.outBase base k M
  let rom:=DescentStaticWordColumn.image base
    (DescentPackedColumnSum.literals 1 M (1*2^k) (fun _:Fin (2^k)=>1) Venue.place) m (2^k*2^(1*M))
  let op:=DescentPackedColumnSum.reads base 1 M (fun _:Fin (2^k)=>1) (input B k)
  have low₁:j<ptr:=low.trans_le (Nat.le_add_right ..)
  have low₂:j<area base k H G M:=low₁.trans_le (Nat.le_add_right ..)
  exact (DescentStaticWordColumn.frame (area base k H G M) (DescentScalarHaloPortROM.length H G M D)
    (DescentScalarHaloPortROM.literal H G M D) (Venue.after base k H G M (input B k) m) j (.inl low₂)).trans
    ((ProtocolRAMGeneratedWrite.frame_image ptr _ op rom j (.inl low₁)).trans
      (DescentStaticWordColumn.frame base _ _ m j (.inl low)))

namespace Date
noncomputable section
variable (d:Date) (B:Sources)

/-- At the same memory that the next date reads, each original one-bit block
plane remains available at its own page, at the common output pitch. -/
theorem phase_actor_plane (base:ℕ) (m:Memory w) (space:d.Space B base w) (positive:0<d.aliveLanes)
    (rows:Fin (2^d.k)→Fin d.hosts→Fin d.groups→Cell 1)
    (alive:∀x:Fin (2^d.k),Reads (B.alive x.val) (rows x) d.aliveLanes m):
    ∀x:Fin (2^d.k),Reads ((d.transported B base).alive x.val) (rows x) d.lanes (d.image B base m):=by
  obtain ⟨o₀,o₁,o₂,o₃⟩:=d.order base
  have lift {T:Bank} {u v:ℕ} (f:T.Fits w u) (uv:u≤v):T.Fits w v:=⟨f.1,f.2.1,f.2.2.trans uv⟩
  let s:=DescentVenueSlabs.image d.signedShape (d.signedPage B) base m
  let p:=DescentVenueSlabs.image d.paidShape (fun x=>B.paid x.val) (d.firstEnd base) s
  let a:=DescentVenueSlabs.image d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) p
  have first:=DescentVenueSlabs.any d.signedShape (d.signedPage B) base m
    (fun i=>(space.signed _ _).1) ((o₁.trans (o₂.trans o₃)).trans_lt space.roof)
  have second:=DescentVenueSlabs.any d.paidShape (fun x=>B.paid x.val) (d.firstEnd base) s
    (fun i=>lift (space.paid i).1 o₀) ((o₂.trans o₃).trans_lt space.roof)
  have kept (x:Fin (2^d.k)) (r:Row d.hosts d.groups d.aliveLanes):
      p ((B.alive x.val).base+(row d.hosts d.groups d.aliveLanes r).val)=((data (rows x) r).val:Word w):=by
    have low:= (Nat.add_lt_add_left ((row d.hosts d.groups d.aliveLanes r).isLt.trans_le (space.alive x).2) _).trans_le
      (space.alive x).1.2.2
    exact (second.2 _ (.inl (low.trans_le o₀))).trans ((first.2 _ (.inl low)).trans (alive x r))
  have packed:=DescentVenueSlabs.run d.aliveShape (fun x=>B.alive x.val) (d.secondEnd base) p rows
    (fun x=>lift (space.alive x).1 (o₀.trans o₁)) (fun x=>(space.alive x).2) kept positive (o₃.trans_lt space.roof)
  intro x r
  let out:=DescentVenueSlabs.page d.aliveShape (d.secondEnd base) x.val
  have low:out.base+(row d.hosts d.groups d.lanes r).val<d.thirdEnd base:=
    (Nat.add_lt_add_left ((row d.hosts d.groups d.lanes r).isLt.trans_le (packed.2.2.1 x).2) _).trans_le
      (packed.2.2.1 x).1.2.2
  exact (image_below (d.transported B base) (d.thirdEnd base) d.k d.hosts d.groups d.lanes d.degree a _
    low).trans (packed.2.1 x r)

end
end Date
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
