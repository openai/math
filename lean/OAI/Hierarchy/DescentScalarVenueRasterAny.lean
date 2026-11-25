import OAI.Hierarchy.DescentScalarVenueRaster
import OAI.Hierarchy.DescentScalarVenueHeaderAny

namespace OAI
/-! # The fixed venue raster program on all RAM tapes -/
namespace Hierarchy.DescentScalarVenueMask.Raster
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentPackedColony DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure Receiver
open scoped Classical Fin.CommRing
noncomputable section
variable {P r cap raw low k gain slots H G M w : ℕ}
local notation "A"=>DescentPackedActorMask.actors (P*r) cap

structure Room (S : Shape P r cap) (base H G M w : ℕ) : Prop where
  shape : Accessible S.ports S.hub H G M w base
  endsFit : S.ends.Fits w base
  endsRoom : H*P≤S.ends.size
  routeFit : ∀x j,(S.route x j).Fits w base
  routeRoom : ∀x j,H*chunks G M≤(S.route x j).size
  keyFit : ∀x j,(S.key x j).Fits w base
  keyRoom : ∀x j,H*chunks G M≤(S.key x j).size

theorem any (S : Shape P r cap) (k gain slots raw low H G M base : ℕ) (m : Memory w)
    (old : Room S base H G M w) (hi : output P r cap raw low H G M base+H*chunks G M<2^w) :
    let o:=result S k gain slots raw low H G M base m;let final:=output P r cap raw low H G M base+H*chunks G M
    (code S k gain slots raw low H G M base w).Exec m o (ticks S k gain slots raw low H G M base) ∧
    (∀j,j<base ∨ final≤j → o j=m j) ∧ CheapCode (code S k gain slots raw low H G M base w) :=by
  intro o final
  let ports:=S.ports;let route:=S.route;let key:=S.key;let hub:=S.hub
  let f:=entries k gain slots raw low A;let u:=unit raw low A;let start:=header base raw low M A
  let out:=Headers.post start H G M P;let C:=view ports route key hub k gain slots raw low M H G base
  let mid:=Book.image f u M base m
  let state:=Headers.image ports.roster S.ends start H G M P mid
  change out+H*chunks G M<2^w at hi
  have next : start≤out:=by
    dsimp [start,out,Headers.post,Headers.rom,Headers.afterHeaders,Headers.start,DescentPackedChildNeighbor.SIMD.ROM.output]
    repeat first | exact le_rfl | apply Nat.le_add_right_of_le
  have before:base≤ start:=Nat.le_add_right ..;have early:=before.trans next;have endFit:out<2^w:=(Nat.le_add_right ..).trans_lt hi
  have liftB {x y : ℕ} (h:x≤y) (B:Bank) (ok:B.Fits w x):B.Fits w y:=⟨ok.1,ok.2.1,ok.2.2.trans h⟩
  obtain ⟨init,dict,fr,cost⟩:=Book.mount f u M base m (width k gain slots raw low A) (next.trans_lt endFit)
  obtain ⟨headers,queryFit,rest,cheap⟩:=Headers.any ports.roster S.ends start H G M P mid
    (liftB before _ old.shape.roster) (liftB before _ old.endsFit) old.shape.rosterRoom old.endsRoom hi
  have geom (i : Fin (2+A)):=Book.geometry f u M base i next endFit (width k gain slots raw low A i)
  have access (B:Bank) (cap_:H*chunks G M≤B.size) (fit:B.Fits w base):Accessible ports B H G M w out:=
    ⟨fun j=>liftB early _ (old.shape.ids j),old.shape.idsRoom,liftB early _ old.shape.roster,old.shape.rosterRoom,liftB early _ old.shape.offsets,old.shape.offRoom,
    liftB early _ old.shape.chunks,old.shape.chunkRoom,liftB early B fit,cap_⟩
  have reg (s x j):=(queryFit s _ (peer_fits ports (route x j) out (access _ (old.routeRoom x j) (old.routeFit x j)) s))
  have low_ (s x j):=(peer_fits ports (key x j) out (access _ (old.keyRoom x j) (old.keyFit x j)) s)
  have hf : (Expr.lookup hub .row).Fits w out:=⟨liftB early _ old.shape.source,trivial⟩
  let priorIdx:Fin (2+A):=finSumFinEquiv (.inl (0:Fin 2));let trimIdx:Fin (2+A):=finSumFinEquiv (.inl (1:Fin 2))
  have keep (s x j) := (show DescentPackedZip.Fits (C.head s).prior (DescentPackedChildNeighbor.SIMD.body (C.head s).host (peerExpr ports (route x j) H s) (List.finRange P)) (peerExpr ports (key x j) H s) 1 (Packed.bits raw) M out w from
    ⟨DescentPackedChildNeighbor.SIMD.fitted _ _ (reg s x j) _,low_ s x j,(geom priorIdx).1,(geom priorIdx).2,
     by simp [C,view,entries,Book.tables,gate],by simp [C,view,entries,Book.tables,gate]⟩)
  have trim (s x j) := (show DescentPackedZip.Fits (C.head s).trim (.lookup hub .row) ((C.head s).prior.read (DescentPackedChildNeighbor.SIMD.body (C.head s).host (peerExpr ports (route x j) H s) (List.finRange P)) (peerExpr ports (key x j) H s)) 1 (Packed.bits raw) M out w from
    ⟨hf,readable (keep s x j),(geom trimIdx).1,(geom trimIdx).2,by simp [C,view,entries,Book.tables,gate],by simp [C,view,entries,Book.tables,gate]⟩)
  have bound : Gather.Bounds (d:=Packed.bits low) (w:=w) (M:=M) C.masks (C.one H) out :=by
    intro j; let t : Fin (2+A) :=finSumFinEquiv (Sum.inr j);let z:Fin (P*r)×Fin (1+cap*6):=finProdFinEquiv.symm j;let part:Fin P×Fin r:=finProdFinEquiv.symm z.1
    refine ⟨readable (trim part.1 part.2 z.2),(geom t).1,(geom t).2,?_,?_⟩ <;> simp [C,view,entries,gate,Book.tables]
  have safe : (C.all H).Fits w out:=Gather.fits C.masks (C.one H) out bound _
  refine ⟨Procedure.Exec.then (Procedure.Exec.then init headers) (scan_exec out (H*chunks G M) (C.all H) state safe hi),?_,cheap_seq (cheap_seq cost cheap) (@scan_cheap _ _ _ _)⟩
  intro j outside;rcases outside with lower|upper
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (lower.trans_le early))).trans ((rest _ (.inl (lower.trans_le before))).trans (fr _ (.inl lower)))
  · have up : out≤j:=(Nat.le_add_right ..).trans upper
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr upper)).trans ((rest _ (.inr up)).trans (fr _ (.inr (next.trans up))))

end
end Hierarchy.DescentScalarVenueMask.Raster

end OAI
