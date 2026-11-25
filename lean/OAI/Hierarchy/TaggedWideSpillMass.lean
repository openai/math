import OAI.Hierarchy.TaggedWideControlValues
import OAI.Hierarchy.TaggedWideSpillLayout

namespace OAI
/-! # Native spill-only neighbor sums on a different site's whole-role directory -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.RAM DescriptorExpr
open Tagged PassiveWindow Calendar.WideCPU
open scoped Classical Fin.CommRing BigOperators
variable {S W D cap : ℕ} {s : Fin S}
variable {t u : ((portGraph S).Port s)→ℕ} (m : Memory W) (reg : Word W)
  (a : Parts ((portGraph S).Port s) (Fin D) cap t) (b : Parts ((portGraph S).Port s) (Fin D) cap u)
  (x y : Fin D→LocalPrefix.Columns)
  (small : ApertureGeometry m reg a x) (whole : ApertureGeometry m reg b y)

private theorem width_at {t : ((portGraph S).Port s)→ℕ} (a : Parts ((portGraph S).Port s) (Fin D) cap t) (x : Fin D→LocalPrefix.Columns)
    (small : ApertureGeometry m reg a x) (i : Fin D) :
    (x i).width.eval m reg=(a.width i:Word W) := by
  rw [small.neighbors.widthAt]
  cases hit:a.owner i with
  | none=>
    have z : a.width i=0 := by
      by_contra ne
      have live:=(small.owned i).mpr (Nat.pos_of_ne_zero ne)
      simp [hit] at live
    simp [PacketNeighbor.amount,hit,z]
  | some p=>simp [PacketNeighbor.amount,hit]

include small whole in
private theorem cross_weight (sites : S≤2^W) (i j : Fin D) :
    (weight (x i) (y j)).eval m reg=
      ((b.owner j).elim 0 (fun p=>if a.owner i=some p then a.width i else 0):ℕ) := by
  have wx:=width_at m reg a x small i
  have wy:=width_at m reg b y whole j
  cases target:b.owner j with
  | none=>
    have zero:=(whole.neighbors.widthAt j)
    simp only [PacketNeighbor.amount,target,Option.elim_none,Nat.cast_zero] at zero
    simp [weight,active,Expr.eval,Comparison.test,zero]
  | some q=>
    have live : 0<b.width j := (whole.owned j).mp (by simp [target])
    have bound:=whole.neighbors.fits j
    simp only [PacketNeighbor.amount,target,Option.elim_some] at bound
    have nonzero : (y j).width.eval m reg≠0 := by
      rw [wy];intro h
      have eq:=congrArg Fin.val h
      simp only [Fin.val_cast_of_lt bound,Fin.val_zero] at eq
      omega
    cases source:a.owner i with
    | none=>
      have zx:=small.neighbors.widthAt i
      simp only [PacketNeighbor.amount,source,Option.elim_none,Nat.cast_zero] at zx
      simp [weight,active,Expr.eval,Comparison.test,nonzero,zx]
    | some p=>
      have positive : 0<a.width i := (small.owned i).mp (by simp [source])
      have same : (x i).opposite.eval m reg=(y j).opposite.eval m reg ↔ p=q := by
        rw [small.neighbors.siteAt i p source positive,whole.neighbors.siteAt j q target live]
        constructor
        · intro eq
          apply PacketNeighbor.other_injective
          apply Fin.ext
          simpa only [Fin.val_cast_of_lt ((PacketNeighbor.other p).isLt.trans_le sites),
            Fin.val_cast_of_lt ((PacketNeighbor.other q).isLt.trans_le sites)] using congrArg Fin.val eq
        · rintro rfl;rfl
      by_cases matchPeer:p=q <;> simp [weight,active,Expr.eval,Comparison.test,nonzero,same,matchPeer,wx]

include small in
private theorem chord_mass (p : (portGraph S).Port s) :
    (∑i,if a.owner i=some p then a.width i else 0)=t p := by
  by_cases live:∃j,a.owner j=some p
  · obtain ⟨j,hj⟩:=live
    have each (i : Fin D) : (if a.owner i=some p then a.width i else 0)=(ChordAperture.sizeAt a i j).val := by
      by_cases hi:a.owner i=some p <;> simp [ChordAperture.sizeAt,ChordAperture.code,hj,hi]
    simp only [each,small.total,ChordAperture.room,hj,Option.elim_some]
  · have no (i : Fin D) : a.owner i≠some p:=fun yes=>live ⟨i,yes⟩
    have zero : t p=0:=by
      by_contra nz
      obtain ⟨i,owner,_⟩:=a.covers p ⟨0,Nat.pos_of_ne_zero nz⟩
      exact no i owner
    simp [no,zero]

include small whole in
theorem spill_low_read (sites : S≤2^W) (q : Fin D) :
    ((spillLow y x q).eval m reg).val=(b.owner q).elim 0 t := by
  have numeric (p : (portGraph S).Port s) : t p<2^W := by
    by_cases positive : 0<t p
    · obtain ⟨i,hit,_⟩:=a.covers p ⟨0,positive⟩
      simpa [ChordAperture.room,hit] using small.roomFit i
    · rw [Nat.eq_zero_of_not_pos positive];exact Nat.two_pow_pos _
  simp only [spillLow,LocalPrefix.total_eval,cross_weight m reg a b x y small whole sites]
  cases hit:b.owner q with
  | none=>simp
  | some p=>simp only [Option.elim_some,←Nat.cast_sum,chord_mass m reg a x small,Fin.val_cast_of_lt (numeric p)]

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
