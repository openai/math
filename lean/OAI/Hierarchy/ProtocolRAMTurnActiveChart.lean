import OAI.Hierarchy.ProtocolRAMTurnSnapshotChart

namespace OAI
/-! # True physical turn fields on one positive-width item -/
namespace Hierarchy.ProtocolRAMTurnChart
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM ProtocolRAMTurnItinerary
open scoped Fin.CommRing
variable {W N : ℕ}

structure Data.At (d : Data) (v : Words) (m : Memory W) (u : Geometry) : Prop where
  rawSource : d.rawSource.read m (u.item:Word W)=(v.rawSource u.item:Word W)
  rawTarget : d.rawTarget.read m (u.item:Word W)=(v.rawTarget u.item:Word W)
  width : d.oldWidth.read m (u.item:Word W)=(v.width u.item:Word W)
  sourceRole : d.sourceRole.read m (u.item:Word W)=(v.sourceRole u.item:Word W)
  targetRole : d.targetRole.read m (u.item:Word W)=(v.targetRole u.item:Word W)
  halfSource : d.half.read m (v.sourceRole u.item:Word W)=((v.sourceRole u.item/2:ℕ):Word W)
  halfTarget : d.half.read m (v.targetRole u.item:Word W)=((v.targetRole u.item/2:ℕ):Word W)
  srcRoom : v.rawSource u.item < 2^W
  dstRoom : v.rawTarget u.item < 2^W

/-- The old endpoints and seat lookup are authenticated only at the indicated
original item. Neither the bank data nor the header of another row enters. -/
theorem row_at (base bits : ℕ) (d : Data) (u : Fin N → Geometry) (v : Words)
    (site : Fin N → ℕ) (m : Memory W) (i : Fin N) (header : Loaded base bits u m)
    (data : d.At v m (u i)) (atSite : d.site.read m (i.val:Word W)=(site i:Word W))
    (pos : (u i).raw ≤ (u i).length) (small : (u i).length < 2^W) (one : 1 < 2^W) :
    (chart base bits d).Row m (i.val:Word W) (record u v site i) := by
  have ir : (get base bits 0).eval m (i.val:Word W)=((u i).item:Word W) := header 0 i
  have ln : (get base bits 2).eval m (i.val:Word W)=((u i).length:Word W) := header 2 i
  have raw : (get base bits 3).eval m (i.val:Word W)=((u i).raw:Word W) := header 3 i
  have pe : (get base bits 4).eval m (i.val:Word W)=((u i).permanent.toNat:Word W) := header 4 i
  have lab : (get base bits 5).eval m (i.val:Word W)=((u i).label:Word W) := header 5 i
  have nz : (1:Word W)≠0 := by
    intro same
    have hv:=congrArg Fin.val same
    change ((1:ℕ):Word W).val=0 at hv
    rw [Fin.val_cast_of_lt one] at hv
    omega
  have dir : (direction (get base bits 0) d).eval m (i.val:Word W)=((rev v (u i).item).toNat:Word W) := by
    have lt : ((v.rawSource (u i).item:Word W)<(v.rawTarget (u i).item:Word W)) ↔
        v.rawSource (u i).item<v.rawTarget (u i).item := by
      change (_:Word W).val<(_:Word W).val ↔ _
      rw [Fin.val_cast_of_lt data.srcRoom,Fin.val_cast_of_lt data.dstRoom]
    by_cases h : v.rawSource (u i).item<v.rawTarget (u i).item
    · have hw := lt.mpr h
      simp [direction,Expr.eval,Comparison.test,ir,data.rawSource,data.rawTarget,hw,h,rev]
    · have hw : ¬((v.rawSource (u i).item:Word W)<(v.rawTarget (u i).item:Word W)) := fun bad=>h (lt.mp bad)
      simp [direction,Expr.eval,Comparison.test,ir,data.rawSource,data.rawTarget,hw,h,rev]
  refine ⟨ir,header 1 i,ln,?_,dir,?_,atSite,?_⟩
  · change (Expr.branch .eq (direction (get base bits 0) d) (.lit 0) _ _).eval m _=_
    cases hr : rev v (u i).item <;>
      simp [Expr.eval,Comparison.test,dir,hr,nz,ln,raw,RowOp.opcode,BinaryOp.eval,record,Nat.cast_sub pos]
  · exact (congrArg (d.oldWidth.read m) ir).trans data.width
  · have zd : 2^W ∣ (u i).raw ↔ (u i).raw=0 :=
      ⟨fun hh=>Nat.eq_zero_of_dvd_of_lt hh (pos.trans_lt small),fun hh=>hh ▸ dvd_zero _⟩
    cases hp : (u i).permanent <;> by_cases hs : (u i).raw=0 <;>
      simp [chart,seat,record,Expr.eval,Comparison.test,pe,raw,ir,lab,hp,hs,nz,zd,data.sourceRole,
        data.targetRole,data.halfSource,data.halfTarget]

theorem observed_live (header bits src : ℕ) (d : Data) (u : Fin N→Geometry) (w : Words) (site : Fin N→ℕ)
    (b : Banks) (m : Memory W) (loaded : Loaded header bits u m)
    (shape : ∀i,(u i).raw ≤ (u i).length) (small : ∀i,(u i).length<2^W)
    (weight : ∀i,d.oldWidth.read m ((u i).item:Word W)=(w.width (u i).item:Word W))
    (auth : ∀i,0<w.width (u i).item → d.At w m (u i) ∧ d.site.read m (i.val:Word W)=(site i:Word W) ∧ site i<2^W)
    (one : 1<2^W) (fit : ∀ f,(field (chart header bits d) b f).Fits W src) (room : src+7*N<2^W) :
    let r := record u w site
    let v := ProtocolRAMTurnSnapshot.values b m
    ∃ out,(program W src N (chart header bits d) b).Exec m out (ticks src N (chart header bits d) b) ∧
      (∀ (i : Fin N) (f : Fin 7), f=4 ∨ (r i).field v 4≠0 →
        out (src+f.val*N+i.val)=((r i).field v f:Word W)) ∧
      ∀ a,a<src ∨ src+7*N≤a → out a=m a := by
  intro r v
  apply ProtocolRAMTurnItinerary.observed_live src _ b r v m one fit room
  · intro i
    change (if rev w (u i).item then _ else _)≤_
    split
    · exact Nat.sub_le ..
    · exact shape i
  · intro i
    have item : (get header bits 0).eval m (i.val:Word W)=((u i).item:Word W) := loaded 0 i
    exact width_at _ m _ _ ((congrArg (d.oldWidth.read m) item).trans (weight i))
      (not_lt_of_ge (ProtocolRAMTurnSnapshot.position_within header bits d m u i loaded (shape i) (small i)))
  · intro i live
    obtain ⟨words,atSite,siteRoom⟩ := auth i live
    exact ⟨row_at header bits d u w site m i loaded words atSite (shape i) (small i) one,
      ProtocolRAMTurnSnapshot.adjacent b m _,small i,siteRoom⟩

end Hierarchy.ProtocolRAMTurnChart

end OAI
