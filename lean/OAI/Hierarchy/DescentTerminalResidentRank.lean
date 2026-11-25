import OAI.Hierarchy.DescentTerminalReachedOrder
import OAI.Hierarchy.DescentTerminalCableSlots
import OAI.Hierarchy.DescentGroupNextDigit

namespace OAI
/-! # The receiver's ordered vertex ordinal is the physical calendar's masked prefix -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentColonies DescentTerminalGraphPositions DescentTerminalCableOrder DescentPhysicalOrder
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist p : ℕ}
    (R:Reached W G price ε S k age z degree wire hist)

def calendar (i : Fin (S.hostSize age)) : {v:W.graph.Site //R.home v=i} ↪ Fin (S.groupCount age*2^k) :=
  (R.slot i).trans finProdFinEquiv.toEmbedding

theorem calendar_val (i : Fin (S.hostSize age)) (u : {v //R.home v=i}) :
    (R.calendar i u).val=(R.placement.pos u.val).1.val*2^k+(R.placement.block u.val).val := by
  change (R.placement.block u.val).val+2^k*(R.placement.pos u.val).1.val=_
  ring

theorem calendar_compare (i : Fin (S.hostSize age)) (x y : {v //R.home v=i}) :
    R.placement.site R.vertex R.valid.coordinates x.val<R.placement.site R.vertex R.valid.coordinates y.val ↔
      R.calendar i x<R.calendar i y := by
  let old:=R.placement.siteSlot R.vertex R.valid.coordinates
  have host: (R.placement.pos x.val).2=(R.placement.pos y.val).2 := R.home_eq.mp (x.property.trans y.property.symm)
  change physical (DescentSiteTape.rank old) x.val<physical (DescentSiteTape.rank old) y.val ↔ _
  rw [physical_lt_iff]
  change (old x.val).val<(old y.val).val ↔ (R.calendar i x).val<(R.calendar i y).val
  rw [GroupStage.siteSlot_val,GroupStage.siteSlot_val,calendar_val,calendar_val,host]
  let a:=(R.placement.pos x.val).1.val
  let b:=(R.placement.pos y.val).1.val
  let h:=(R.vertex (R.placement.pos y.val).2).val
  have both : a*Fintype.card R.V+h=b*Fintype.card R.V+h ↔ a=b := by
    have hpos:= (R.vertex (R.placement.pos y.val).2).isLt
    have pos : 0<Fintype.card R.V := Nat.zero_lt_of_lt hpos
    exact ⟨fun eqn=>Nat.eq_of_mul_eq_mul_right pos (Nat.add_right_cancel eqn),fun eqn=>eqn ▸ rfl⟩
  simp only [GroupStage.nextDigit (R.placement.block x.val).isLt (R.placement.block y.val).isLt,
    GroupStage.nextDigit (R.vertex (R.placement.pos y.val).2).isLt (R.vertex (R.placement.pos y.val).2).isLt,
    lt_self_iff_false,and_false,or_false]
  exact or_congr Iff.rfl (and_congr both Iff.rfl)

theorem ordinal_count {X : Type} [Fintype X] (r : X≃Fin (Fintype.card X)) (s : X↪ℕ)
    (same : ∀u v,r u<r v ↔ s u<s v) (u : X) :
    (r u).val=(Finset.univ.filter (fun v=>s v<s u)).card := by
  have e : (Finset.univ.filter (fun v=>s v<s u)).map r.toEmbedding=Finset.Iio (r u) := by
    ext j
    obtain ⟨v,rfl⟩:=r.surjective j
    simp [same]
  simpa [Finset.card_map] using (congrArg Finset.card e).symm

/-- Regard a local node as a resident of the corresponding reached host. -/
def homeFiber (L : Order W.graph (S.hostSize age) p) (sameHome : L.home=R.home)
    (i : Fin (S.hostSize age)) : L.Nodes i ↪ {v : W.graph.Site // R.home v=i} where
  toFun t := ⟨t.val, sameHome ▸ t.property⟩
  inj' _ _ e := Subtype.ext (congrArg (fun t : {v : W.graph.Site // R.home v=i} => t.val) e)

theorem rank_read (L : Order W.graph (S.hostSize age) p) (sameHome : L.home=R.home)
    (ranks : ∀u,L.nodeRank u=(R.placement.site R.vertex R.valid.coordinates u).val)
    (i : Fin (S.hostSize age)) (u : L.Nodes i) :
    let f : L.Nodes i↪Fin (S.groupCount age*2^k) :=
      (R.homeFiber L sameHome i).trans (R.calendar i)
    ((L.nodes i) u).val=(Finset.univ.filter fun t=>f t<f u).card := by
  intro f
  apply ordinal_count (L.nodes i) (f.trans Fin.valEmbedding)
  intro x y
  rw [Order.nodes,ordered_lt]
  change L.nodeRank x.val<L.nodeRank y.val ↔ _
  rw [ranks x.val,ranks y.val]
  exact R.calendar_compare i (R.homeFiber L sameHome i x) (R.homeFiber L sameHome i y)

/-- The packed mask may skip any number of unoccupied group/block addresses. -/
theorem mask_prefix {X : Type} [Fintype X] {N : ℕ} (f : X↪Fin N) (active : Fin N→Bool)
    (live : ∀n,active n=true ↔ ∃u,f u=n) (x : X) :
    (Finset.univ.filter (fun u=>f u<f x)).card=(Finset.univ.filter (fun i=>active i=true ∧ i<f x)).card := by
  have eqn : (Finset.univ.filter (fun u=>f u<f x)).map f=Finset.univ.filter (fun i=>active i=true ∧ i<f x) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_map,Finset.mem_univ,true_and,live]
    constructor
    · rintro ⟨u,h,rfl⟩;exact ⟨⟨u,rfl⟩,h⟩
    · rintro ⟨⟨u,rfl⟩,h⟩;exact ⟨u,h,rfl⟩
  simpa using congrArg Finset.card eqn

end
end Hierarchy.DescentSixParty.Reached

end OAI
