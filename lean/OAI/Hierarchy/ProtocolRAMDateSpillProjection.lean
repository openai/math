import OAI.Hierarchy.ProtocolRAMDateSpillOffsets
import OAI.Hierarchy.TaggedWideDateApertures
import OAI.Hierarchy.TaggedWideSpillDates

namespace OAI
/-! # Ordered spill offsets and the complete spill segment at a full physical role -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM.DescriptorExpr
open Tagged PassiveWindow
open scoped Classical Fin.CommRing BigOperators
variable {W S n D : ℕ} (ends : Fin n→Chord S) (qty : Fin n→ℕ) (s : Fin S)
variable (place : EndsAt ends qty s ↪ Fin D) (tag : Fin n→ℕ) (m : Memory W) (r : Word W)
variable (row : Fin D→LocalPrefix.Columns) (p : (portGraph S).Port s)
private abbrev ChordRows (ends : Fin n → Chord S) (qty : Fin n → ℕ) (e : Chord S) :=
  {i : Fin n // 0 < qty i ∧ key ends i = Fintype.equivFin (Chord S) e}

def liftRole (i : ChordRows ends qty p.val.1) : EndsAt ends qty s :=
  ⟨⟨(i.val,p.val.2),by
    have eq : ends i.val=p.val.1:=(Fintype.equivFin _).injective i.property.2
    simpa only [rowGraph,portGraph,PortGraph.vertex,eq] using p.property⟩,i.property.1⟩

def sliceRoles : ChordRows ends qty p.val.1 ↪ Fin D where
  toFun i:=place (liftRole ends qty s p i)
  inj' _ _ eq:=Subtype.ext (congrArg (fun u : EndsAt ends qty s=>u.val.val.1) (place.injective eq))

/-- This is exactly the output of `SiteControls.dated_columns` on the
published only-spill triple, which includes the zero width in every vacancy. -/
def Seen (ends : Fin n → Chord S) (qty : Fin n → ℕ) (s : Fin S)
    (place : EndsAt ends qty s ↪ Fin D) (tag : Fin n → ℕ) (m : Memory W) (r : Word W)
    (row : Fin D → LocalPrefix.Columns) : Prop :=
  (∀u : EndsAt ends qty s,((row (place u)).ordinal.eval m r).val=tag u.val.val.1 ∧
    ((row (place u)).opposite.eval m r).val=(PacketNeighbor.other (byRow ends qty s u)).val ∧
    ((row (place u)).width.eval m r).val=qty u.val.val.1) ∧
  (∀q,q∉Set.range place→((row q).width.eval m r).val=0)

theorem slice_read (seen : Seen ends qty s place tag m r row) :
    (∀i : ChordRows ends qty p.val.1,((row (sliceRoles ends qty s place p i)).ordinal.eval m r).val=tag i.val ∧
      ((row (sliceRoles ends qty s place p i)).opposite.eval m r).val=(PacketNeighbor.other p).val ∧
      ((row (sliceRoles ends qty s place p i)).width.eval m r).val=qty i.val) ∧
    (∀q,q∉Set.range (sliceRoles ends qty s place p) →
      ((row q).opposite.eval m r).val≠(PacketNeighbor.other p).val ∨ ((row q).width.eval m r).val=0) := by
  constructor
  · intro i
    have eq : ends i.val=p.val.1:=(Fintype.equivFin _).injective i.property.2
    have port : byRow ends qty s (liftRole ends qty s p i)=p:=Subtype.ext (Prod.ext eq rfl)
    have got:=seen.1 (liftRole ends qty s p i)
    exact ⟨got.1,got.2.1.trans (congrArg (fun v=>(PacketNeighbor.other v).val) port),got.2.2⟩
  · intro q missing
    by_cases active : q∈Set.range place
    · obtain ⟨b,rfl⟩:=active
      apply Or.inl
      intro same
      have opposite : PacketNeighbor.other (byRow ends qty s b)=PacketNeighbor.other p:=
        Fin.ext ((seen.1 b).2.1.symm.trans same)
      have port := congrArg Subtype.val (PacketNeighbor.other_injective opposite)
      have eq : ends b.val.val.1=p.val.1:=congrArg Prod.fst port
      have side : b.val.val.2=p.val.2:=congrArg Prod.snd port
      let i : ChordRows ends qty p.val.1:=⟨b.val.val.1,b.property,congrArg (Fintype.equivFin _) eq⟩
      apply missing
      exact ⟨i,congrArg place (Subtype.ext (Subtype.ext (Prod.ext rfl side.symm)))⟩
    · exact Or.inr (seen.2 q active)

theorem Side.prefix_seen (source : Side D) (same : source.columns=row)
    (seen : Seen ends qty s place tag m r row) (order : StrictMono tag) (i : Fin n)
    (chord : ends i=p.val.1) (ordinal : (source.ordinal.eval m r).val=tag i)
    (neighbor : (source.opposite.eval m r).val=(PacketNeighbor.other p).val) :
    source.prefix.eval m r=(prefixAt ends qty i:Word W) := by
  have cells:=slice_read ends qty s place tag m r row p seen
  have keyEq : key ends i=Fintype.equivFin (Chord S) p.val.1:=congrArg (Fintype.equivFin _) chord
  let head : LocalPrefix.Columns:=⟨source.ordinal,source.opposite,.lit 1⟩
  have transfer (v : Fin (Fintype.card (Chord S)))
      (put : {j : Fin n // 0<qty j ∧ key ends j=v} ↪ Fin D)
      (on : ∀j,((row (put j)).ordinal.eval m r).val=tag j.val ∧
        ((row (put j)).opposite.eval m r).val=(head.opposite.eval m r).val ∧
        ((row (put j)).width.eval m r).val=qty j.val)
      (off : ∀l,l∉Set.range put→((row l).opposite.eval m r).val≠(head.opposite.eval m r).val ∨
        ((row l).width.eval m r).val=0) (vEq : v=key ends i) :
      (LocalPrefix.expr row head).eval m r=(prefixAt ends qty i:Word W) := by
    subst v
    exact LocalPrefix.read_sparse row head m r (key ends) qty tag order i put ordinal on off
  unfold Side.prefix
  rw [same]
  exact transfer (Fintype.equivFin (Chord S) p.val.1) (sliceRoles ends qty s place p) (by simpa only [head,neighbor] using cells.1)
    (by simpa only [head,neighbor] using cells.2) keyEq.symm

/-- The numerical low word at a nonempty full role counts every positive
spill row with its actual peer. Positive parallel rows are each counted
once, including when the full role's own chronological row has zero spill. -/
theorem spillLow_seen (full : Fin D→LocalPrefix.Columns) (q : Fin D)
    (seen : Seen ends qty s place tag m r row) (positive : (full q).width.eval m r≠0)
    (peer : ((full q).opposite.eval m r).val=(PacketNeighbor.other p).val) :
    (WideCPU.spillLow full row q).eval m r=(installedWidths ends qty p.val.1:Word W) := by
  have cells:=slice_read ends qty s place tag m r row p seen
  let emb:=sliceRoles ends qty s place p
  let val:=fun j : Fin D=>(SiteControls.weight (row j) (full q)).eval m r
  have hit (i : ChordRows ends qty p.val.1) : val (emb i)=(qty i.val:Word W) := by
    have equal : (row (emb i)).opposite.eval m r = (full q).opposite.eval m r :=
      Fin.ext ((cells.1 i).2.1.trans peer.symm)
    have amount : (row (emb i)).width.eval m r = (qty i.val : Word W) :=
      (Fin.cast_val_eq_self _).symm.trans
        (congrArg (fun x : ℕ => (x : Word W)) (cells.1 i).2.2)
    simp [val,SiteControls.weight,SiteControls.active,Expr.eval,Comparison.test,positive,equal,amount]
  have miss (j : Fin D) (absent : j∉Set.range emb) : val j=0 := by
    rcases cells.2 j absent with no|zero
    · have neq : (row j).opposite.eval m r≠(full q).opposite.eval m r:=fun eq=>no ((congrArg Fin.val eq).trans peer)
      simp [val,SiteControls.weight,SiteControls.active,Expr.eval,Comparison.test,positive,neq]
    · have z : (row j).width.eval m r=0:=Fin.ext zero
      simp [val,SiteControls.weight,SiteControls.active,Expr.eval,Comparison.test,positive,z]
  rw [WideCPU.spillLow,LocalPrefix.total_eval,←measured ends qty p.val.1]
  change (∑j,val j)=_
  calc
    _ = ∑j∈Finset.univ.map emb,val j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ outside
      apply miss j
      simpa only [Finset.mem_map,Finset.mem_univ,true_and,Set.mem_range] using outside
    _ = ∑i : ChordRows ends qty p.val.1,(qty i.val:Word W) := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl (fun i _=>hit i)
    _ = (NativeSlot.mass (key ends) qty (Fintype.equivFin (Chord S) p.val.1):Word W) := by
      rw [←Nat.cast_sum]
      apply congrArg (fun x : ℕ => (x : Word W))
      unfold NativeSlot.mass
      apply Finset.sum_bij_ne_zero (fun i _ _=>i.val)
      · simp
      · intro a _ _ b _ _ eq
        exact Subtype.ext eq
      · intro i _ nonzero
        split_ifs at nonzero with h
        · exact ⟨⟨i,Nat.pos_of_ne_zero nonzero,h⟩,Finset.mem_univ _,nonzero,rfl⟩
        · contradiction
      · intro i _ _
        simp [i.property.2]

theorem spillLow_vacant (full only : Fin D→LocalPrefix.Columns) (q : Fin D)
    (zero : (full q).width.eval m r=0) : (WideCPU.spillLow full only q).eval m r=0 := by
  simp [WideCPU.spillLow,LocalPrefix.total_eval,SiteControls.weight,SiteControls.active,Expr.eval,Comparison.test,zero]

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
