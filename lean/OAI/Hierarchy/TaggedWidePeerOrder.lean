import OAI.Hierarchy.TaggedWideDatedControls
import OAI.Hierarchy.TaggedWideDatedRows

namespace OAI
/-! # The native neighbor-prefix scan uses the same order as the signed incidence tensor -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope NamedAperture
open Tagged PassiveWindow
open scoped Classical Fin.CommRing BigOperators
variable {W S N D : ℕ} (ends : Fin N→Chord S) (qty : Fin N→ℕ) (s : Fin S)
variable (slot : (EndsAt ends qty s) ↪ Fin D) (id : Fin N→ℕ) (order : StrictMono id)

def cohort (a : (EndsAt ends qty s)) : {i : Fin N // 0<qty i ∧ key ends i=key ends a.val.val.1} ↪ Fin D where
  toFun i := slot ⟨⟨(i.val,a.val.val.2),by
    have h : ends i.val=ends a.val.val.1 := (Fintype.equivFin (Chord S)).injective i.property.2
    cases hb : a.val.val.2 <;> simpa only [hb,rowGraph,PortGraph.vertex,h] using a.val.property⟩,i.property.1⟩
  inj' i j h := Subtype.ext (congrArg (fun b : (EndsAt ends qty s)=>b.val.val.1) (slot.injective h))

include order in
theorem common_live (row : Fin D→LocalPrefix.Columns) (m : Memory W) (r : Word W)
    (_one : S≤2^W) (_bits : ∀i,qty i<2^W)
    (observed : ∀a : (EndsAt ends qty s),
      ((row (slot a)).ordinal.eval m r).val=id a.val.val.1 ∧
      ((row (slot a)).opposite.eval m r).val=(PacketNeighbor.other (byRow ends qty s a)).val ∧
      ((row (slot a)).width.eval m r).val=qty a.val.val.1)
    (blank : ∀q,q∉Set.range slot→((row q).width.eval m r).val=0) (a : (EndsAt ends qty s)) :
    (common row (slot a)).eval m r=(prefixAt ends qty a.val.val.1:Word W) := by
  let p:=byRow ends qty s a
  let emb:=cohort ends qty s slot a
  have rows (i : {j : Fin N // 0<qty j ∧ key ends j=key ends a.val.val.1}) :
      ((row (emb i)).ordinal.eval m r).val=id i.val ∧
      ((row (emb i)).opposite.eval m r).val=((row (slot a)).opposite.eval m r).val ∧
      ((row (emb i)).width.eval m r).val=qty i.val := by
    have eq : ends i.val=ends a.val.val.1 := (Fintype.equivFin (Chord S)).injective i.property.2
    let z : (EndsAt ends qty s) := ⟨⟨(i.val,a.val.val.2),by cases hb : a.val.val.2 <;> simpa only [hb,rowGraph,PortGraph.vertex,eq] using a.val.property⟩,i.property.1⟩
    have port : byRow ends qty s z=byRow ends qty s a := Subtype.ext (Prod.ext eq rfl)
    have h:=observed z
    exact ⟨h.1,h.2.1.trans ((congrArg (fun x=>(PacketNeighbor.other x).val) port).trans (observed a).2.1.symm),
      h.2.2⟩
  have blanks (j : Fin D) (missing : j∉Set.range emb) :
      ((row j).opposite.eval m r).val≠((row (slot a)).opposite.eval m r).val ∨
        ((row j).width.eval m r).val=0 := by
    by_cases hi : j∈Set.range slot
    · obtain ⟨b,rfl⟩:=hi
      left
      intro h
      have hh : PacketNeighbor.other (byRow ends qty s b)=PacketNeighbor.other (byRow ends qty s a) :=
        Fin.ext ((observed b).2.1.symm.trans (h.trans (observed a).2.1))
      have eq:=congrArg Subtype.val (PacketNeighbor.other_injective hh)
      have left : ends b.val.val.1=ends a.val.val.1:=congrArg Prod.fst eq
      have side : b.val.val.2=a.val.val.2:=congrArg (fun p : Chord S × Bool=>p.2) eq
      let i : {j : Fin N // 0<qty j ∧ key ends j=key ends a.val.val.1} :=
        ⟨b.val.val.1,b.property,congrArg (Fintype.equivFin _) left⟩
      apply missing
      refine ⟨i,congrArg slot ?_⟩
      exact Subtype.ext (Subtype.ext (Prod.ext rfl side.symm))
    · exact Or.inr (blank _ hi)
  have e:=LocalPrefix.read_sparse row (row (slot a)) m r (key ends) qty id order a.val.val.1 emb
    (observed a).1 rows blanks
  have hit : (row (slot a)).width.eval m r≠0 := by
    intro hz
    have good:=a.property
    have zero:((row (slot a)).width.eval m r).val=0 := by simp [hz]
    rw [(observed a).2.2] at zero
    omega
  simpa [common,active,Expr.eval,Comparison.test,hit,prefixAt] using e

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
