import OAI.Hierarchy.DescentTerminalPreflightChipEarlier

namespace OAI
/-! # The original occupied, primitive and mask table extents in the later meter -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalCompiledPrefix DescentTerminalRowArena
open DescentTerminalVertexFields DescentTerminalPrimitiveArena
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ : ℕ)
local notation "R_" => x.channels begin_
local notation "floor_" => x.maskBase begin_

/-- Every packed family comes from a genuinely later primitive, old-actor or
old-population output band. No family aliases an earlier history vote word. -/
theorem channels_after_cohorts (f : Fin (DescentTerminalVertexFields.channels x.scalar.blocks)) :
    x.cohortEnd begin_≤((R_).bank f).base := by
  have pop : x.cohortEnd begin_≤x.population begin_ := Nat.le_add_right ..
  have actor : x.cohortEnd begin_≤x.actors begin_ := by
    change x.cohortEnd begin_≤x.population begin_+_+_+_;omega
  have prior := (x.layers begin_).1
  have released :
      x.primitive begin_≤x.scalar.«public» (x.primitive begin_) ∧
      x.primitive begin_≤x.scalar.number (x.primitive begin_) ∧
      x.primitive begin_≤x.scalar.widths (x.primitive begin_) ∧
      x.primitive begin_≤x.scalar.pointers (x.primitive begin_) := by
    simp only [DescentTerminalPrimitiveArena.Shape.widths,DescentTerminalPrimitiveArena.Shape.number,
      DescentTerminalPrimitiveArena.Shape.counting,DescentTerminalPrimitiveArena.Shape.pointers,
      DescentTerminalPrimitiveArena.Shape.«public»,DescentTerminalPrimitiveArena.Shape.rom,
      DescentTerminalPrimitiveArena.Shape.gather]
    omega
  obtain ⟨⟨b,j⟩,rfl⟩:=finProdFinEquiv.surjective f
  cases j using Fin.cases with
  | zero =>
    rw [MaskAllocation.Channels.occupied_at]
    change x.cohortEnd begin_≤x.actors begin_+_;omega
  | succ j =>
    rw [MaskAllocation.Channels.primitive_at]
    fin_cases j
    · exact (prior.trans released.1).trans (Nat.le_add_right ..)
    · exact actor.trans (Nat.le_add_right ..)
    · exact (prior.trans released.2.1).trans (Nat.le_add_right ..)
    · exact pop.trans (Nat.le_add_right ..)
    · exact (prior.trans released.2.2.1).trans (Nat.le_add_right ..)
    · exact prior.trans (Nat.le_add_right ..)
    · exact (prior.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
    · exact (prior.trans released.2.2.2).trans (Nat.le_add_right ..)

theorem channels_before_weights (f : Fin (DescentTerminalVertexFields.channels x.scalar.blocks)) :
    ((R_).bank f).base+((R_).bank f).size≤x.weights begin_ := by
  have primitive := (x.layers begin_).2.1
  obtain ⟨⟨block,col⟩,rfl⟩:=finProdFinEquiv.surjective f
  cases col using Fin.cases with
  | zero =>
    rw [MaskAllocation.Channels.occupied_at]
    exact ((x.prior begin_).actorEnd block).trans primitive
  | succ col =>
    rw [MaskAllocation.Channels.primitive_at]
    exact x.channel_end begin_ block col

theorem channels_before (f : Fin (DescentTerminalVertexFields.channels x.scalar.blocks)) :
    ((R_).bank f).base+((R_).bank f).size≤floor_ := by
  obtain ⟨_,_,a,b,c,d,e,g,h⟩:=x.layers begin_
  exact (x.channels_before_weights begin_ f).trans (by omega)

variable (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format) {w : ℕ}
local notation "C_" => AddressPlan.meter V R_ floor_
local notation "base_" => AddressPlan.afterMeter V cfg R_ floor_

theorem mask_before (room : base_<2^w) :
    (∀f,(((C_).layout.channel f).base+((C_).layout.channel f).size≤base_) ∧
      (((C_).layout.weight f).base+((C_).layout.weight f).size≤base_)) ∧
      (C_).layout.table.base+(C_).layout.table.size≤base_ := by
  have actual := MaskAllocation.room (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (p:=V.piece) (groups:=V.groups) (homes:=cfg.sites)
    R_ floor_ (x.channels_before begin_) room
  have later : (C_).base≤base_ := by change _≤(C_).base+_+_+_+3; omega
  refine ⟨fun f=>⟨((actual.old f).1.2.2).trans later,((actual.old f).2.2.2).trans later⟩,?_⟩
  let nbits := channelSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=x.scalar.blocks)
  let cap := cohortSize (q:=V.publicArity) (t:=V.roles) (H:=V.privateWords)
    (N:=V.nodes) (A:=V.addresses) (w:=V.piece) (groups:=V.groups) (blocks:=x.scalar.blocks)
  have scale : 2^(∑f,nbits f)=cap := by
    symm
    unfold cap cohortSize
    rw [Finset.prod_pow_eq_pow_sum]
  apply le_trans _ later
  change floor_+MaskAllocation.marks nbits+2^(∑f,nbits f)≤
    floor_+((∑f,2^(nbits f))+cap)
  rw [scale,MaskAllocation.marks,Nat.add_assoc]

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
