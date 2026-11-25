import OAI.Hierarchy.TaggedWideRoleScatter

namespace OAI
/-! # Localizing the actual selected ballot and all its histogram counters -/

noncomputable section
namespace Hierarchy.ProtocolRAM.SiteScatter
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

variable {W n sites columns : ℕ} {I : Type} (place : I ↪ Fin sites)
  (word : I → Fin columns → Word W)

def participant : I×Fin columns ↪ Fin sites×Fin columns :=
  place.prodMap (Function.Embedding.refl _)

def pos (s : Fin sites) (c : Fin columns) : Fin (sites*columns) := finProdFinEquiv (s,c)

def table : Fin sites → Fin columns → Word W := fun s c=>
  (RoleWidths.shelf (participant place) finProdFinEquiv.toEmbedding
    (fun p=>(word p.1 p.2).val) (pos s c):Word W)

theorem active (i : I) (c : Fin columns) : table place word (place i) c=word i c := by
  let emitted:=fun p : I×Fin columns=>(word p.1 p.2).val
  have read:=RoleWidths.shelf_live (participant place) finProdFinEquiv.toEmbedding emitted (i,c)
  exact (congrArg (fun z:ℕ=>(z:Word W)) read).trans (Fin.cast_val_eq_self (word i c))

theorem idle (s : Fin sites) (c : Fin columns) (vacant : s∉Set.range place) :
    table place word s c=0 := by
  let emitted:=fun p : I×Fin columns=>(word p.1 p.2).val
  have absent : (s,c)∉Set.range (participant place) := by
    rintro ⟨⟨i,j⟩,hit⟩
    exact vacant ⟨i,congrArg Prod.fst hit⟩
  exact congrArg (fun z:ℕ=>(z:Word W))
    (RoleWidths.shelf_blank (participant place) finProdFinEquiv.toEmbedding emitted (s,c) absent)

/-- One genuine word-RAM scatter for the selected party flag, local
party and packet tags, root, and all finite native histogram columns.
Every signed site subsequently reads these at fixed site-local addresses.
An inactive slot can have an arbitrary hidden site word. -/
theorem run (base scratch sink : ℕ) (stored index : Expr) (m : Memory W)
    (source : Fin n → Option (I×Fin columns))
    (covers : ∀i c,∃j,source j=some (i,c))
    (valueFits : stored.Fits W base) (addrFits : (RoleWidths.destination base sink stored index).Fits W base)
    (space : base+sites*columns ≤ scratch) (room : scratch+n+n<2^W) (low : sink<base)
    (read : ∀j,stored.eval m (j.val:Word W)=(source j).elim 0 (fun p=>word p.1 p.2))
    (address : ∀j i c,source j=some (i,c)→0<(word i c).val→
      index.eval m (j.val:Word W)=((pos (place i) c).val:Word W)) :
    let dst := RoleWidths.destination base sink stored index
    ∃ out,(ProtocolRAMTurnReplay.program W base (sites*columns) scratch n dst stored).Exec m out
        (ProtocolRAMTurnReplay.work (sites*columns) n dst stored) ∧
      (∀s c,out (base+(pos s c).val)=table place word s c) ∧
      ∀t,(t<base ∨ base+sites*columns ≤ t) → (t<scratch ∨ scratch+n+n ≤ t) → t≠sink → out t=m t := by
  intro dst
  have sourceRead (j : Fin n) : stored.eval m (j.val:Word W)=
      ((source j).elim 0 (fun p=>(word p.1 p.2).val):ℕ) := by
    rw [read]
    cases source j <;> simp
  obtain ⟨out,run,each,frame⟩ := RoleWidths.run (participant place) finProdFinEquiv.toEmbedding
    (fun p=>(word p.1 p.2).val) base scratch sink stored index m source
    (fun ⟨i,c⟩ _=>covers i c) (fun p=>(word p.1 p.2).isLt) valueFits addrFits space room low sourceRead
    (fun j ⟨i,c⟩=>address j i c)
  exact ⟨out,run,fun s c=>each (s,c),frame⟩

end Hierarchy.ProtocolRAM.SiteScatter

end
end OAI
