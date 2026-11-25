import OAI.Computability.BorderVNP.CellDirectoryMerge

/-! # Separate scalar bounds for local wire addresses and global gadget identifiers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- The original factor's gadget IDs are compared as binary words. -/
def Factor.IDBound (f : Factor) (U : ℕ) : Prop :=
  match f with
  | .gadget _ ids => ∀ i ∈ ids, i ≤ U
  | _ => True

theorem Packet.factorFields_iff (f : Factor) (U : ℕ) :
    Packet.FactorFields f U ↔ f.FieldBound U ∧ f.IDBound U := Iff.rfl

theorem Factor.FieldBound.mono {f : Factor} {V U : ℕ} (hf : f.FieldBound V) (h : V ≤ U) :
    f.FieldBound U := by
  cases f with
  | truth ws rs | sign ws rs | gadget ws rs =>
    obtain ⟨⟨a,b⟩,c⟩ := hf
    exact ⟨⟨a.trans h,b.trans h⟩,fun i hi => (c i hi).trans h⟩
  | unary w p => obtain ⟨_,a,b,c,d⟩ := hf; exact ⟨trivial,a.trans h,b.trans h,c.trans h,d.trans h⟩

theorem Factor.IDBound.mono {f : Factor} {V U : ℕ} (hf : f.IDBound V) (h : V ≤ U) : f.IDBound U := by
  cases f with
  | gadget ws ids => exact fun i hi => (hf i hi).trans h
  | _ => trivial

private theorem port_mono {p : Port} {V U : ℕ} (a : Profile.PortBound V p) (h : V ≤ U) :
    Profile.PortBound U p := ⟨a.1.trans h,a.2.1.trans h,a.2.2.trans h⟩

theorem Record.GuardBound.mono {r : Record} {V U : ℕ} (hr : r.GuardBound V) (h : V ≤ U) : r.GuardBound U := by
  cases r with
  | box => trivial
  | zero => exact ⟨hr.1.trans h,hr.2.1.trans h,port_mono hr.2.2 h⟩
  | equal => exact ⟨hr.1.trans h,hr.2.1.trans h,port_mono hr.2.2.1 h,port_mono hr.2.2.2 h⟩
  | profile =>
    obtain ⟨c,w,hist,rs,s,hroute⟩ := hr
    refine ⟨c.trans h,w.trans h,hist.trans h,rs.trans h,port_mono s h,fun r hmem => ?_⟩
    obtain ⟨t,l,a,b⟩ := hroute r hmem
    exact ⟨t.trans h,l.trans h,port_mono a h,port_mono b h⟩

theorem Packet.RecordFields.mono {r : Record} {V U : ℕ} (hr : Packet.RecordFields r V) (h : V ≤ U) :
    Packet.RecordFields r U := by
  refine ⟨hr.1.mono h,?_⟩
  cases r with
  | box => obtain ⟨a,b,c,d⟩ := hr.2; exact ⟨a.trans h,b.trans h,c.trans h,d.trans h⟩
  | profile => exact fun i hi => (hr.2 i hi).trans h
  | _ => trivial

end CellSparse

end BorderVNP
end Computability
end OAI
