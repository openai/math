import OAI.Hierarchy.ProtocolRAMRouteSettlement

namespace OAI
/-! # Mounting the two core/catalyst occurrence directories in the public header -/

namespace Hierarchy.ProtocolRAM.RouteSettlement
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

variable {w r edges : ℕ} {I C : Type*} [Fintype I] [Fintype C]
variable {core : I → List (Fin edges)} {center : C → List (Fin edges)}

/-- The addresses and resource indices depend on the prescribed walks only. Neither
column contains any final stock amount, selected width, or computed cash information. -/
def directoryWord (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (kind : Bool) (row : ℕ) : ℕ :=
  if h : row/2< r then
    let o := enum ⟨row/2,h⟩
    if row%2=0 then (if kind then 0 else o.edge.val)
    else (if kind then oddKind o else resource ci cj o)
  else 0

def mount (b : Banks) (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (m : Memory w) : Memory w :=
  fillSegment b.index.base (2*r) (fun a => (directoryWord enum ci cj false (a-b.index.base):Word w))
    (fillSegment b.kind.base (2*r) (fun a => (directoryWord enum ci cj true (a-b.kind.base):Word w)) m)

omit [Fintype I] [Fintype C] in
theorem directoryWord_even (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (kind : Bool) (i : Fin r) : directoryWord enum ci cj kind (2*i.val) =
      if kind then 0 else (enum i).edge.val := by
  have div : 2*i.val/2=i.val := by omega
  simp [directoryWord,div,i.isLt]

omit [Fintype I] [Fintype C] in
theorem directoryWord_odd (enum : Fin r ≃ RouteOccurrence core center) (ci : I → ℕ) (cj : C → ℕ)
    (kind : Bool) (i : Fin r) : directoryWord enum ci cj kind (2*i.val+1) =
      if kind then oddKind (enum i) else resource ci cj (enum i) := by
  have div : (2*i.val+1)/2=i.val := by omega
  have odd : (2*i.val+1)%2=1 := by omega
  simp [directoryWord,div,odd,i.isLt]

omit [Fintype I] [Fintype C] in
theorem mount_directory (b : Banks) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (m : Memory w) (room : 2*r≤2^w)
    (kFit : 2*r≤b.kind.size) (iFit : 2*r≤b.index.size) (apart : b.kind.base+2*r≤b.index.base) :
    Directory b (mount b enum ci cj m) enum ci cj := by
  have readK (k : ℕ) (hk : k<2*r) : b.kind.read (mount b enum ci cj m) (k:Word w)=
      (directoryWord enum ci cj true k:Word w) := by
    simp [Bank.read,Fin.val_cast_of_lt (hk.trans_le room),Nat.mod_eq_of_lt (hk.trans_le kFit),
      mount,fillSegment,show ¬(b.index.base≤b.kind.base+k ∧ b.kind.base+k<b.index.base+2*r) by omega,
      show b.kind.base≤b.kind.base+k ∧ b.kind.base+k<b.kind.base+2*r by omega]
  have readI (k : ℕ) (hk : k<2*r) : b.index.read (mount b enum ci cj m) (k:Word w)=
      (directoryWord enum ci cj false k:Word w) := by
    simp [Bank.read,Fin.val_cast_of_lt (hk.trans_le room),Nat.mod_eq_of_lt (hk.trans_le iFit),
      mount,fillSegment,show b.index.base≤b.index.base+k ∧ b.index.base+k<b.index.base+2*r by omega]
  constructor
  · intro i
    simpa [directoryWord_even] using readK (2*i.val) (by have := i.isLt; omega)
  · intro i
    simpa [directoryWord_even] using readI (2*i.val) (by have := i.isLt; omega)
  · intro i
    simpa [directoryWord_odd] using readK (2*i.val+1) (by have := i.isLt; omega)
  · intro i
    simpa [directoryWord_odd] using readI (2*i.val+1) (by have := i.isLt; omega)

omit [Fintype I] [Fintype C] in
theorem mount_frame (b : Banks) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (m : Memory w) (a : ℕ)
    (safeKind : a<b.kind.base ∨ b.kind.base+2*r≤a) (safeIndex : a<b.index.base ∨ b.index.base+2*r≤a) :
    mount b enum ci cj m a=m a := by
  simp [mount,fillSegment,show ¬(b.kind.base≤a ∧ a<b.kind.base+2*r) by omega,
    show ¬(b.index.base≤a ∧ a<b.index.base+2*r) by omega]

omit [Fintype I] [Fintype C] in
/-- Earlier core and purchase passes can initialize all other words independently. -/
theorem Directory.transport (b : Banks) (m m' : Memory w) (enum : Fin r ≃ RouteOccurrence core center)
    (ci : I → ℕ) (cj : C → ℕ) (dir : Directory b m enum ci cj)
    (sameKind : ∀ x,b.kind.read m' x=b.kind.read m x)
    (sameIndex : ∀ x,b.index.read m' x=b.index.read m x) : Directory b m' enum ci cj :=
  ⟨fun i => (sameKind _).trans (dir.headKind i),fun i => (sameIndex _).trans (dir.headIndex i),
   fun i => (sameKind _).trans (dir.tailKind i),fun i => (sameIndex _).trans (dir.tailIndex i)⟩

end
end Hierarchy.ProtocolRAM.RouteSettlement

end OAI
