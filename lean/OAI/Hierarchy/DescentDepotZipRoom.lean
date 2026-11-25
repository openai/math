import OAI.Hierarchy.DescentDepotZipInstall

namespace OAI
/-! # Address and key bounds for every binary operation executed in the donor gather -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Binary
open DescentPackedZip DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {w : ℕ} (s : DepotRAM.Shape) (M unit base out : ℕ)
local notation "N" => s.blocks*(2*s.cap)
local notation "D" => s.degree+1
local notation "cb" => DescentSignedCableCodec.width s.degree s.cap
local notation "ob" => (Owners.digits s.blocks s.degree s.short*3)*s.blocks
local notation "ub" => s.short*DescentPacking.PackedMatch.Local.«fields» s.blocks s.degree (2*s.cap)
local notation "bytes" => count s*(2*2^(unit*M))
variable (large : 2*totalBits s+1≤unit) (before : base+count s*(2*2^(unit*M))≤out) (fit : out<2^w)
local notation "shelf" => bank s M unit base

private theorem shape_at (j : Kind s) :
    (shelf j).shift.bits=(gates s j).left*M ∧
    (shelf j).apply.bits=((gates s j).left+(gates s j).right)*M := by
  simp only [bank,Book.tables,menu_at, and_self]

include large before fit in
theorem binary_room (j : Kind s) {l r : Expr} (lf : l.Fits w out) (rf : r.Fits w out) :
    DescentPackedZip.Fits (shelf j) l r (gates s j).left (gates s j).right M out w := by
  obtain ⟨sroom,aroom⟩:=rooms s M unit base j out large before fit
  exact ⟨lf,rf,sroom,aroom,(shape_at s M unit base j).1,(shape_at s M unit base j).2⟩

theorem zip_expr {T : Tables} {l r : Expr} {a b : ℕ} (feasible : DescentPackedZip.Fits T l r a b M out w) :
    (T.read l r).Fits w out := ⟨feasible.apply,feasible.right,feasible.shift,feasible.left⟩

include large before fit in
theorem gather_room (f : Fields)
    (raw : f.raw.Fits w out) (signed : f.signed.Fits w out) (owner : f.owners.Fits w out)
    (ranks : f.ranks.Fits w out) (hubs : f.hub.Fits w out) (fresh : f.fresh.Fits w out) :
    FitsInputs s (joints s M unit base) f M out w := by
  have ab:=binary_room s M unit base out large before fit (.inl 0) raw signed
  have cd:=binary_room s M unit base out large before fit (.inl 1) owner ranks
  have ef:=binary_room s M unit base out large before fit (.inl 2) hubs fresh
  have left:=binary_room s M unit base out large before fit (.inl 3) (zip_expr _ _ ab) (zip_expr _ _ cd)
  have all:=binary_room s M unit base out large before fit (.inl 4) (zip_expr _ _ left) (zip_expr _ _ ef)
  exact ⟨ab,cd,ef,left,all⟩

include large before fit in
theorem cable_room (f : Fin N→Expr) (reads : ∀i,(f i).Fits w out) :
    Gather.Bounds (w:=w) (M:=M) (d:=cb) (cables s M unit base) f out := by
  intro i
  let j : Kind s:=.inr (.inl i)
  obtain ⟨sroom,aroom⟩:=rooms s M unit base j out large before fit
  exact ⟨reads i,sroom,aroom,(shape_at s M unit base j).1,(shape_at s M unit base j).2⟩

include large before fit in
theorem owner_room (f : Fin D→Expr) (reads : ∀i,(f i).Fits w out) :
    Gather.Bounds (w:=w) (M:=M) (d:=ob) (owners s M unit base) f out := by
  intro i
  let j : Kind s:=.inr (.inr (.inl i))
  obtain ⟨sroom,aroom⟩:=rooms s M unit base j out large before fit
  exact ⟨reads i,sroom,aroom,(shape_at s M unit base j).1,(shape_at s M unit base j).2⟩

include large before fit in
theorem layout_room {l r : Expr} (lf : l.Fits w out) (rf : r.Fits w out) :
    DescentPackedZip.Fits (layoutBit s M unit base) l r 1 ub M out w :=
  binary_room s M unit base out large before fit (.inr (.inr (.inr 0))) lf rf

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Binary

end OAI
