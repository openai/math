import OAI.Hierarchy.DescentContactHaloLimits
import OAI.Hierarchy.DescentContactOutputObservation

namespace OAI
/-! # Four attained receiver fields from the preceding ordered sensor pages -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w k : ℕ}
set_option quotPrecheck false
set_option hygiene false
local notation "D" => A.donor
local notation "H" => (D).hosts
local notation "J" => (D).groups
local notation "M" => (D).batch
local notation "N" => (D).lows*(2*(D).cap)
local notation "F" => DescentOldContactSender.count (D).degree (D).lows (D).cap (D).n (D).residual
local notation "b" => (D).fieldBits
local notation "C" => (D).markers donorStart A.shapes A.markerBits
local notation "S₀" => (D).sender donorStart
variable (u : DescentContactSenderDate.Prior (D).degree (D).lows (D).cap (D).n (D).residual)
variable (board : NonlinearExpanders.Graph (D).n k) (front : (D).Space donorStart u w)
variable (post : (C).endAddress≤first) (area : A.endAddress first<2^w)
variable (pack : M*max (b*8) A.markerBits≤w/2)
variable (xs : Fin H→Fin J→Fin F→Cell b) (next : Fin H→Fin (D).degree→Option (Fin H))
    (raw : Fin (D).lows→Fin (2*(D).cap)→Fin H→Fin J→Cell b)
local notation "measured" => A.rawIndicators donorStart board xs next raw
include area in
private theorem start_lt : first<2^w:=by
  obtain ⟨cut₁,cut₂,cut₃,cut₄,cut₅,cut₆⟩:=A.cuts first
  exact cut₁.trans_lt (cut₂.trans_lt (cut₃.trans_lt (cut₄.trans_lt (cut₅.trans_lt (cut₆.trans_lt area)))))

local notation "markerEnd" => post.trans_lt (start_lt A first area)
local notation "original" => (D).result donorStart A.shapes A.markerBits u board front markerEnd pack

/-- From the physically reached sender memory the two endpoint lookups share their
ordered old roster. The same memory supplies the counted mass and the receiving shape.
The final finite product decoder permits distinct old and new packing factors. -/
theorem attained_fields (early trunk : Memory w) (previous : (S₀).Before u xs next raw early)
    (stable : ∀a,a<(C).endAddress→trunk a=original early a)
    (jobs : (S₀).Packed w) (matrix : M*max (b*(C).oldFields) (C).viewBits≤w/2)
    (tailRoom : A.marker first+H*chunks J M<2^w)
    (keys : DescentResetLocalRoster.rootSlots (D).residual (2^(D).n)*(2^(D).n+2^(D).height)<2^b)
    (counter : M*max (b*(N+1)) b≤w/2) (halo : (D).degree+2<2^(D).cargoBits)
    (joint : A.shapes*2^Nat.clog 2 ((D).degree+2)≤2^A.metaBits)
    (newBatch : 0<A.batch) (newBlocks : 0<A.blocks) (oldBatch : 0<M) (groups : J=A.groups*A.blocks)
    (q : Fin A.sockets) (f : Fin 4) (x : Fin A.blocks) :
    (A.fieldExpr first x q f).Fits w (A.endAddress first) ∧
    Source (A.fieldExpr first x q f) (fun h g=>(measured q).indicators.output f h
      (Fin.cast groups.symm (finProdFinEquiv (g,x)))) A.batch (A.issuedImage donorStart first u trunk):=by
  apply A.projected_indicators donorStart first u front post area newBatch newBlocks oldBatch groups trunk measured ?_ ?_ ?_ q f x
  · intro i
    exact A.sparse_sensors donorStart first u board front markerEnd pack xs next raw early trunk previous
      jobs matrix post tailRoom keys counter halo stable i
  · intro i
    exact (A.all_fit donorStart board xs next raw keys joint i).1
  · intro i
    exact (A.all_fit donorStart board xs next raw keys joint i).2

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
