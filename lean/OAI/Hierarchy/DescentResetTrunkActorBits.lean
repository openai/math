import OAI.Hierarchy.DescentResetTrunkMarkers
import OAI.Hierarchy.DescentResetActorDirectory

namespace OAI
/-! # The actual reset actor suffices to mark geometric trunk neighbors -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentSIMDLookup DescentCommonHost
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

local notation "Z₀" => B.reset
local notation "T₀" => B.terminals
local notation "rad₀" => (Z₀).k-(T₀).commonDepth
local notation "height₀" => GroupStage.depthBound D n f g
local notation "digits₀" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "order₀" => DescentResetTrunkPalette.order (Z₀).graph rad₀ height₀
local notation "actorId" pad => (B.frame.host.symm.toEmbedding.trans input.vertex).trans (Fin.castLEEmb pad)

/-- A genuine occupied good or fall slot is filtered by the shape table. At
either trunk the measured actor bit and the census of emitting terminals agree. -/
theorem trunk_actor_bits {H D₀ b : ℕ} (pad : Fintype.card input.V≤H)
    (v : B.next.V) (hi : Block (T₀).commonDepth) :
    let named:=(Z₀).rawHostRank T₀ (actorId pad)
    let key:=(finProdFinEquiv.symm (named v)).2
    let u:=(((digits₀ hi).1,v),(digits₀ hi).2)
    (DescentResetTrunkChip.bits (Z₀).graph rad₀ height₀ D₀ key ((Z₀).sparseActor T₀ (actorId pad) (named v) hi):Cell b)=
      DescentResetTrunkChip.bits (Z₀).graph rad₀ height₀ D₀ key (if trunkTest B u then 1 else 0):=by
  intro named key u
  have idx : key=(order₀) ((Z₀).localShape T₀ v):=
    congrArg Prod.snd (Equiv.symm_apply_apply finProdFinEquiv _)
  have shapeAt : ((order₀).symm key).val=shape (Z₀).graph v.val:=by
    rw [idx,Equiv.symm_apply_apply];rfl
  have occupied:=(Z₀).sparse_known T₀ (actorId pad) v hi
  rw [occupied]
  cases kind : v.val with
  | trunk s label =>
    have yes : trunkTest B u ↔ (Z₀).emits T₀ (.trunk s label) hi:=by
      simp only [trunkTest,trunkCoordinate,u,kind]
      exact (congrArg (fun key => (Z₀).emits T₀ (.trunk s label) key) ((digits₀).symm_apply_apply hi)).to_iff
    simp only [yes]
  | good s root site =>
    have off : DescentResetTrunkChip.other (Z₀).graph rad₀ height₀ key=none:=by
      simp only [DescentResetTrunkChip.other,shapeAt,kind,shape]
    simp [DescentResetTrunkChip.bits,DescentResetTrunkChip.marker,off]
  | fall s root path =>
    have off : DescentResetTrunkChip.other (Z₀).graph rad₀ height₀ key=none:=by
      simp only [DescentResetTrunkChip.other,shapeAt,kind,shape]
    simp [DescentResetTrunkChip.bits,DescentResetTrunkChip.marker,off]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
