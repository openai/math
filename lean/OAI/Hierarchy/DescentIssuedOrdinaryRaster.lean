import OAI.Hierarchy.DescentOrdinaryRasterRun
import OAI.Hierarchy.DescentPaddedRasterValue
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # Reading both true padded host rasters from the original relative-location and payment rows -/
namespace Hierarchy.DescentOrdinaryRasterReturn
open DescentSIMDLookup DescentVenueQuantityPlanes DescentScalarBookReshape DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable (d:Dims)(B:Sources)(base:ℕ)
local notation "Q" => d.shapes
local notation "H" => d.oldHosts
local notation "R" => d.hosts
local notation "G" => d.groups
local notation "X" => d.blocks
local notation "oldG" => G*X
local notation "s" => chunks G d.lanes
local notation "s₀" => chunks oldG d.oldLanes

theorem issued {old w:ℕ}(m:Memory w)(oldFit:old≤H)(newFit:old*Q≤R)
    (space:Room d B base (old*Q) w)(m₀:0<d.oldLanes)(m₁:0<d.lanes)(blocks:0<X)
    (hosts:0<R)(chunksPos:0<s)
    (paid:Fin Q→Fin old→Fin oldG→Cell d.precision)(alive:Fin Q→Fin old→Fin oldG→Cell 1)
    (funded:∀q(u:Row H oldG d.oldLanes),m (B.paid.base+q.val*(H*s₀)+(row H oldG d.oldLanes u).val)=
      ((data (extend (paid q)) u).val:Word w))
    (actors:∀q(u:Row H oldG d.oldLanes),m (B.alive.base+q.val*(H*s₀)+(row H oldG d.oldLanes u).val)=
      ((data (extend (alive q)) u).val:Word w))
    (count:m B.count.base=((old*Q:ℕ):Word w))
    (earlyFund:B.paid.base+Q*(H*s₀)≤base)(earlyActor:B.alive.base+Q*(H*s₀)≤base)(earlyCount:B.count.base<base):
    let out:=(phase d B base w).image m
    (∀x(u:Row R G d.lanes),out ((paidBank d base x.val).base+(row R G d.lanes u).val)=
      ((data (extend (fun v=>book paid x v)) u).val:Word w)) ∧
    (∀x(u:Row R G d.lanes),out ((actorBank d base x.val).base+(row R G d.lanes u).val)=
      ((data (extend (fun v=>book alive x v)) u).val:Word w)):=by
  let ids:=identityColumn d base w
  let load:=DescentVenueQuantityPlanes.phase d (fund d B base) w
  let bits:=DescentVenueQuantityPlanes.phase (actor d) (seen d B base) w
  let idm:=ids.image m
  let pm:=load.image idm
  have below (a:ℕ)(h:a<base):idm a=m a:=DescentStaticWordColumn.frame _ _ _ _ _ (.inl h)
  have before (a:ℕ)(h:a<first d base):pm a=idm a:=
    (DescentVenueQuantityPlanes.any d (fund d B base) idm space.firstFit).2 a (.inl h)
  have lower:base+R≤first d base:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
  have inv (j:Fin (old*Q)):idm ((inverse d base).base+j.val)=((widen oldFit j).val:Word w):=
    DescentStaticWordColumn.read base R id m (j.isLt.trans_le newFit)
  have num:idm B.count.base=((old*Q:ℕ):Word w):=(below _ earlyCount).trans count
  have fp (q:Fin Q)(u:Row H oldG d.oldLanes):
      B.paid.base+q.val*(H*s₀)+(row H oldG d.oldLanes u).val<base:=by
    have r:=(row H oldG d.oldLanes u).isLt
    have sz:=(Nat.mul_le_mul_right (H*s₀) q.isLt);rw [Nat.succ_mul] at sz;omega
  have fa (q:Fin Q)(u:Row H oldG d.oldLanes):
      B.alive.base+q.val*(H*s₀)+(row H oldG d.oldLanes u).val<base:=by
    have r:=(row H oldG d.oldLanes u).isLt
    have sz:=(Nat.mul_le_mul_right (H*s₀) q.isLt);rw [Nat.succ_mul] at sz;omega
  obtain ⟨pay,hp,readP,_⟩:=DescentVenueQuantityPlanes.run d (fund d B base) (widen oldFit)
    (fun q=>extend (paid q)) idm space.firstFit m₀ m₁ blocks hosts chunksPos
    (fun q u=>(below _ (fp q u)).trans (funded q u)) num inv
  have hp₀:pay=pm:=ProtocolRAM.exec_unique _ idm _ _ hp
    (DescentVenueQuantityPlanes.any d (fund d B base) idm space.firstFit).1
  subst pay
  have baseFirst : base ≤ first d base := (Nat.le_add_right base R).trans lower
  obtain ⟨act,ha,readA,_⟩:=DescentVenueQuantityPlanes.run (actor d) (seen d B base) (widen oldFit)
    (fun q=>extend (alive q)) pm space.secondFit m₀ m₁ blocks hosts chunksPos
    (fun q u=>(before _ ((fa q u).trans_le baseFirst)).trans
      ((below _ (fa q u)).trans (actors q u)))
    ((before B.count.base (earlyCount.trans_le baseFirst)).trans num)
    (fun j=>(before (base+j.val) ((Nat.add_lt_add_left (j.isLt.trans_le newFit) base).trans_le lower)).trans (inv j))
  have ha₀:act=bits.image pm:=ProtocolRAM.exec_unique _ pm _ _ ha (DescentVenueQuantityPlanes.any (actor d) (seen d B base) pm space.secondFit).1
  subst act
  constructor
  · intro x u
    have r : (row R G d.lanes u).val < R*s := (row R G d.lanes u).isLt
    have bound:=Nat.mul_le_mul_right (R*s) x.isLt
    rw [Nat.succ_mul] at bound
    have outSize:(fund d B base).out+X*(R*s) ≤ second d base:=Nat.add_le_add_left (Nat.le_pow_clog (by decide) _) _
    have below₂:(paidBank d base x.val).base+(row R G d.lanes u).val<second d base:=by
      change (fund d B base).out+x.val*(R*s)+(row R G d.lanes u).val < second d base
      omega
    exact ((DescentVenueQuantityPlanes.any (actor d) (seen d B base) pm space.secondFit).2 _ (.inl below₂)).trans
      ((readP x u).trans (congrArg (fun f : Fin R → Fin G → Cell d.precision => ((data f u).val : Word w))
        (funext fun h => funext fun g => padded_value (m₀:=d.oldLanes) (m₁:=d.lanes) paid oldFit x h g)))
  · intro x u
    exact (readA x u).trans (congrArg (fun f : Fin R → Fin G → Cell 1 => ((data f u).val : Word w))
      (funext fun h => funext fun g => padded_value (m₀:=d.oldLanes) (m₁:=d.lanes) alive oldFit x h g))

end
end Hierarchy.DescentOrdinaryRasterReturn

end OAI
