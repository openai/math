import OAI.Hierarchy.DescentPreparedPrimitiveRole
import OAI.Hierarchy.DescentPrimitiveBirthCases

namespace OAI
/-! # A compact root gate evaluates the rotation of its actual installed circuit -/
namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentSIMDLookup DescentHostDirectory DescentIssuedRotorRoles DescentPackedResetRotorRoles
open DescentResetGates DescentRotor DescentBaseProfile
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable (z : DescentPrimitiveBirth.Layout) {F E : Type} [Field F] [Fintype E]
variable {D cap field U h C packet u : ℕ} {positive : 0<packet}
    {board : NonlinearExpanders.Graph z.rotorBits h} {src dst : E→Fin (2^z.rotorBits)} {payment : ℝ}
    (P : BaseCircuit F board C packet u positive src dst payment)
local notation "r" => z.residual
local notation "L" => 2^r
local notation "N" => z.rotorBits
local notation "B" => z.placement
variable (f batches levelBits : ℕ) (primitive : CanonicalTag (2^N)→Cell z.rootBits)
    (inputs : Fin z.roots→Fin (r+1)→Fin (B).oldHosts→Fin ((B).groups*(B).blocks)→z.GuardPacket D cap field)
    (k : Fin (B).oldHosts→Fin ((B).groups*(B).blocks)→ℕ)
    (name : Fin U→Fin (B).sparse) (x : Fin (B).blocks) (host : Fin (B).newHosts) (group : Fin (B).groups)
    (member : host.val<U) (root : Fin z.roots) (lev : Fin (r+1))
local notation "phase" => z.observedWord packet f batches levelBits primitive inputs
local notation "v" => (B).previous (name ⟨host.val,member⟩)
local notation "g" => finProdFinEquiv (group,x)
local notation "atRoot" => inputs root lev v g
local notation "fields" => chartPart (D:=D) («L»:=L) (cap:=cap) atRoot
local notation "parts" => rootParts r N root

/-- Every data field in the statement refers to the original paid traffic and
its cap. The only chronology is the installed circuit's real layer and batch. -/
theorem rotation_raw (n : Fin z.nodes) (cls : Cell z.classBits) (paid : Cell z.paidBits)
    (spans : Fin z.arguments→Cell z.spanBits) (live : n.val<paid.val) (key : cls.val=6+root.val)
    (level : k v g=lev.val+1) (cover : (parts).2.1.val<2^lev.val)
    (observed : (flagPart (D:=D) («L»:=L) (cap:=cap) atRoot 0).val=k v g)
    (good : (flagPart (D:=D) («L»:=L) (cap:=cap) atRoot 1).val%2=0)
    (traffic : ∀i j,DescentPackedResetRotorRoles.matrix N (DescentPackedRotorMatrix.bins (L*(2*cap)))
      (DescentRotorWindowArchive.matrix r N (parts).1 (lev.val,(parts).2.1.val)
        (fun t=>fields (Fin.castSucc (DescentRotorWindowArchive.ix t)))) i j=matrixOfBundles src dst i j)
    (clock : P.layers=DescentRecordedRotorLayers.layers N packet f
      (fields (Fin.last (DescentRotorWindowArchive.count D L cap))).val)
    (levels : P.layers<2^levelBits) (layer : Fin P.layers) (batch : Fin batches)
    (number : n.val=layer.val*batches+batch.val) (inside : n.val<z.stop) :
    z.raw n cls paid spans (fun q=>z.rootActual (fun h grp=>activeDepth r (k h grp)) phase name n x q host group)=
      primitive (.inl (P.rotation layer,(parts).2.2)):=by
  refine (z.scalar_rotation n cls paid spans
    (fun q=>z.rootActual (fun h grp=>activeDepth r (k h grp)) phase name n x q host group) live root key).trans ?_
  refine (z.root_actual n (fun h grp=>activeDepth r (k h grp)) phase name x host group member root lev
    ((activeDepth_at r _ lev).mpr level)).trans ?_
  apply Fin.ext
  rw [z.digit_value n _ inside,z.observed_active packet f batches levelBits primitive inputs root lev v g cover (observed.trans level) good,number]
  exact actual P r f batches z.stop levelBits primitive (parts).1 (lev.val,(parts).2.1.val) (parts).2.2 fields
    traffic clock levels layer batch (number ▸ inside)

end
end Hierarchy.DescentPrimitiveBirth.Layout

end OAI
