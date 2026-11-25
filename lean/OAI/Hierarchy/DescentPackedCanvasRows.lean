import OAI.Hierarchy.DescentPackedResetRectangle
import OAI.Hierarchy.DescentPaddedEstimatorRows

namespace OAI
/-! # Readout ABI for measured reset inputs on a fixed public host and port canvas -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentPackedWalsh DescentWalshPhysical
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H u l b w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
local notation "m" => u+l
local notation "dep" => GroupStage.MixerHeader.depth A (A.mixerHeader digits name)
local notation "lev" => inputLevels (k:=m)
local notation "contacts" => Contacts A.mutual
local notation "measure" => (fun v z=>A.resetLoad digits v (address m z))
local notation "traffic" => (fun c : contacts=>fun z=>A.resetFlow digits (Sigma.fst c) (Subtype.val (Sigma.snd c)) (address m z))

structure Loaded {N : ℕ} (f K : ℕ) (loc : Item (lev (dep f)) contacts ↪ Fin N) (depthBase gainBase out : ℕ)
    (dst : Memory w) : Prop where
  input : Installed out (fun i=>shaped (u:=u) (l:=l) (fun z=>(padded loc (load (lev (dep f)) measure traffic) (fun _=>0) i
    ((DescentWalshPhysical.coordinates (u+l)).symm z):Cell b))) dst
  levels (i : Fin N) : dst (depthBase+i.val)=(padded (α:=ℕ) loc (level (lev (dep f)) (inputDepth (dep f))
    (pairDepth A.mutual (dep f))) 0 i:Word w)
  gains (i : Fin N) : dst (gainBase+i.val)=(padded (α:=ℕ) loc (gain (lev (dep f)) f (A.wire*(A.z*G.b)*A.cap) K) 0 i:Word w)

def loc {HP D : ℕ} (f : ℕ) (hosts : H≤HP) (ports:A.degree≤D) :
    Item (lev (dep f)) contacts ↪ Fin (HP*(m+1+D)) :=
  publicRectangle name (lev (dep f)) (fun v=>by unfold inputLevels;omega)
    (atPort name A.mutual (fun v=>(Finset.card_filter_le ..).trans (A.degreeBound v))) hosts ports

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
