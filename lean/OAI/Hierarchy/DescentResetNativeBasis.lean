import OAI.Hierarchy.DescentPackedWalshPhysicalBasis
import OAI.Hierarchy.DescentPackedWalshGlobalWidth
import OAI.Hierarchy.DescentResetWalshPrecision
import OAI.Hierarchy.DescentIssuedCanonicalReset

namespace OAI
/-! # Measured reset basis on the exact original numbered multi-epoch chronological branch -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentIntegerScale DescentMeasuredWeights
open DescentWalshPrecision DescentPackedWalsh DescentSIMDLookup DescentBaseVariance
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F V J P : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule) (E : EstimatorArena)
variable (digits : Block E.dim≃J×Block k) (H : A.MixerHeader digits) (p f K : ℕ)
local notation "full" => A.wire*(A.z*G.b)*A.cap
local notation "depth" => H.depth A f
local notation "levels" => inputLevels (k:=E.dim) depth
local notation "domains" => DescentMeasuredWeights.Item levels (Contacts A.mutual)
local notation "siteLoad" => (fun v (z : Bits E.dim)=>A.resetLoad digits v (DescentColonies.address E.dim z))
set_option quotPrecheck false in
local notation "edgeLoad" => (fun (c : Contacts A.mutual) (z : Bits E.dim)=>A.resetFlow digits c.1 c.2.val (DescentColonies.address E.dim z))
local notation "money" => (gain levels f full K)

theorem mixer_basis_first {w i grainAge : ℕ} (loc : domains↪Fin E.hosts) (mem prior : Memory w)
    (ready : A.StateBounds S i) (positive : 0<S.height) (age : i≤S.length)
    (grain : A.z=S.grainAt G.b p grainAge) (wire : A.wire=S.epochPower^S.priceExponent) (branch : G.b≤2^S.capGain)
    (live : 0<full) (depths : ∀v,depth v≤E.dim)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (fixed : ∀a<E.start,mem a=E.literal prior a)
    (loads : Installed E.start (fun v=>shaped (fun a=>(asCube
      (padded loc (DescentMeasuredWeights.load levels siteLoad edgeLoad) (fun _=>0) v) a:Cell E.precision))) mem)
    (levelPin : ∀v,prior (E.depthRows.base+v.val)=((padded loc
      (level levels (inputDepth depth) (pairDepth A.mutual depth)) 0 v:ℕ):Word w))
    (gainPin : ∀v,prior (E.gainRows.base+v.val)=((padded loc money 0 v:ℕ):Word w))
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let μ:=H.chosenBasis A f K
    (E.cpu w).Exec mem (E.image mem) E.clock ∧
      (∀a : Fin E.dim,E.image mem (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a : Fin (2^E.dim),E.image mem (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val:Word w)) ∧
      (∀z<E.start,E.image mem z=mem z) ∧
      E.FirstTotals (padded loc (DescentMeasuredWeights.load levels siteLoad edgeLoad) (fun _=>0)) (E.image mem) := by
  obtain ⟨_,_,room,_,gains,old,products⟩:=A.original_calibration S digits ready p f K positive age grain wire branch depth
  rw [←localBits] at room products
  rw [←localGain] at gains
  have gb (v : Fin E.hosts) : padded loc money 0 v<2^E.gainBits :=
    padded_measure loc money 0 (fun a : ℕ => a < 2^E.gainBits) gains (Nat.two_pow_pos _) v
  have bounded (v : Fin E.hosts) (z : Bits E.dim) :
      padded loc (DescentMeasuredWeights.load levels siteLoad edgeLoad) (fun _=>0) v z≤full :=
    padded_measure loc (DescentMeasuredWeights.load levels siteLoad edgeLoad) (fun _=>0) (fun y=>y z≤full) (fun t=>old t z)
      (Nat.zero_le _) v
  have ords (v : Fin E.hosts) : padded loc (level levels (inputDepth depth) (pairDepth A.mutual depth)) 0 v<2^w := by
    apply padded_measure _ _ _ (·<2^w) _ (Nat.two_pow_pos _) v
    intro t
    have hx : level levels (inputDepth depth) (pairDepth A.mutual depth) t≤E.dim := by
      rcases t with ⟨v,s⟩|q
      · have bound:=s.isLt
        change s.val<E.dim-depth v+1 at bound
        change depth v+s.val≤E.dim
        have dv:=depths v
        omega
      · exact max_le (depths _) (depths _)
    omega
  have single:=padded_bill levels loc (inputDepth depth) (pairDepth A.mutual depth) siteLoad edgeLoad
    f full K gb products
  have all:=global_precision levels loc (inputDepth depth) (pairDepth A.mutual depth) siteLoad edgeLoad
    f full K gb products
  exact E.from_counts_first levels loc (inputDepth depth) (pairDepth A.mutual depth) siteLoad edgeLoad
    f full K (2^f*full) (E.precision+Nat.clog 2 E.hosts) full mem prior fit gb bounded room ords stage small
    (by omega) (fun j _=>single j) fixed loads levelPin gainPin issue (Nat.mul_pos (Nat.two_pow_pos _) live) score all


theorem mixer_basis {w i grainAge : ℕ} (loc : domains↪Fin E.hosts) (mem prior : Memory w)
    (ready : A.StateBounds S i) (positive : 0<S.height) (age : i≤S.length)
    (grain : A.z=S.grainAt G.b p grainAge) (wire : A.wire=S.epochPower^S.priceExponent) (branch : G.b≤2^S.capGain)
    (live : 0<full) (depths : ∀v,depth v≤E.dim)
    (localBits : E.precision=S.localWalshBits p E.dim f K)
    (localGain : E.gainBits=gainBits E.dim f K (S.censusBits p))
    (fit : E.Fits w) (stage : E.dim+1≤2^w) (small : E.payload≤w)
    (score : 3*E.dim+(E.precision+Nat.clog 2 E.hosts)+2≤w)
    (fixed : ∀a<E.start,mem a=E.literal prior a)
    (loads : Installed E.start (fun v=>shaped (fun a=>(asCube
      (padded loc (DescentMeasuredWeights.load levels siteLoad edgeLoad) (fun _=>0) v) a:Cell E.precision))) mem)
    (levelPin : ∀v,prior (E.depthRows.base+v.val)=((padded loc
      (level levels (inputDepth depth) (pairDepth A.mutual depth)) 0 v:ℕ):Word w))
    (gainPin : ∀v,prior (E.gainRows.base+v.val)=((padded loc money 0 v:ℕ):Word w))
    (issue : PhysicalTrajectory.Room w E.dim E.solveAt E.bank) :
    let μ:=H.chosenBasis A f K
    (E.cpu w).Exec mem (E.image mem) E.clock ∧
      (∀a : Fin E.dim,E.image mem (PhysicalTrajectory.pointer E.dim E.solveAt a.val)=
        ((rowIndex E.dim (rowFunctional μ a)).val:Word w)) ∧
      (∀a : Fin (2^E.dim),E.image mem (PhysicalTrajectory.outputBase E.dim E.solveAt+a.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm a))).val:Word w)) ∧
      ∀z<E.start,E.image mem z=mem z := by
  obtain ⟨ran,rows,table,frame,_⟩:=A.mixer_basis_first S E digits H p f K loc mem prior ready positive age grain wire
    branch live depths localBits localGain fit stage small score fixed loads levelPin gainPin issue
  exact ⟨ran,rows,table,frame⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
