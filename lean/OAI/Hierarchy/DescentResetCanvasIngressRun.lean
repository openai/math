import OAI.Hierarchy.DescentResetCanvasInputBanks
import OAI.Hierarchy.DescentResetCanvasIngressRoster

namespace OAI
/-! # One entered state with the column, roster, flag and count words of the reset -/
namespace Hierarchy.DescentResetCanvasIngress
open DescentSixParty DescentCompiler DescentColonies DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F}
    {price ε : ℝ} {S : AtomSchedule} {k i z D wire hist H w : ℕ}
    (r : Reached W G price ε S k i z D wire hist) (wide : Fintype.card r.V≤H)
variable (io : Dated.Operands) (old M short a b base : ℕ)
local notation "A" => r.placement
local notation "L" => datedLayout r H old M short a b
local notation "nm" => DescentResetSignedTokens.venueNames r
local notation "host" => r.vertex.trans (Fin.castLEEmb wide)
local notation "gr" => Equiv.refl (Fin (S.groupCount i))
local notation "native" => r.order.trans Fin.valEmbedding
local notation "phase" => (L).phase base w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

theorem stage_front (count : Bank) (m : Memory w)
    (seen : stageVenue r wide io old a base (r.venueRoster wide) m)
    (countFit : count.Fits w base) (countRead : m count.base=(Fintype.card r.V:Word w))
    (sourceRoom : ∀(x : Block k)(j : Fin (2*(A).cap)),(io.wire x.val j.val).Fits w base ∧
      H*chunks (S.groupCount i) old≤(io.wire x.val j.val).size)
    (positive : 0<old) (oldPrecision : (A).wire*((A).z*G.b)*(A).cap<2^a)
    (newPrecision : (A).wire*((A).z*G.b)*(A).cap<2^b) (roof : (L).endAddress base<2^w) :
    let cut:=(L).endAddress base
    let out:=(phase).image m
    let rows:=H*chunks (S.groupCount i) M
    (phase).Runs m ∧ ((L).source base).Fits w cut ∧ rows≤((L).source base).size ∧
    Reads ((L).source base) (fun h g=>encode b (2^k) (fun x=>((A).censusValue host gr false h g x:Cell b))) M out ∧
    (∀t,((L).tokens base t).Fits w cut ∧ rows≤((L).tokens base t).size ∧
      Reads ((L).tokens base t) (fun (h : Fin H) g=>PackedFlow.Padded.tokens A native S r.valid gr nm short h g t) M out) ∧
    io.roster.Fits w base ∧ H*D≤ io.roster.size ∧
    (∀h:Fin H,∀j:Fin D,out (io.roster.base+(h.val*D+j.val))=
      (DescentPackedColony.target (PackedFlow.Padded.roster (D:=D) A nm wide h j):Word w)) ∧
    io.hubs.Fits w base ∧ H≤ io.hubs.size ∧ (∀v:r.V,out (io.hubs.base+(nm v).val)=(((A).hub v).toNat:Word w)) ∧
    count.Fits w base ∧ out count.base=(Fintype.card r.V:Word w) ∧
    ∀v,v<base ∨ cut≤v→ out v=m v := by
  obtain ⟨exec,weights,ports,frame⟩:=stage_issued r wide io old M short a b base (r.venueRoster wide) m
    seen sourceRoom positive oldPrecision newPrecision roof
  obtain ⟨cnt,hubs,roster⟩:=header r wide io old M short a b base count m seen countFit countRead
    (fun x j=>(sourceRoom x j).1) roof
  obtain ⟨fit,size,stored⟩:=(L).input_banks roof
  exact ⟨exec,fit,size,weights,(fun t=>⟨(stored t).1,(stored t).2,ports t⟩),
    seen.1.roster,seen.1.rosterRoom,roster,seen.2.2.2.2.1,seen.2.2.2.2.2.1,hubs,countFit,cnt,frame⟩

end
end Hierarchy.DescentResetCanvasIngress

end OAI
