import OAI.Hierarchy.DescentResetCanvasIngress
import OAI.Hierarchy.DescentResetCanvasAmountRead
import OAI.Hierarchy.DescentResetSignedTokenVenue
import OAI.Hierarchy.DescentCanvasIngressValue

namespace OAI
/-! # The reached predecessor supplies the full measured reset canvas -/
namespace Hierarchy.DescentResetCanvasIngress
open DescentSixParty DescentCompiler DescentColonies DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
variable {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs}
  {G : PoweredGadget F} {price ε : ℝ} {S : AtomSchedule} {k i z D wire hist H w : ℕ}
  (r : Reached W G price ε S k i z D wire hist) (wide : Fintype.card r.V≤H)

def datedLayout (H old M short a b : ℕ) : Layout :=
  ⟨DescentResetSignedTokens.datedLayout r.placement H (S.groupCount i) old M short,
    a,b,r.placement.hist,r.placement.wire*(r.placement.z*G.b)⟩
variable (io : Dated.Operands) (old M short a b : ℕ)
local notation "A" => r.placement
local notation "L" => datedLayout r H old M short a b
local notation "gr" => (Equiv.refl (Fin (S.groupCount i)))
local notation "host" => (r.vertex.trans (Fin.castLEEmb wide))
local notation "nat_" => r.order.trans Fin.valEmbedding
local notation "atom_" => (fun x : Block k=>io.atoms x.val)
local notation "ports_" => (fun t : Block k×Fin (2*(A).cap)=>io.wire t.1.val t.2.val)

private theorem retain {H N t M w floor : ℕ} {m m' : Memory w} {B : Bank}
    {val : Fin H→Fin N→Cell t} (fit : B.Fits w floor) (size : H*chunks N M≤B.size)
    (low : ∀a,a<floor→m' a=m a) (read : Reads B val M m) : Reads B val M m' := by
  intro p
  exact (low _ ((Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le size) _).trans_le fit.2.2)).trans (read p)

theorem stage_issued (base : ℕ) (rs : Fin H→Fin D→Option (Fin H)) (m : Memory w)
    (seen : stageVenue r wide io old a base rs m)
    (sourceRoom : ∀(x:Block k) (j:Fin (2*(A).cap)),(io.wire x.val j.val).Fits w base ∧ H*chunks (S.groupCount i) old≤(io.wire x.val j.val).size)
    (positive : 0<old) (oldPrecision : (A).wire*((A).z*G.b)*(A).cap<2^a)
    (newPrecision : (A).wire*((A).z*G.b)*(A).cap<2^b) (roof : (L).endAddress base<2^w) :
    let phase:=(L).phase base w io.hubs atom_ ports_
    phase.Runs m ∧
    Reads ((L).source base) (fun h g=>encode b (2^k) (fun x=>((A).censusValue host gr false h g x:Cell b))) M (phase.image m) ∧
    (∀t,Reads ((L).tokens base t)
      (fun (h : Fin H) g=>PackedFlow.Padded.tokens A nat_ S r.valid gr (DescentResetSignedTokens.venueNames r) short h g t)
      M (phase.image m)) ∧
    ∀v,v<base ∨ (L).endAddress base≤v→phase.image m v=m v := by
  classical
  have recorded:=seen
  obtain ⟨_,_,_,_,hubFit,hubSize,hubWords,atomFit,atomWords⟩:=seen
  have wires (j:(L).signed.Slot) := (sourceRoom j.1 j.2).1
  obtain ⟨before,afterS,afterA⟩:=(L).order base
  let s:=(L).signed
  let c:=(L).collector
  let se:=(L).signedEnd base
  let ae:=(L).atomEnd base
  let first:=(s.phase base w ports_).image m
  let second:=DescentVenueSlabs.ExprInputs.image (L).amounts atom_ se first
  have ar : ae<2^w:=afterA.trans_lt roof
  have sr : se<2^w:=afterS.trans_lt ar
  have run := (L).any base io.hubs atom_ ports_ m hubFit (fun x=>atomFit x.val) wires roof
  have keep1 := (s.any base ports_ m wires sr).2
  have allSigned := (DescentResetSignedTokens.stage_issued r wide io old M short base a base rs m
    recorded (fun x j=>(sourceRoom x j).1) (fun x j=>(sourceRoom x j).2) positive sr).2
  have atomsBefore (x:Block k) : (io.atoms x.val).Fits w se :=
    ProtocolRAMGeneratedWrite.fits_mono _ before (atomFit x.val)
  have sameAtoms (x:Block k) : Source (io.atoms x.val) (fun h g=>Census.count A gr host a h g x) old first := by
    intro p
    exact (ProtocolRAM.eval_below _ _ _ _ (atomFit x.val) (fun j hj=>keep1 j (.inl hj))).trans (atomWords x p)
  obtain ⟨_,amountRead,keep2⟩:=DescentVenueSlabs.ExprInputs.issued (L).amounts atom_ se first
    (fun x h g=>Census.count A gr host a h g x) atomsBefore sameAtoms positive ar
  have layoutRoom:=s.room sr
  have rawFits (t : s.Slot) : (s.raw base t).Fits w se := by
    have h:=(layoutRoom.2.1 t).1
    have bound : (s.dictionary base).base ≤ se := by
      change (s.dictionary base).base ≤ (s.dictionary base).base + (s.dictionary base).size + s.slots*s.rows + 2^Nat.clog 2 s.rows
      exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
    exact ⟨h.1,h.2.1,h.2.2.trans bound⟩
  have wireFits (t:s.Slot) : (s.raw base t).Fits w ae :=
    ⟨(rawFits t).1,(rawFits t).2.1,(rawFits t).2.2.trans afterS⟩
  have tokenFits(t:s.Slot) : (s.bank base t).Fits w ae :=
    ⟨(layoutRoom.2.2 t).1.1,(layoutRoom.2.2 t).1.2.1,(layoutRoom.2.2 t).1.2.2.trans afterS⟩
  have atomBankFit (x:Block k) := DescentVenueSlabs.page_room (L).amounts se w x ar
  have headKeep (j:ℕ) (hj:j<base) : second j=m j := (keep2 j (.inl (hj.trans_le before))).trans (keep1 j (.inl hj))
  let af:=fun x:Block k=>(atomBankFit x).1
  have hf : io.hubs.Fits w ae:= ⟨hubFit.1,hubFit.2.1,hubFit.2.2.trans (before.trans afterS)⟩
  let actual:=fun (p:s.Slot) h g=>DescentSignedCableCodec.encode (Prepare.signed A nat_ S r.valid (gr).toEmbedding host p.1 p.2 h g)
  have wireRead (t:s.Slot) : Reads (s.raw base t) (actual t) M second :=
    retain (rawFits t) (layoutRoom.2.1 t).2 (fun j hj=>keep2 j (.inl hj)) (allSigned t).1
  have observed:= c.issued (Census.hub A host) (fun x h g=>Census.count A gr host a h g x) actual
    ae io.hubs ((L).atomBank base) (s.raw base) second hf hubSize
    (fun h=>(headKeep _ ((Nat.add_lt_add_left (h.isLt.trans_le hubSize) _).trans_le hubFit.2.2)).trans (hubWords h))
    af (fun x=>(atomBankFit x).2) amountRead wireFits (fun t=>(layoutRoom.2.1 t).2) wireRead
    (fun x h g=>((A).censusValue host gr false h g x : Cell b)) (by
      intro x h g
      refine Eq.trans ?_ ((A).census_nat S host gr r.valid newPrecision false h g x).symm
      unfold DescentResetCanvasAmount.Layout.fee
      refine Eq.trans ?_ (Census.canvas_value A nat_ S r.valid gr host oldPrecision h g x).symm
      refine congrArg (fun y : ℕ => c.hist*(Census.count A gr host a h g x).val +
        c.unitFee*(if (Census.hub A host h).val=0 then 1 else 256)*y) ?_
      exact Finset.sum_congr rfl (fun j _ => c.alive_eq (actual (x, j) h g))) roof
  have keep3:=(c.any ae io.hubs ((L).atomBank base) (s.raw base) second hf af wireFits roof).2
  refine ⟨run.1,observed,?_,run.2⟩
  intro t
  exact retain (tokenFits t) (layoutRoom.2.2 t).2 (fun j hj=>keep3 j (.inl hj))
    (retain (layoutRoom.2.2 t).1 (layoutRoom.2.2 t).2 (fun j hj=>keep2 j (.inl hj)) (allSigned t).2)

end
end Hierarchy.DescentResetCanvasIngress

end OAI
