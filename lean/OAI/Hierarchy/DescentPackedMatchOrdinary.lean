import OAI.Hierarchy.DescentPackedMatchInstalled
import OAI.Hierarchy.DescentPackedMatchStageReturn
import OAI.Hierarchy.DescentPackedMatchTerrain
import OAI.Hierarchy.DescentGroupPeerOrder

namespace OAI
/-! # The installed neighborhood matcher on one reached ordinary descent stage -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup DescentPackedProfileWindow ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalEpochDecoder DescentKernelHistory.BitDescription DescentSixParty.StarKeys
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2000000
theorem early_expr {r D p w H G M : ℕ} (wins : Fin r→Bank) (marked : Fin r→Fin p→Bank)
    (P : DescentPackedColony.Ports D) (base : ℕ)
    (access : ∀x,DescentPackedColony.Accessible P (wins x) H G M w base)
    (mf : ∀x i,(marked x i).Fits w base) (j : Fin («fields» r D p)) : (Gather.expr wins marked P H j).Fits w base := by
  induction j using Fin.addCases with
  | left x=>
    simp only [Gather.expr,Fin.addCases_left]
    exact ⟨(access x).source,trivial⟩
  | right j=>
    induction j using Fin.addCases with
    | left j=>
      simp only [Gather.expr,Fin.addCases_right,Fin.addCases_left]
      exact ⟨mf _ _,trivial⟩
    | right j=>
      simp only [Gather.expr,Fin.addCases_right]
      exact DescentPackedColony.peer_fits P _ base (access _) _

variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (groupKey : J↪ℕ) (vertex : V↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "rankOf" => groupRank groupKey vertex
local notation "names" => cableNames k rankOf
local notation "peers" => rotor A rankOf
local notation "r" => 2^k
local notation "K" => 2^(k+1)
local notation "p" => 2*A.cap
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank groupKey vertex))
    (fit : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "R" => M*(s).pairs
local notation "slotOf" => slot he A groups hosts hm

include coord named fit winner df in
theorem ordinary_run_observed (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (wins : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports A.degree)
    (unit base seats : ℕ) (m : Memory w)
    (large : Gather.matchUnit s short r A.degree p≤unit) (shortWord : unit*M≤w/2)
    (space : (Gather.ROM.place s short r A.degree p K H G M unit base seats).endAddr<2^w)
    (roster : DescentPackedColony.Mounted P (hostRotor hosts (DescentGroupPeerOrder.hostRoster A vertex)) m G M)
    (access : ∀x,DescentPackedColony.Accessible P (wins x) H G M w base)
    (mf : ∀x i,(marked x i).Fits w base) (mr : ∀x i,H*chunks G M≤(marked x i).size)
    (own : ∀x,DescentPackedColony.Reads (wins x) (fun h g=>(real h g).winner x) M m)
    (old : ∀x i,DescentPackedColony.Reads (marked x i) (fun h g=>(real h g).neighbor x i) M m)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : let b:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).raw
      ∀i<b.size,m (b.base+i)=((DescentPackedProfileWindow.word (s).digit R stream i).val:Word w)) :
    let l:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).layout
    let field:=Gather.expr wins marked P H
    let E:=Gather.ROM.machine s short r A.degree p A.cap K H G M unit base seats w field
    let o:=Gather.ROM.after s short r A.degree p A.cap K H G M unit base seats field m
    let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
    E.Exec m o (Gather.ROM.ticks s short r A.degree p K H G M unit base seats field) ∧
      (∀i,o (l.topology.base+i.val)=((keys i).val:Word w)) ∧
      ((∀i,(stream i).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) i) → ∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        ∃i : Fin (s).pairs,i.val=j ∧ digit (s).digit (finProdFinEquiv ((slotOf c).2,i)).val (o (l.out+(slotOf c).1.val)).val=
          DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      (∀i<base,o i=m i) ∧ CheapCode E := by
  let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
  have located:=gathered_fields A native S ready names win peers groups hosts (DescentGroupPeerOrder.hostRoster A vertex)
    (DescentGroupPeerOrder.rotor_group A groupKey vertex) wins marked P base m roster access mf mr own old
  have measured_:=measured A native S ready rankOf win he groups hosts hm coord named fit winner df profile
  have sum_eq : (∑c,countIn he A c)=Fintype.card (NativePair W.graph W.core home color A.cap) := Fintype.card_sigma.symm
  have prefixFits (i : Fin ((K*H)*chunks G M)) : PackedProfileCursor.total (ProfileTable.quota s keys) i.val≤ seats :=
    (ProfileTable.measured_prefix s keys slotOf (countIn he A) measured_ i.val i.isLt.le).trans (sum_eq.le.trans cap)
  have cpp:=A.capPos
  have rad : 0<R := by change 0<M*(r*(r*(1+A.degree*r)*(2*A.cap)));positivity
  have digitPos : 0<(s).digit := by
    change 0< max profile (Nat.clog 2 (2+entryCount r A.degree p+binCount r A.degree+(A.degree+1)*r+r*p))
    exact (Nat.clog_pos (by decide) (by omega)).trans_le (le_max_right ..)
  obtain ⟨cpu,top,issued,low,cheap⟩:=Gather.ROM.execute s A.cap unit base seats (Gather.expr wins marked P H)
    real m stream large shortWord space rad digitPos (early_expr wins marked P base access mf) located raw prefixFits
  exact ⟨cpu,top,fun pins=>original_digit A native S ready rankOf win he groups hosts hm coord named fit winner df profile
    choice stream pins _ _ issued,low,cheap⟩

include coord named fit winner df in
theorem ordinary_run (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀i,(stream i).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) i)
    (wins : Fin r→Bank) (marked : Fin r→Fin p→Bank) (P : DescentPackedColony.Ports A.degree)
    (unit base seats : ℕ) (m : Memory w)
    (large : Gather.matchUnit s short r A.degree p≤unit) (shortWord : unit*M≤w/2)
    (space : (Gather.ROM.place s short r A.degree p K H G M unit base seats).endAddr<2^w)
    (roster : DescentPackedColony.Mounted P (hostRotor hosts (DescentGroupPeerOrder.hostRoster A vertex)) m G M)
    (access : ∀x,DescentPackedColony.Accessible P (wins x) H G M w base)
    (mf : ∀x i,(marked x i).Fits w base) (mr : ∀x i,H*chunks G M≤(marked x i).size)
    (own : ∀x,DescentPackedColony.Reads (wins x) (fun h g=>(real h g).winner x) M m)
    (old : ∀x i,DescentPackedColony.Reads (marked x i) (fun h g=>(real h g).neighbor x i) M m)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats)
    (raw : let b:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).raw
      ∀i<b.size,m (b.base+i)=((DescentPackedProfileWindow.word (s).digit R stream i).val:Word w)) :
    let l:=(Gather.ROM.place s short r A.degree p K H G M unit base seats).layout
    let field:=Gather.expr wins marked P H
    let E:=Gather.ROM.machine s short r A.degree p A.cap K H G M unit base seats w field
    let o:=Gather.ROM.after s short r A.degree p A.cap K H G M unit base seats field m
    let keys:=topologyWords (M:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real))
    E.Exec m o (Gather.ROM.ticks s short r A.degree p K H G M unit base seats field) ∧
      (∀i,o (l.topology.base+i.val)=((keys i).val:Word w)) ∧
      (∀c : ScanColonies he A.stage,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
        let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
        ∃i : Fin (s).pairs,i.val=j ∧ digit (s).digit (finProdFinEquiv ((slotOf c).2,i)).val (o (l.out+(slotOf c).1.val)).val=
          DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩)) ∧
      (∀i<base,o i=m i) ∧ CheapCode E := by
  obtain ⟨cpu,top,rows,low,cost⟩:=ordinary_run_observed A native S ready groupKey vertex win he groups hosts hm coord named fit winner df profile choice stream wins marked P unit base seats m large shortWord space roster access mf mr own old cap raw
  exact ⟨cpu,top,rows pins,low,cost⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
