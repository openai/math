import OAI.Hierarchy.DescentResetFieldReceipt
import OAI.Hierarchy.DescentResetWindowRankInput
import OAI.Hierarchy.DescentResetWindowRanksRAM

namespace OAI
/-! # The local streaming prefix uses only the physical header and returned original-source ticket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "board" => Stage.source A ord
local notation "fit" => Stage.measured A ord S B.next.valid
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
open DescentResetWindowResidentSources DescentResetFieldAssembler
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentPackedColony DescentSIMDLookup DescentPackedZip
local notation "K" => totalLocal B
local notation "FN" => fieldNames B
local notation "position_" => sumAt B FN (localRoster B)
variable {H b : ℕ} (rack : Fin H→Option B.next.V)
local notation "X" => 2^k
local notation "gg" => S.groupCount (i+1)

def actualTicket (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin gg) : ℕ :=
  (rack v).elim 0 (fun r=>(localOrigin B ((g,r),x) j).elim 0
    (fun e=>(sourceTicket B e.val e.property.1).val))

def actualParent (x : Fin X) (j : Fin K) (v : Fin H) (g : Fin gg) : Option Parent :=
  (rack v).bind (fun r=>shortRow B FN (localRoster B) ((g,r),x) j)

theorem actual_parent (x j v g) :
    RankInput.parent (actualMeta B rack x j v g) (actualTicket B rack x j v g)=actualParent B rack x j v g := by
  cases hv:rack v with
  | none=>simp [actualMeta,actualParent,hv,RankInput.parent,Meta.blank]
  | some r=>
    let u : Host:=((g,r),x)
    change RankInput.parent ((rack v).elim _ _) ((rack v).elim _ _)=((rack v).bind _)
    rw [hv]
    change RankInput.parent («meta» B u (localOrigin B u j))
      ((localOrigin B u j).elim 0 (fun e=>(sourceTicket B e.val e.property.1).val))=
      (localOrigin B u j).map (shortParent B FN u)
    cases he:localOrigin B u j with
    | none=>rfl
    | some e=>
      change some ⟨peer («meta» B u (some e)),_,_,_⟩=some (shortParent B FN u e)
      rw [meta_peer]
      rfl

theorem meta_room (degree : (A).degree+1<2^b) (capacity : (A).cap<2^b) (x j v g t) :
    digits (actualMeta B rack x j v g) t<2^b := by
  have pos : 1<2^b:=by omega
  cases hv:rack v with
  | none=>
    simp only [actualMeta,hv,Option.elim_none]
    fin_cases t <;> exact Nat.two_pow_pos _
  | some r=>
    let u : Host:=((g,r),x)
    change digits ((rack v).elim _ _) t<_
    rw [hv]
    change digits («meta» B u (localOrigin B u j)) t<_
    cases found:localOrigin B u j with
    | none=>fin_cases t <;> exact Nat.two_pow_pos _
    | some e=>
      have bound (u' : Host) : localClass B u u'<2^b:=
        ((Finset.card_le_card (Finset.filter_subset ..)).trans (sources_room A u)).trans_lt degree
      have count:=(DescentResetWindowFields.count_room A ord S B.next.valid C₀ u e).trans_lt capacity
      fin_cases t <;> first | exact pos | exact bound _ | exact count | exact (Bool.toNat_le _).trans_lt pos

theorem ticket_room (cap : B.raw.cap≤2^b) (x j v g) : actualTicket B rack x j v g<2^b := by
  cases hv:rack v with
  | none=>simpa only [actualTicket,hv,Option.elim_none] using Nat.two_pow_pos b
  | some r=>
    simp only [actualTicket,hv,Option.elim_some]
    cases he:localOrigin B ((g,r),x) j with
    | none=>exact Nat.two_pow_pos _
    | some e=>exact (sourceTicket B e.val e.property.1).isLt.trans_le cap

theorem parent_room (degree : (A).degree+1<2^b) (capacity : (A).cap<2^b) (old : B.raw.cap≤2^b) (x j v g) :
    DescentResetSignedScan.Fits b (actualParent B rack x j v g) := by
  cases hv:rack v with
  | none=>simp [actualParent,hv,DescentResetSignedScan.Fits]
  | some r=>
    let u : Host:=((g,r),x)
    change DescentResetSignedScan.Fits b ((rack v).bind _)
    rw [hv]
    change DescentResetSignedScan.Fits b ((localOrigin B u j).map (shortParent B FN u))
    cases hz:localOrigin B u j with
    | none=>trivial
    | some e=>
      have p : 1<2^b:=by omega
      exact ⟨p,(show (shortParent B FN u e).peer<(A).degree from Fin.isLt _).trans (by omega), (sourceClass B u e).isLt.trans degree,
        (sourceTicket B e.val e.property.1).isLt.trans_le old,
        (DescentResetWindowFields.count_room A ord S B.next.valid C₀ u e).trans_lt capacity⟩

theorem sum_room (parallel : Bool) (u : Host) (e : Local C₀ u) :
    position_ parallel u e<(A).cap := by
  cases parallel with
  | false=>rw [incident_position];exact Fin.isLt _
  | true=>
    rw [shared_position]
    apply (board).serial_lt fit
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨(C₀).atSource ..,(C₀).atTarget ..⟩⟩

def localOffset (x : Fin X) (p : Fin 3) (j : Fin K) (v : Fin H) (g : Fin gg) : ℕ :=
  (rack v).elim 0 (fun r=>(localOrigin B ((g,r),x) j).elim 0 (fun e=>position_ (Ranks.parallelQuery p) ((g,r),x) e))

theorem local_rank_sum (x p j v g) :
    (∑a,contribution (Ranks.parallelQuery p) (actualParent B rack x j v g) (actualParent B rack x a v g))=
      localOffset B rack x p j v g := by
  cases hv:rack v with
  | none=>simp [actualParent,localOffset,hv,contribution]
  | some r=>
    let u : Host:=((g,r),x)
    simp only [actualParent,localOffset,hv,Option.bind_some,Option.elim_some]
    change (∑a,contribution _ ((localOrigin B u j).map (shortParent B FN u)) (shortRow B FN (localRoster B) u a))=_
    cases he:localOrigin B u j with
    | none=>simp [u,contribution]
    | some e=>simp [u,sumAt]

theorem local_room (limit : (A).cap≤2^b) (x p j v g) :
    localOffset B rack x p j v g<2^b := by
  cases hv:rack v with
  | none=>simpa only [localOffset,hv,Option.elim_none] using Nat.two_pow_pos b
  | some r=>
    simp only [localOffset,hv,Option.elim_some]
    cases he:localOrigin B ((g,r),x) j with
    | none=>exact Nat.two_pow_pos _
    | some e=>exact (sum_room B _ _ e).trans_le limit

theorem offset_at_receiver (x p j v g) (here : p≠(2:Fin 3)) :
    (localOffset B rack x p j v g:Cell b)=actualOffset (b:=b) B rack x p j v g := by
  cases hv:rack v with
  | none=>simp [localOffset,actualOffset,hv]
  | some r=>
    simp only [localOffset,actualOffset,hv,Option.elim_some,rankAt,Ranks.parallelQuery]
    cases hs:localOrigin B ((g,r),x) j with
    | none => rfl
    | some e =>
      have same : decide (p.val=1)=decide (p=1) :=
        decide_eq_decide.mpr ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp only [Option.elim_some,ite_eq_right here,same]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
