import OAI.Hierarchy.DescentResetLocalRankRAM
import OAI.Hierarchy.DescentResetRankedCandidates

namespace OAI
/-! # All reset receiver ranks from meta records and the measured ticket at their source -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentNextSignedWindow DescentResetSignedScan
open DescentPackedColony DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) {H M b bitsW : ℕ}
local notation "X" => 2^k
local notation "K" => totalLocal B
local notation "gg" => S.groupCount (i+1)
local notation "A" => B.next.placement
open DescentResetLocalRankRun

theorem local_ranks (rack : Fin H→Option B.next.V) (base : ℕ) (header ticket : Fin X→Fin K→Expr) (m : Memory bitsW)
    (raw : ∀x j,(header x j).Fits bitsW base) (old : ∀x j,(ticket x j).Fits bitsW base)
    (source : ∀x j,Source (header x j) (fun v g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j v g)) M m)
    (assigned : ∀x j,Source (ticket x j) (fun v g=>(actualTicket B rack x j v g:Cell b)) M m)
    (degree : (A).degree+1<2^b) (cap : (A).cap<2^b) (prev : B.raw.cap≤2^b)
    (space : endAddress base X K b M H gg<2^bitsW) :
    let done:=memory base X K b M H gg header ticket m
    (program base X K b M H gg bitsW header ticket).Exec m done (time base X K b M H gg header ticket) ∧
    (∀x p j,Reads (bank base X K b M H gg x p j) (fun v g=>(localOffset B rack x p j v g:Cell b)) M done) ∧
    (∀a,a<base ∨ endAddress base X K b M H gg≤a→done a=m a) ∧ CheapCode (program base X K b M H gg bitsW header ticket) := by
  intro done
  have room:=(lower base X K b M H gg).trans_lt space
  let rbase:=rankBase base b M
  let start:=RankInput.memory base b M m
  have guard (x j):=RankInput.expr_fits base (header x j) (ticket x j) (raw x j) (old x j) room
  have chip (x j) : Source (RankInput.expr base b M (header x j) (ticket x j))
      (fun v g=>encode b 5 (literal b (actualParent B rack x j v g))) M start :=by
    have issued:=RankInput.read base (header x j) (ticket x j) m (actualMeta B rack x j)
      (fun v g=>(actualTicket B rack x j v g:Cell b)) (raw x j) (old x j) (source x j) (assigned x j)
      (meta_room B rack degree cap x j) room
    simpa only [Fin.val_cast_of_lt (ticket_room B rack prev ..),actual_parent] using issued
  let qv : Ranks.QueryRows X K H gg:=fun x _ j=>actualParent B rack x j
  let rs : Ranks.ItemRows X K H gg:=fun x _ _ j=>actualParent B rack x j
  have bound (x p j v g): (∑a,contribution (Ranks.parallelQuery p) (qv x p j v g) (rs x p j a v g))<2^b :=
    (local_rank_sum B rack ..).trans_lt (local_room B rack cap.le ..)
  obtain ⟨_,got,_,_⟩:=Ranks.run rbase (query base b M header ticket) (items base b M header ticket) start qv rs
    (fun x _ j=>guard x j) (fun x _ _ j=>guard x j) (fun x _ j=>parent_room B rack degree cap prev x j)
    (fun x _ _ j=>parent_room B rack degree cap prev x j) (fun x _ j=>chip x j)
    (fun x _ _ j=>chip x j) bound space
  obtain ⟨exec,frame,ok⟩:=DescentResetLocalRankRun.any base X K b M H gg header ticket m raw old space
  refine ⟨exec,?_,frame,@ok⟩
  intro x p j
  have values : (fun v g => (localOffset B rack x p j v g : Cell b)) =
      sumWord (Ranks.parallelQuery p) (qv x p j) (rs x p j) (bound x p j) := by
    funext v g
    apply Fin.ext
    rw [Fin.val_cast_of_lt (local_room B rack cap.le x p j v g)]
    exact (local_rank_sum B rack x p j v g).symm
  rw [values]
  exact got x p j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
