import OAI.Hierarchy.DescentDatedOperandPages
import OAI.Hierarchy.DescentRoleScansNames
import OAI.Hierarchy.DescentOrdinaryOverlapReserve
import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentArgumentPageWordTariff
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentOrdinaryWordTariff

namespace OAI
/-! # Native cost of the earlier Parts-to-operand pages and their physical pitch change -/
namespace Hierarchy.DescentDatedOperandPages
open DescentSIMDLookup DescentPackedColony DescentRawCablePanel.DepotRAM
open DescentOperandPriorIncidence DescentSixParty.Chronology DescentPackedZip
open DescentStaticWordColumn DescentDatedSeedStartup DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable (f : Shape) (l : Layout)
local notation "H" => l.hosts
local notation "G" => l.groups
local notation "A" => l.old
local notation "B" => l.newLanes
local notation "N" => count f

theorem evaluate_fee (base w h unit ratio : ℕ) (src : Bank) (lookup : (totalBits f)*A≤h/2)
    (density : h≤A*unit) (bus : w≤ratio*h) :
    DateBill.bitTariff (evaluate f l base w src).program (evaluate f l base w src).ticks ≤
      2048*ratio*(N+1)*(h+H*h+H*G*unit)+2048*ratio*(N+1)*2^(h/2)*h :=by
  unfold DateBill.bitTariff
  apply page_scan_words H G A unit h w ratio N 2048 _ density bus
  change RoleScans.ticks (totalBits f) H G A N+
    7*names (RoleScans.cpu (law f l.profile l.bits) H G A w base N src) ≤ _
  rw [RoleScans.cpu_names]
  have span : 2^(Nat.clog 2 (H*chunks G A))≤2*(H*chunks G A)+1 :=DescentDyadicSpan.span_le _
  have pc : RoleScans.pitch (totalBits f) H G A≤2^(h/2)+(2*(H*chunks G A)+1) :=
    Nat.add_le_add (Nat.pow_le_pow_right (by decide) lookup) span
  unfold RoleScans.ticks
  calc
    _ ≤ (4+10*(N*(2^(h/2)+(2*(H*chunks G A)+1))))+(4+N*(4+44*(H*chunks G A)))+
      7*(15*(N*(2^(h/2)+(2*(H*chunks G A)+1))+1)+(15+N*(11+4*20))) :=by gcongr
    _ ≤ _ :=by ring_nf; omega

theorem phase_word_bill (base w h x y ratio : ℕ) (src : Bank)
    (oldCap : A≤h) (newCap : B≤h) (oldPos : 0<A) (newPos : 0<B)
    (purchase : (totalBits f)*A≤h/2) (lookup : l.bits*A≤h/2)
    (before : h≤A*x) (after : h≤B*y) (bus : w≤ratio*h) :
    DateBill.bitTariff (phase f l base w src).program (phase f l base w src).ticks ≤
      2048*ratio*(N+1)*(h+H*h+H*G*x)+2048*ratio*(N+1)*2^(h/2)*h+
      2048*ratio*(h+2*(N*H)*h+(N*H)*G*(x+y))+(2048*ratio)*(2*(h+1)^2*2^(h/2))*h :=by
  have recompute:=evaluate_fee f l base w h x ratio src purchase before bus
  have transfer:=Overlap.tariff (scratch f l base) (N*H) G A B l.bits w (sourceRows f l base) oldPos newPos
  have allocation:=Overlap.half_pages h G A B l.bits oldCap newCap lookup
  have initial:=chunk_work (N*H) G A h x before
  have final:=chunk_work (N*H) G B h y after
  unfold phase
  rw [show ∀(p q : NativePhase w),DateBill.bitTariff (p.seq q).program (p.seq q).ticks =
    DateBill.bitTariff p.program p.ticks+DateBill.bitTariff q.program q.ticks from fun p q=>DateBill.bitTariff_seq ..]
  rw [Nat.add_assoc _ (2048*ratio*(h+2*(N*H)*h+(N*H)*G*(x+y)))]
  refine Nat.add_le_add recompute ?_
  refine (Nat.mul_le_mul transfer bus).trans ?_
  unfold Overlap.rows
  calc
    _ = 2048*ratio*(h+((N*H)*chunks G A)*h+((N*H)*chunks G B)*h)+
          (2048*ratio)*((Overlap.pieces G A B+1)*(A+1)*2^(l.bits*A))*h :=by ring
    _ ≤ 2048*ratio*(h+((N*H)*h+(N*H)*G*x)+((N*H)*h+(N*H)*G*y))+
          (2048*ratio)*(2*(h+1)^2*2^(h/2))*h :=by gcongr
    _ = _ :=by ring
end
end Hierarchy.DescentDatedOperandPages

end OAI
