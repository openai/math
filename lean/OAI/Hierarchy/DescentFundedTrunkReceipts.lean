import OAI.Hierarchy.DescentFundedCensusRoles
import OAI.Hierarchy.DescentRecordedStencilCell
import OAI.Hierarchy.DescentFundedArrivals

namespace OAI
/-! # The two charged trunk columns from real prior counts and the signed census -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPaidResidentCount.Reset DescentFundedCensus DescentColonies DescentGL
open DescentCompiler DescentIssuedFallbackPanel DescentPacking.PackedMatch.Local.Stage
open DescentContacts DescentChosenRouter DescentPlainTerminal DescentPlainTerminal.Suffix
open DescentSharedCableNames DescentRelativeContacts DescentSIMDLookup
open scoped BigOperators Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist p H : ℕ}
  {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset cap ctl) (issued : b.Recorded p) (racks : cap.V↪Fin H)
local notation "Z" => b.reset
local notation "T" => b.terminals
local notation "A" => cap.placement
local notation "c" => (T).commonDepth
local notation "width" => S.groupWidth k tail i+k
local notation "L" => 2^(width-c)
local notation "B" => (A).wire*((A).z*G.b)*(A).cap
local notation "K" => quota S.rounds
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fit" => b.frame.enough.trans (Nat.sub_le ..)
local notation "mu" => rearrange b.frame.basis
local notation "group_" => Equiv.refl (Fin (S.groupCount i))
local notation "cost" => fun v : W.graph.Site=>((A).records v).length
local notation "cc" => DescentPacking.PackedMatch.Local.Stage.Census.count A group_ racks
local notation "sg" => DescentSignedCableCodec.width (A).degree (A).cap

variable {oldBits sf payBits : ℕ}
variable (up : S.groupWidth k tail i+k-b.terminals.commonDepth<2^oldBits) (one : 1<2^oldBits)
  (enough : 2^(S.groupWidth k tail i+k-b.terminals.commonDepth)*
    (cap.placement.wire*(cap.placement.z*G.b)*cap.placement.cap)<2^oldBits)
  (legal : 2*DescentFallbackShapeTable.rows (S.groupWidth k tail i+k-b.terminals.commonDepth)
    (2^b.reset.n)≤2^sf)
  (active : 0<cap.placement.wire*(cap.placement.z*G.b)*cap.placement.cap)
  (quotaPos : 0<quota S.rounds) (degreePos : 0<32*Nat.clog 2 (2*cap.placement.degree))
variable (t : b.reset.Fallback)
local notation "v₀" => b.frame.host.symm (((T).code t).1)
local notation "hi" => (Z).rootBlock T (.inr t)
local notation "prior" => fun l => (mu).symm (join fit hi l)
local notation "hold" => Recorded.realPanel (reset:=b) rfl b.frame.basis oldBits sf v₀ hi
local notation "name" => DescentFallbackShapeTable.cell ((Z).k-c) (DescentRelativeContacts.shortName c ((T).code t)).2
local notation "mode" => Recorded.originalCell (reset:=b)

include up one enough legal active quotaPos degreePos issued in
theorem funded_stencil (l : Block (width-c)) :
    (hold l).val/2=Stencil.shapeCode (width-c) (2^(Z).n) (fieldsRelative c (mode v₀ (prior l))) :=by
  have at_:=issued.stencil_cell rfl b.frame.basis HEq.rfl up one enough legal active quotaPos degreePos v₀ hi l
  simp only [Fin.cast_refl] at at_
  have decode (value shape : ℕ) (flag : Bool) (eqn : value=2*shape+flag.toNat) :
      value/2=shape := by
    have bounded := Bool.toNat_le flag
    omega
  exact decode _ _ _ at_


include up one enough legal active quotaPos degreePos in
theorem primary_payout (paidFits : B<2^payBits) :
    (trunk sf payBits L name).apply (encode sf L hold)
      (encode payBits L (fun l=>cc payBits (racks v₀) ((digits (prior l)).1) ((digits (prior l)).2)))=
      ((payee b issued (.inl (false,t)):ℕ):Cell payBits) :=by
  apply funded_chip b.frame (cap.vertex.trans Fin.valEmbedding) (A).mutual (Z).n f B (A).wire K (A).degree ((A).resetLoad digits)
    (fun v u j=>(((A).resetFlow digits v u j):ℝ)) (Recorded.old_roster (reset:=b)) t (fun l=>(hold l).val)
    (funded_stencil b issued up one enough legal active quotaPos degreePos t) (fun v : W.graph.Site=>v) cost
    hold (fun l=>cc payBits (racks v₀) ((digits (prior l)).1) ((digits (prior l)).2)) (fun _=>rfl)
  intro l
  exact previous_paid A S cap.valid racks group_ paidFits digits v₀ (prior l)

include up one enough legal active quotaPos degreePos in
theorem relay_payout (order : W.graph.Edge↪ℕ) (names : DescentSharedCableNames.Stage.Host (Fin (S.groupCount i)) cap.V k↪ℕ)
    (ports : Fin (2*(A).cap)→Fin L→Cell sg)
    (read : ∀j l,ports j l=DescentSignedCableCodec.encode (Stage.signedPanel A order S cap.valid names
      (((digits (prior l)).1,v₀),(digits (prior l)).2) j)) (small : 2*(A).cap<2^payBits) :
    (trunk sf payBits L name).apply (encode sf L hold) (encode payBits L (fun l=>
      ((∑j,Arrivals.bit (A).degree (A).cap (ports j l):ℕ):Cell payBits)))=
      ((payee b issued (.inl (true,t)):ℕ):Cell payBits) :=by
  apply funded_chip b.frame (cap.vertex.trans Fin.valEmbedding) (A).mutual (Z).n f B (A).wire K (A).degree ((A).resetLoad digits)
    (fun v u j=>(((A).resetFlow digits v u j):ℝ)) (Recorded.old_roster (reset:=b)) t (fun l=>(hold l).val)
    (funded_stencil b issued up one enough legal active quotaPos degreePos t) W.graph.dst (A).grainCount
    hold _ (fun _=>rfl)
  intro l
  have total : (∑j,Arrivals.bit (A).degree (A).cap (ports j l))<2^payBits :=
    (Arrivals.count_le (fun j (_ : Fin 1) (_ : Fin 1) u=>ports j u) 0 0 l).trans_lt small
  rw [Fin.val_cast_of_lt total]
  exact previous_relay A S cap.valid order names digits v₀ (prior l) (fun j=>ports j l) (fun j=>read j l)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
