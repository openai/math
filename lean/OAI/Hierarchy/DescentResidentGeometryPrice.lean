import OAI.Hierarchy.DescentReadyGeometryPhase

namespace OAI
/-! # Word work and names of the complete native donor geometry phase -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement
open DescentPacking.PackedMatch.Local DescentHaloWalkRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
open DescentSixParty.Chronology DescentStaticWordColumn ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable (H G M D r p d cap profile w base : ℕ) (adj hub : Bank) (e : Expr)
local notation "P" => breadth D
local notation "N" => H*chunks G M
local notation "a" => Owners.inputBits r D p d
local notation "L" => layout H G M D a base adj hub
local notation "W" => (L).walks
local notation "Q" => (L).ranks
local notation "u" => (body W H D 4).work
local notation "v" => (Ranks.body Q P).work
local notation "full" => issuedPhase H G M D r p d cap profile w base adj hub e
local notation "sharedWords" => 2^(a*M)+P*((M+1)*(P+1))
local notation "total" => (full).ticks+names (full).program

theorem geometry_count :
    total = 300 + 4*e.work+4*u+4*v+
      N*(2*e.work+148) + H*P*(2*u+2*v+206) + 25*sharedWords := by
  have hubWork : (DonorHeaders.hubExpr (L).ranks.endpoints (L).hub H).work=22 := rfl
  simp only [issuedPhase,rootsPhase,NativePhase.seq,Dynamic.phase,Owners.Board.issue,DonorHeaders.schedule,
    RootTables.program,Book.install,DonorChartBook.install,DescentSIMDLookup.program,names_seq,names_scan,names_mount,
    Owners.Board.ticks,Book.words,RootTables.length,DonorChartBook.words,DonorChartBook.pages,
    DonorHeaders.clocks,lookup_work,hubWork]
  ring

theorem geometry_limit :
    total≤1024*((N+1)*(e.work+1)+(H+1)*(D+10)^8+sharedWords) := by
  let X:=(D+10)^4
  have pos : 1≤X := Nat.pow_pos (show 0<D+10 by omega)
  have path : P≤X := Nat.pow_le_pow_left (show D+1≤D+10 by omega) 4
  have x2:X≤X*X:=by simpa using Nat.mul_le_mul_right X pos
  have walkWork := body_work W H D 4
  have rankWork := Ranks.body_work Q P
  have both : 2*u+2*v+206≤312*X:=by dsimp [X] at *;omega
  have area := Nat.mul_le_mul (Nat.mul_le_mul_left H path) both
  have squares:X*X=(D+10)^8:=by dsimp [X];rw [←pow_add]
  have tally : H*P*(2*u+2*v+206)≤312*(H*((D+10)^8)) :=
    area.trans_eq (by rw [←squares];ring)
  have perRow : 2*e.work+148≤148*(e.work+1):=by omega
  have localSum:=Nat.mul_le_mul_left N perRow
  rw [show N*(148*(e.work+1))=148*(N*(e.work+1)) by ring] at localSum
  rw [geometry_count]
  have bas : 4*u+4*v+300≤800*(D+10)^8:=by
    rw [←squares]
    change u+10≤20*X at walkWork
    omega
  simp only [Nat.add_mul,one_mul]
  omega

/-- The actual previous host canvas pays for all literal pages once per date.
The previous multiplicity can be much larger than one machine word. -/
theorem geometry_date {payload unit ratio : ℕ} (lanes_ : M=lanes payload unit)
    (positive : 0<unit) (room : 2*unit≤payload) (enters : a≤unit)
    (hosts : 2^(payload/2)≤H) (wordWidth : w≤ratio*payload) :
    total*w≤1024*ratio*((H*payload+4*H*G*unit+payload)*(e.work+1)+
      ((H+1)*(D+10)^8+H+2*H*(P+1)^2)*payload) := by
  have parts : N*payload≤H*payload+4*H*G*unit:=by simpa only [lanes_] using volume H G payload unit positive room
  have budget : a*M≤payload/2 := (Nat.mul_le_mul_right M enters).trans (by simpa [lanes_,Nat.mul_comm] using lanes_fit payload unit)
  have book : 2^(a*M)≤H := (Nat.pow_le_pow_right (by decide) budget).trans hosts
  have count : M≤payload/2 := by
    have room' : M*unit≤payload/2:=by simpa [lanes_] using lanes_fit payload unit
    exact (by simpa using (Nat.mul_le_mul_left M positive) : M≤M*unit).trans room'
  have bins : M+1≤H:=((Nat.succ_le_succ count).trans (Nat.lt_two_pow_self)).trans hosts
  have covers : P*((M+1)*(P+1))≤2*H*(P+1)^2:=by
    have bound:=Nat.mul_le_mul (Nat.le_succ P) (Nat.mul_le_mul_right (P+1) bins)
    nlinarith only [bound,Nat.zero_le (H*(P+1)^2)]
  have total_:=geometry_limit H G M D r p d cap profile w base adj hub e
  have low:=Nat.mul_le_mul total_ wordWidth
  have reg:=(Nat.mul_le_mul_right (e.work+1) (Nat.add_le_add_right parts payload))
  have old:=Nat.mul_le_mul_right payload (Nat.add_le_add_left (Nat.add_le_add book covers) ((H+1)*(D+10)^8))
  calc
    _ ≤ 1024*ratio*(((N+1)*(e.work+1))*payload+(((H+1)*(D+10)^8)+sharedWords)*payload) :=
      low.trans_eq (by ring)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add (by convert reg using 1; ring) (by simpa [Nat.add_assoc] using old))


theorem geometry_word_bill {payload unit ratio : ℕ} (lanes_ : M=lanes payload unit)
    (positive : 0<unit) (room : 2*unit≤payload) (enters : a≤unit)
    (hosts : 2^(payload/2)≤H) (wordWidth : w≤ratio*payload) :
    total*w≤16384*ratio*((H*payload+H*G*unit)*(e.work+1)+H*payload*(D+10)^8) := by
  have previous:=geometry_date H G M D r p d cap profile w base adj hub e lanes_ positive room enters hosts wordWidth
  have nonempty : 1≤H:=(Nat.two_pow_pos _).trans_le hosts
  have units : payload≤H*payload:=by simpa using Nat.mul_le_mul_right payload nonempty
  have left : H*payload+4*H*G*unit+payload≤4*(H*payload+H*G*unit):=by
    rw [show 4*H*G*unit=4*(H*G*unit) by ring];omega
  let X:=(D+10)^4
  have xpos : 1≤X := Nat.pow_pos (show 0<D+10 by omega)
  have path : P≤X := Nat.pow_le_pow_left (show D+1≤D+10 by omega) 4
  have square : X^2=(D+10)^8:=by dsimp [X];rw [←pow_mul]
  have wide : 1≤(D+10)^8 := Nat.pow_pos (show 0<D+10 by omega)
  have double_ : P+1≤2*X:=by omega
  have area: (P+1)^2≤4*(D+10)^8:=(Nat.pow_le_pow_left double_ 2).trans_eq (by rw [←square];ring)
  have height : H+1≤2*H:=by omega
  have first:=Nat.mul_le_mul_right ((D+10)^8) height
  have last:=Nat.mul_le_mul_left (2*H) area
  have row:=Nat.mul_le_mul_left H wide
  have amount: (H+1)*(D+10)^8+H+2*H*(P+1)^2≤11*(H*(D+10)^8):=by
    nlinarith only [first,last,row]
  have allocations:=Nat.add_le_add (Nat.mul_le_mul_right (e.work+1) left) (Nat.mul_le_mul_right payload amount)
  have big:=Nat.mul_le_mul_left (1024*ratio) allocations
  calc _ ≤ _ := previous
       _ ≤ _ := big
       _ ≤ _ := by
         nlinarith only [Nat.zero_le (ratio*(H*payload+H*G*unit)*(e.work+1)),Nat.zero_le (ratio*payload*(H*(D+10)^8))]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Resident.Dynamic.Placement

end OAI
