import OAI.Hierarchy.DescentPacketPullInvoiceVolume
import OAI.Hierarchy.DescentResetReceivedVolume

namespace OAI
/-! # Both prepared root packet invoices on the actual dated reset -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentCompiler DescentSixParty
noncomputable section
set_option quotPrecheck false

def packetFactor (v : ResetOutput) (growth : ℕ) :=
  let P:=v.setup.packets
  (DescentPacketPullInvoiceVolume.factor (P.stage 0 false).fields P.blocks+
    DescentPacketPullInvoiceVolume.factor (P.stage 0 true).fields P.blocks)*(growth+2)

private theorem packetKeys (v : ResetOutput) (side : Bool) (positive : 0<v.sheets.blocks) :
    let width:=v.setup.packets.oldBits*(v.setup.packets.stage 0 side).fields
    width+width≤v.groupWidth ∧ width*v.sheets.blocks≤v.groupWidth :=by
  let width:=v.setup.packets.oldBits*(v.setup.packets.stage 0 side).fields
  have old : width∈v.rootUnits := by cases side <;> simp [rootUnits,width]
  have new_ : width*v.sheets.blocks∈v.receiverUnits := by cases side <;> simp [receiverUnits,width]
  have o:=List.single_le_sum (fun _ _=>Nat.zero_le _) _ old
  have n:=List.single_le_sum (fun _ _=>Nat.zero_le _) _ new_
  have below:=Nat.le_mul_of_pos_right width positive
  unfold groupWidth
  rw [List.sum_append]
  change width+width≤_ ∧ width*v.sheets.blocks≤_
  omega

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "pkg" => (V).setup.packets
local notation "P" => S.hostSize age
local notation "O" => S.groupCount age
local notation "M" => 2^e
local notation "X" => 2^k
local notation "growth" => 2^S.hostGain*S.radix
local notation "T" => receiptArea h P (chunks O M)

/-- The previous host rows are scanned once per packet. Both lookups for a split
field are financed even at block count one by its two occurrences in the original width list. -/
theorem packet_volume (floor : ℕ) (radix : S.radix=X) (reached : age<S.length)
    (fitted : (V).groupWidth*(V).receiver.lanes≤h/2) :
    ((pkg).lane ((V).setup.placed floor) false).invoice+((pkg).lane ((V).setup.placed floor) true).invoice≤
      (V).packetFactor growth*T :=by
  let A:= (growth+1)*T
  have hx:=Nat.two_pow_pos k
  have hm:=Nat.two_pow_pos e
  have split : S.groupCount (age+1)*X=O:=by
    simpa only [Fintype.card_prod,Fintype.card_fin] using (Fintype.card_congr (S.groupDigits reached radix)).symm
  have count : S.groupCount (age+1)≤O:=(Nat.le_mul_of_pos_right _ hx).trans_eq split
  have fewer : chunks (S.groupCount (age+1)) M≤chunks O M :=
    Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right count _) _)
  have next : S.hostSize (age+1)=P*growth :=by simp only [AtomSchedule.hostSize,pow_succ,Nat.mul_assoc]
  have rows : P*chunks O M≤T:=by unfold receiptArea;omega
  have hosts : P≤T:=by unfold receiptArea;omega
  have tables : (h+1)^3*2^(h/2)≤T:=by unfold receiptArea;omega
  have pos : 0<T:=lt_of_lt_of_le (by positivity) tables
  have fixed : T≤A:=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have packedRows: P*chunks (S.groupCount (age+1)) M ≤ T:=(Nat.mul_le_mul_left _ fewer).trans rows
  have nextRows : S.hostSize (age+1)*chunks (S.groupCount (age+1)) M ≤ A:=by
    rw [next,show (P*growth)*chunks (S.groupCount (age+1)) M=growth*(P*chunks (S.groupCount (age+1)) M) by ring]
    exact Nat.mul_le_mul (Nat.le_succ _) packedRows
  have logged : 0<Nat.clog 2 (X+1):=Nat.clog_pos (by decide) (by omega)
  have known : X*Nat.clog 2 (X+1)∈(V).rootUnits := by
    change (2^(V).middle.rootDepth)*Nat.clog 2 (2^(V).middle.rootDepth+1)∈(V).rootUnits
    simp [rootUnits]
  have lengthFit : X≤(V).groupWidth:=(Nat.le_mul_of_pos_right _ logged).trans ((V).groupWidth_fit (Or.inl known))
  have big : M*X≤h:=by
    rw [Nat.mul_comm M X]
    exact (Nat.mul_le_mul_right M lengthFit).trans (fitted.trans (Nat.div_le_self ..))
  have pitch : M≤h:=(Nat.le_mul_of_pos_right _ hx).trans big
  have single (s : Bool) :
      ((pkg).lane ((V).setup.placed floor) s).invoice≤
      DescentPacketPullInvoiceVolume.factor ((pkg).stage 0 s).fields (pkg).blocks*(A+1):=by
    let L:=(pkg).lane ((V).setup.placed floor) s
    obtain ⟨twice,strip⟩:=packetKeys (V) s hx
    have doubled : (L.width+L.width)*M≤h/2:=(Nat.mul_le_mul_right M twice).trans fitted
    have dest : (L.width*X)*M≤h/2:=(Nat.mul_le_mul_right M strip).trans fitted
    have source : L.width*M≤h/2:=(Nat.mul_le_mul_right M (Nat.le_add_right L.width L.width)).trans doubled
    apply DescentPacketPullInvoiceVolume.one L h A hm hm hx pitch big source dest
    · change P*chunks (S.groupCount (age+1)*X) M≤A
      rw [split]
      exact rows.trans fixed
    · exact packedRows.trans fixed
    · exact tables.trans fixed
    · exact hosts.trans fixed
    · exact nextRows
    · exact doubled
  have total:=Nat.add_le_add (single false) (single true)
  rw [←Nat.add_mul] at total
  change _≤(_+_)*(growth+2)*T
  rw [Nat.mul_assoc]
  apply total.trans
  apply Nat.mul_le_mul_left
  dsimp only [A]
  exact (Nat.add_le_add_left pos ((growth+1)*T)).trans_eq (Nat.succ_mul (growth+1) T).symm

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
