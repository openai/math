import OAI.Hierarchy.DescentDatedMatcherClock
import OAI.Hierarchy.DescentDatedMatcherHardwareBill
import OAI.Hierarchy.DescentMatcherCountTariff

namespace OAI
/-! # Native match and count prices on the same census, roster and layout tables -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
namespace DateBill

def matchCountRate (k D cap K bound : ℕ) :=
  5*(Census.multiplier k D cap K (max 22 bound)+2*extraFactor k D K)+
  2*(controlFactor k D cap K bound+2000*(1+K))

/-- Includes all labels/registers/slots of the matcher, plus a sevenfold allowance for
those of the final physical count publication. -/
theorem match_count_bill {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k groups ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k)
    (board payload unit ratio profile seats : ℕ) (input : Dated.Operands) (floor : ℕ)
    (bound : ℕ) (atoms : ∀x : Fin (2^k),(input.atoms x.val).work≤bound)
    (groupsPos : 0<groups) (word : w≤ratio*payload) (gate : 2^k+(k+3)≤unit) :
    let H:=(2:ℕ)^ℓ
    let K:=2^(k+1)
    let a:Dated.Ordinary:=⟨H,groups,k,board,A.degree,A.cap,payload,unit,profile,seats⟩
    let data:Dated.Measures:=⟨A.wire,A.z,A.hist⟩
    let b:=a.shapeAt.outputBits*a.lanesAt
    let N:=(K*H)*chunks groups a.lanesAt
    ∀(_space : a.Space input w floor) (src : Bank) (fee : Cell b→ℕ) (base : ℕ),
    ((a.ticks G A.fieldBits input data w floor+DescentStaticWordColumn.names (a.program G A.fieldBits input data w floor))+
      (DescentOrdinaryCountScan.clock b N+7*DescentStaticWordColumn.names (DescentOrdinaryCountScan.program w src fee base N)))*w ≤
      (ratio*matchCountRate k A.degree A.cap K bound)*volumeBits H groups payload unit := by
  intro H K a data b N _space src fee base
  let V:=volumeBits H groups payload unit
  let words₀:=words H groups payload unit
  let t:=a.ticks G A.fieldBits input data w floor
  let names₀:=DescentStaticWordColumn.names (a.program G A.fieldBits input data w floor)
  let count:=DescentOrdinaryCountScan.clock b N+7*DescentStaticWordColumn.names (DescentOrdinaryCountScan.program w src fee base N)
  let old:=Census.multiplier k A.degree A.cap K (max 22 bound)+2*extraFactor k A.degree K
  let ctrl:=controlFactor k A.degree A.cap K bound
  let post:=2000*(1+K)
  have radixPos : 0<(2:ℕ)^k:=Nat.two_pow_pos _
  have unitPos : 0<unit:=by omega
  have bytes:=_space.laneWidth
  have lanePos : 0<a.lanesAt:=(DescentSIMDLookup.occupancy payload unit unitPos bytes).1
  have rowsPos : 0<a.rows :=
    Nat.mul_pos _space.hosts
      (position (⟨0,_space.hosts⟩ : Fin a.H) (⟨0,groupsPos⟩ : Fin a.G) lanePos).2.pos
  have cable : DescentSignedCableCodec.width A.degree A.cap≤unit:=
    (le_max_right ..).trans ((le_max_right ..).trans _space.inputWidth)
  have cost : t*w≤ratio*(old*V):=Dated.real_clock (ℓ:=ℓ) (groups:=groups) A board payload unit ratio profile seats
    input floor bound atoms unitPos bytes word gate cable _space.chooserWidth _space.birthWidth
  have code:=a.hardware_bill G A.fieldBits input data w floor bound atoms _space rowsPos gate
  let chooser:=a.chooser input.roster floor
  have core : chooser.ticks a.D a.k a.b (2*a.cap) a.H a.G a.lanesAt w≤t:=by
    dsimp only [t,Dated.Ordinary.ticks,chooser];omega
  have controls : names₀≤4*t+ctrl*words₀:=code.trans (by gcongr)
  have liveBits : a.shapeAt.outputBits≤unit:= (Nat.le_add_left ..).trans ((le_max_left ..).trans _space.birthWidth)
  have short : b≤payload/2 := (Nat.mul_le_mul_right _ liveBits).trans
    (by simpa only [Dated.Ordinary.lanesAt,Nat.mul_comm unit] using lanes_fit payload unit)
  have finish : count≤post*words₀:=count_words H groups payload unit K w b src fee base short
  have volume : words₀*w≤ratio*(2*V) := calc
    _ ≤ words₀*(ratio*payload):=Nat.mul_le_mul_left _ word
    _ = ratio*(words₀*payload):=by ring
    _ ≤ _:=Nat.mul_le_mul_left _ (words_bits H groups payload unit unitPos bytes)
  change (t+names₀+count)*w≤(ratio*(5*old+2*(ctrl+post)))*V
  calc
    _ ≤ (5*t+(ctrl+post)*words₀)*w := Nat.mul_le_mul_right _ (by nlinarith only [controls,finish])
    _ = 5*(t*w)+(ctrl+post)*(words₀*w):=by ring
    _ ≤ 5*(ratio*(old*V))+(ctrl+post)*(ratio*(2*V)) := Nat.add_le_add
      (Nat.mul_le_mul_left _ cost) (Nat.mul_le_mul_left _ volume)
    _ = _:=by ring

end DateBill
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
