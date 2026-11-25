import OAI.Hierarchy.DescentDatedOrdinaryHardware
import OAI.Hierarchy.DescentDatedOrdinaryAny
import OAI.Hierarchy.DescentMatcherControlFactor
import OAI.Hierarchy.DescentMatcherBirthPages
import OAI.Hierarchy.DescentPackedOrdinaryDateBill

namespace OAI
/-! # Physical control names in the publicly scheduled ordinary matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup DescentSixParty ProtocolRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section

namespace Dated.Ordinary
variable {F : Type} [Field F] (a : Ordinary) (gadget : PoweredGadget F) (hk : 0<a.k)
    (i : Operands) (v : Measures) (w floor : ℕ)
local notation "r" => 2^a.k
local notation "K" => 2^(a.k+1)
local notation "M" => a.lanesAt
local notation "C" => a.chooser i.roster floor
local notation "V" => DateBill.words a.H a.G a.payload a.unit
local notation "N" => Census.columns r a.cap
local notation "s" => a.shapeAt

theorem hardware_bill (bound : ℕ) (bounded : ∀x : Fin r,(i.atoms x.val).work≤bound)
    (space : Space a i w floor) (live : 0<a.rows) (gateSize : r+(a.k+3)≤a.unit) :
    names (a.program gadget hk i v w floor)≤
      4*(C).ticks a.D a.k a.b (2*a.cap) a.H a.G M w+DateBill.controlFactor a.k a.D a.cap K bound*V := by
  have mass : a.unit*M≤a.payload/2 := by
    simpa only [lanesAt,Nat.mul_comm a.unit] using lanes_fit a.payload a.unit
  have volume : V=1+2^(a.payload/2)+a.H+a.rows :=rfl
  have volume_parts (x y z : ℕ) :
      1 ≤ 1+x+y+z ∧ x ≤ 1+x+y+z ∧ y ≤ 1+x+y+z ∧ z ≤ 1+x+y+z := by omega
  obtain ⟨one,fund,hosts,packed⟩ : 1 ≤ V ∧ 2^(a.payload/2) ≤ V ∧ a.H ≤ V ∧ a.rows ≤ V := by
    rw [volume]
    exact volume_parts _ _ _
  have cable : DescentSignedCableCodec.width a.D a.cap≤a.unit :=
    (le_max_right ..).trans ((le_max_right ..).trans space.inputWidth)
  have wordPage : 2^(a.unit*M)≤V := (Nat.pow_le_pow_right (by decide : 0<2) mass).trans fund
  have flags : (1*r+(a.k+3))*M≤a.payload/2 := by
    rw [Nat.one_mul];exact (Nat.mul_le_mul_right M gateSize).trans mass
  have code:=controls a gadget hk i v w floor bound V bounded live flags
    ((Nat.mul_le_mul_right M cable).trans mass) mass fund hosts packed
  have tables:=DateBill.header_words (w:=w) (C).chart a.k a.b a.D (2*a.cap) a.H a.G a.payload a.unit
    (C).origin (DescentHostDegree.gap a.D)
    (2^DescentHostDegree.packExponent 20 a.D*((v.wire*(v.z*gadget.b))*a.cap))
    hk (fun fl=>PackedCensus.lookup fl a.b (2*a.cap) a.k v.wire 256 (v.z*gadget.b) v.hist) rfl space.chooserWidth
  have input : (a.censusImage gadget i v w floor).length≤2*V :=tables.1
  have phase : (a.chooserImage gadget hk i v w floor).length≤2*Phase.Arena.sharedTables a.k a.D*V:=tables.2
  have ⟨birth,emit⟩:=DateBill.birth_pages s a.payload a.unit M V space.birthWidth mass fund
  have nPage:=Nat.mul_le_mul_left N wordPage
  have cost:=Nat.mul_le_mul_left (4*N*(max 22 bound+6)) one
  have rotation:=Nat.mul_le_mul_left r one
  have drop:=Nat.sub_le r 1
  simp only [Nat.mul_one] at cost rotation
  apply code.trans
  unfold DateBill.controlFactor DateBill.extraFactor
  nlinarith only [input,phase,birth,emit,nPage,cost,rotation,drop,one,packed,
    Nat.zero_le (K*V),Nat.zero_le (Phase.Arena.sharedTables a.k a.D*V),Nat.zero_le (r*V)]

/-- An occupied typed date already pays for the selector inputs inside its
chooser width and has at least one resident row in its first host. -/
theorem occupied_hardware_bill (bound : ℕ) (bounded : ∀x : Fin r,(i.atoms x.val).work≤bound)
    (space : Space a i w floor) (groups : 0<a.G) :
    names (a.program gadget hk i v w floor)≤
      4*(C).ticks a.D a.k a.b (2*a.cap) a.H a.G M w+DateBill.controlFactor a.k a.D a.cap K bound*V := by
  have chart : Phase.unit a.k a.b ≤ a.unit := (le_max_left ..).trans space.chooserWidth
  have mul : r≤a.k*r:=by simpa using Nat.mul_le_mul_right r hk
  have gates : r+(a.k+3)≤a.unit := by
    unfold Phase.unit at chart
    omega
  have unit : 0<a.unit := (Nat.two_pow_pos a.k).trans_le (by omega)
  have hm : 0<M := (occupancy a.payload a.unit unit space.laneWidth).1
  let p:=position (⟨0,space.hosts⟩ : Fin a.H) (⟨0,groups⟩ : Fin a.G) hm
  exact hardware_bill a gadget hk i v w floor bound bounded space (Nat.mul_pos space.hosts p.2.pos) gates

end Dated.Ordinary
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
