import OAI.Hierarchy.DescentSeedHeaderLayout
import OAI.Hierarchy.DescentSeedPublicFrontRate
import OAI.Hierarchy.DescentSeedSelectedAperture
import OAI.Hierarchy.DescentSeedRoleFloor
import OAI.Hierarchy.DescentTerminalPublicImageRate
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentPackedEpochBill

namespace OAI
/-! # One address exponent for the original dated seed over all terminal cutoffs -/
namespace Hierarchy.DescentDatedSeedStartup.SeedHeader
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentWideSeedFlags DescentPackedEpochShelves
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentTerminalDenseWindow DescentTerminalBinReaddress
open DescentInitialHost DescentSeedRoot DescentExterior DescentDatedAddressBook Catalyst Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F]

variable (G : PoweredGadget F) (op : RotorSpec) (t f g drift : ℕ)
namespace Input
variable (v : Input F)

/-- These are quantities in the public input and its lookup tables, before the seed runs. -/
structure Purchased (h a : ℕ) : Prop where
  budget : h≤a
  rounds : v.schedule.rounds≤t
  depth : v.schedule.height≤h
  live : Fintype.card (Vertex v.circuit)≤v.hosts
  hosts : v.hosts≤2^a
  sized : v.circuit.size+1≤2^a
  copies : v.schedule.copies≤2^a
  radix : v.schedule.radix=2^v.k
  dates : v.steps.length≤2^a
  seats : seatBill v.steps≤2^a
  digits : 2*digitsNeeded (v.width G)≤h
  table : DescentExteriorShelf.tableBits v.j v.rest (v.width G)≤h/2
  split : v.schedule.copies=2^(v.j+(v.j+v.rest))
  appendix : v.appendix.words (ExteriorCount v.circuit*2^(v.j+v.rest))≤2^a

theorem base_words (h a : ℕ) (data : v.Purchased G t h a) (large : 10≤h)
    (pr : 2*unit G.C≤h/2) : v.base G h≤2^(16+3*a):=by
  have first:=public_front_words v.circuit v.schedule.copies (v.width G) h G.C v.steps v.j v.rest a
    large data.budget data.sized data.copies data.dates data.seats data.digits pr data.table data.split
  have second:=data.appendix
  have lower : 2^a≤2^(12+3*a):=Nat.pow_le_pow_right (by decide) (by omega)
  have one : 0<2^(12+3*a):=Nat.two_pow_pos _
  let r:=grain (h/2) G.C
  let lo:=selectorBase v.circuit v.schedule.copies (v.width G) h v.steps.length
  have slots (ss:List (Source v.labels)) :
      (ss.map (fun e=>DescentPackedProfileTape.slots e.seats r)).sum≤ seatBill ss+2*ss.length:=by
    induction ss with
    | nil=>simp [seatBill]
    | cons s ss ih=>
      simp only [List.map_cons,List.sum_cons,List.length_cons,seatBill,DescentPackedProfileTape.slots] at *
      have :=Nat.div_le_self s.seats r
      omega
  have counted:=output_rows r lo 0 v.steps
  have rows : ((shelves r lo 0 v.steps).map (stepRows r)).sum≤5*2^a:=by
    have rowBudget:=slots v.steps
    have :=data.seats
    have :=data.dates
    omega
  change _+_+((shelves r lo 0 v.steps).map (stepRows r)).sum+2≤_
  change v.appendix.words (ExteriorCount v.circuit*2^(v.j+v.rest))≤_ at second
  rw [show 16+3*a=12+3*a+4 by omega,Nat.pow_add 2 (12+3*a) 4]
  omega
end Input

/-- The exponent is chosen before the varying schedule, both cutoff parameters,
the circuit, the word-width multiplier, the public row menu and every assignment. -/
theorem common (M : ℕ) :
    ∃K : ℕ,∀ᶠ h in atTop,∀v : Input F,v.Purchased G t h (M*h) → v.floor G op t f g drift h≤2^(K*h) :=by
  let ι:=fun h:ℕ=>{v:Input F // v.Purchased G t h (M*h)}
  let get:=fun (h:ℕ) (v:ι h)=>v.val
  have origin : Bounded (fun h (v:ι h)=>(get h v).base G h):=by
    refine ⟨16+3*M,?_⟩
    filter_upwards [eventually_ge_atTop (max 10 (4*unit G.C))] with h high
    intro v
    have wh : 10≤h:=le_trans (le_max_left ..) high
    have pr : 2*unit G.C≤h/2:=by have :=le_trans (le_max_right ..) high;omega
    apply (v.val.base_words G t h (M*h) v.property wh pr).trans
    apply Nat.pow_le_pow_right (by decide)
    have :=Nat.le_mul_of_pos_right 16 (by omega : 0<h)
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  let S:=fun h (v:ι h)=>(get h v).schedule
  let k:=fun h (v:ι h)=>(get h v).k
  have copies : Bounded (fun h (v:ι h)=>(S h v).copies):=⟨M,Eventually.of_forall fun _ v=>v.property.copies⟩
  have hosts : Bounded (fun h (v:ι h)=>(get h v).hosts):=⟨M,Eventually.of_forall fun _ v=>v.property.hosts⟩
  have vertices:=hosts.of_le (fun h v=>v.property.live)
  have old:=vertices.of_le (fun h v=>show Fintype.card (Old (get h v).circuit)≤Fintype.card (Vertex (get h v).circuit) from
    Fintype.card_le_of_embedding ⟨Sum.inl,Sum.inl_injective⟩)
  have bits (h) (v:ι h): (S h v).copies=(S h v).groupCount 0*2^(k h v):=by
    simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr ((S h v).initialDigits v.property.radix)
  have groups : Bounded (fun h (v:ι h)=>(S h v).groupCount 0):=
    copies.of_le (fun h v=>by rw [bits h v];exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  have blocks : Bounded (fun h (v:ι h)=>2^(k h v)):=by
    apply (Bounded.const 2).mul copies |>.of_le
    intro h v
    have positive : 0<(S h v).copies:=by rw [v.property.split];exact Nat.two_pow_pos _
    have pp:=bits h v
    have gp : 0<(S h v).groupCount 0:=by by_contra! z;rw [Nat.eq_zero_of_le_zero z,Nat.zero_mul] at pp;omega
    exact (Nat.le_mul_of_pos_left _ gp).trans (by rw [←pp];omega)
  have native : ∀ᶠ h in atTop,∀_ : ι h,h≤1*h:=Eventually.of_forall (by simp)
  have dims:=selected_rates G op S (fun h _=>h) k (fun h v=>(get h v).tail) (fun _ _=>g) (fun h v=>(get h v).p)
    (fun _ _=>drift) (fun h v=>(get h v).degree) (fun _ _=>f) (fun _ _=>quota t) (fun h v=>(get h v).base G h)
    (fun h v=>(S h v).censusBits (get h v).p) (fun h v=>(get h v).wire) (fun h v=>(get h v).hist)
    (fun h v=>(S h v).grainAt G.b (get h v).p 0) t 1 (Eventually.of_forall fun _ v=>v.property.rounds)
    (Eventually.of_forall fun _ v=>v.property.depth) native
  have first:=seeded_rate origin vertices hosts groups dims.1 dims.2.1 blocks dims.2.2.1
  obtain ⟨K,ready⟩:=role_rate first old hosts groups copies blocks
    ((Bounded.pow_of_linear native).of_le (fun _ _=>Nat.lt_two_pow_self.le)) dims.2.2.2.1 ⟨1,native⟩ ⟨1,dims.2.2.2.2⟩
  exact ⟨K,ready.mono fun h ok v hv=>ok ⟨v,hv⟩⟩

end
end Hierarchy.DescentDatedSeedStartup.SeedHeader

end OAI
