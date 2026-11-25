import OAI.Hierarchy.DescentPhysicalPublicOperandInputs

namespace OAI
/-! # The three public conversions and the joint operand lookup share the actual rendered reset memory -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {w : ℕ}

/-- Snapshot immediately after the two different prepared root packets have been physically pulled. -/
def packetMemory (base : ℕ) (s : C.Sources) (m : Memory w) : Memory w :=
  (C.packets.image (C.placed base)) ((C.sources base w s).image m)

theorem public_snapshots (base : ℕ) (s : C.Sources) (f : C.Laws) (m : Memory w)
    (ready : C.Ready s w base) (space : C.endAddress base<2^w) :
    base≤C.packetEnd base ∧ C.publicEnd base≤C.endAddress base ∧
    (∀i,i<base→C.packetMemory base s m i=m i) ∧
    (∀i,i<C.publicEnd base→(C.code base w s f).image m i=
      C.publicCasts.image (C.packetEnd base) (C.packetMemory base s m) i) ∧
    (∀i,i<base→(C.code base w s f).image m i=m i) := by
  obtain ⟨a,b,c⟩:=C.before base
  have first:=((a.trans b).trans c).trans ((C.packets.join (C.placed base)).1.trans (C.packets.join (C.placed base)).2)
  change base≤C.packetEnd base at first
  have mid : C.packetEnd base≤C.publicEnd base:=Nat.le_add_right ..
  obtain ⟨l₀,l₁,l₂,l₃,l₄,l₅,l₆,l₇⟩:=C.order base
  have last : C.publicEnd base≤C.endAddress base:=by omega
  let pre:=C.packetMemory base s m
  let widened:=C.publicCasts.image (C.packetEnd base) pre
  have run:=C.any base m s f ready space
  have preRun:=C.publicCasts.any (C.packetEnd base) pre (last.trans_lt space)
  have control:=C.control_run base widened f space
  have lower (j : ℕ) (hj : j<C.publicEnd base) : (C.code base w s f).image m j=widened j :=
    control.frame j (.inl hj)
  refine ⟨first,last,?_,lower,fun j hj=>run.frame j (.inl hj)⟩
  intro j hj
  exact ((preRun.2.2 j (.inl (hj.trans_le first))).symm.trans (lower j ((hj.trans_le first).trans_le mid)).symm).trans
    (run.frame j (.inl hj))

end
end Hierarchy.DescentResetOperandSetup.Chart

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
set_option quotPrecheck false
local notation "v" => a.successor
local notation "C" => (v).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation "banks" w => menu.banks sh floor count hub g Y w
local notation "base" => (v).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload
local notation "idx" => menu.publicInputIndex

/-- Earlier halo and coordinate rows are held across the pull. The two packets are read in their
installed compact order at that exact pull. The later dictionary phases preserve all three casts. -/
theorem public_input_prefix {H G w} (values : (ports).Values H G) (m : Memory w)
    (ready : (C).Ready (banks w) w base) (space : (C).endAddress base<2^w)
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j x lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j x lo
      t.Fits w base ∧ Source t (values.coord j x lo) (ports).casts.lanes m)
    (packet : ∀f j x,let t:=(ports).packets.src (ports).packetBase f j x
      t.Fits w (ports).castBase ∧ Source t (values.packet f j x) (ports).casts.lanes ((C).packetMemory base (banks w) m))
    (live : active.Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (registers : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (x : ℕ) (j : Fin (C).fallbackInputs) :
    let e:=menu.publicInput sh floor count hub g Y active reg x j
    e.Fits w ((C).publicEnd base) ∧
      Source e (fun h g₀=>(ports).value values x h g₀ ((cfg).port (j.cast idx)))
        (ports).casts.lanes (((C).code base w (banks w) menu.tables).image m) :=by
  let pre:=(C).packetMemory base (banks w) m
  let final:=((C).code base w (banks w) menu.tables).image m
  obtain ⟨first,last,archive,widened,original⟩:=(C).public_snapshots base (banks w) menu.tables m ready space
  have middle : (C).packetEnd base≤(C).publicEnd base:=Nat.le_add_right ..
  have saved {b : ℕ} (e : Expr) {f : Fin H→Fin G→Cell b} {stop : ℕ} {dst : Memory w}
      (fit : e.Fits w base) (source : Source e f (ports).casts.lanes m)
      (bound : base≤ stop) (keep : ∀i,i<base→dst i=m i) :
      e.Fits w stop ∧ Source e f (ports).casts.lanes dst :=by
    refine ⟨ProtocolRAMGeneratedWrite.fits_mono e bound fit,?_⟩
    intro q
    exact (eval_below e _ m dst fit keep).trans (source q)
  have previous : (ports).RawPrior values pre :=
    ⟨fun e=>saved _ (aux e).1 (aux e).2 first archive,
      fun i x d=>saved _ (coords i x d).1 (coords i x d).2 first archive,packet⟩
  exact (ports).public_late values pre final previous (last.trans_lt space) le_rfl widened
    (saved _ live.1 live.2 (first.trans middle) original)
    (fun i=>saved _ (registers i).1 (registers i).2 (first.trans middle) original)
    x ((cfg).port (j.cast idx))

theorem public_input_read {H G w} (values : (ports).Values H G) (m : Memory w)
    (ready : (C).Ready (banks w) w base) (space : (C).endAddress base<2^w)
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j x lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j x lo
      t.Fits w base ∧ Source t (values.coord j x lo) (ports).casts.lanes m)
    (packet : ∀f j x,let t:=(ports).packets.src (ports).packetBase f j x
      t.Fits w (ports).castBase ∧ Source t (values.packet f j x) (ports).casts.lanes ((C).packetMemory base (banks w) m))
    (live : active.Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (registers : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (x : ℕ) (j : Fin (C).fallbackInputs) :
    let e:=menu.publicInput sh floor count hub g Y active reg x j
    e.Fits w ((C).endAddress base) ∧
      Source e (fun h g₀=>(ports).value values x h g₀ ((cfg).port (j.cast idx)))
        (ports).casts.lanes (((C).code base w (banks w) menu.tables).image m) :=by
  have r:=public_input_prefix menu sh floor count hub g Y active reg values m ready space aux coords packet live registers x j
  have stop:=((C).public_snapshots base (banks w) menu.tables m ready space).2.1
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ stop r.1,r.2⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
