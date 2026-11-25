import OAI.Hierarchy.DescentPublicOperandDateTables

namespace OAI
/-! # Physical output rows expressed with the original board and actual operand packet -/
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



/-- The cast is only a change of the public field-width index. All cell values originate in
the mounted donor/auxiliary/control banks. -/
def publicData {H G} (values : (ports).Values H G)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (g₀ : Fin G) :
    (cfg).Data (v).middle.rotorBits :=
  fun i=>(menu.publicRow sh floor count hub g Y active reg values digits x h g₀ (i.cast (idx).symm)).cast
      (congrArg (2^·) menu.wordSize)

theorem publicData_val {H G} (values : (ports).Values H G)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (g₀ : Fin G)
    (j : Fin ((cfg).inputs (v).middle.rotorBits)) :
    (menu.publicData sh floor count hub g Y active reg values digits x h g₀ j).val=
      ((ports).value values x h g₀ ((cfg).port j)).val :=by
  have back : (j.cast (idx).symm).cast idx=j:=Fin.ext rfl
  simp only [publicData, publicRow, back]
  rfl

theorem public_columns {H G w} (values : (ports).Values H G) (m : Memory w)
    (digits : (ports).casts.bits=(C).fallbackBits) (lanes : (ports).casts.lanes=(C).lanes)
    (ready : (C).Ready (banks w) w base) (space : (C).endAddress base<2^w)
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j x lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j x lo
      t.Fits w base ∧ Source t (values.coord j x lo) (ports).casts.lanes m)
    (packet : ∀f j x,let t:=(ports).packets.src (ports).packetBase f j x
      t.Fits w (ports).castBase ∧ Source t (values.packet f j x) (ports).casts.lanes ((C).packetMemory base (banks w) m))
    (live : active.Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (registers : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (x : ℕ) (arg : Fin (C).retained.args) (node : Fin (C).retained.nodes) :
    let final:=((C).code base w (banks w) menu.tables).image m
    let src:=menu.publicInput sh floor count hub g Y active reg x
    let payload:=menu.publicData sh floor count hub g Y active reg values digits x
    let mouth:=finProdFinEquiv (arg,node)
    (let e:=DescentOperandFamilyBook.expr menu.tables.fallbackQuery (C).lanes ((C).fallbackQuery base) mouth src
     e.Fits w ((C).endAddress base) ∧
       Source e (fun h g₀=>(cfg).column z.board (C).queryBits none mouth (payload h g₀)) (C).lanes final) ∧
    (∀f : Fin 7,let e:=DescentOperandFamilyBook.expr menu.tables.fallbackFields (C).lanes ((C).fallbackFields base) (finProdFinEquiv (f,mouth)) src
       e.Fits w ((C).endAddress base) ∧
       Source e (fun h g₀=>(cfg).column z.board (C).fieldBits (some f) mouth (payload h g₀)) (C).lanes final) :=by
  have rows:=public_tables menu sh floor count hub g Y active reg values m digits lanes ready space aux coords packet live registers x
  let fmt : (C).Format (n:=(v).middle.rotorBits) cfg:=⟨rfl,rfl,rfl,menu.wordSize,menu.publicInputIndex⟩
  let mouth : Fin (C).members:=finProdFinEquiv (arg,node)
  constructor
  · exact rows.1 mouth
  · intro f
    have r:=rows.2 (finProdFinEquiv (f,mouth))
    refine ⟨r.1,?_⟩
    have eqn : (fun h g₀=>menu.tables.fallbackFields (finProdFinEquiv (f,mouth))
        (menu.publicRow sh floor count hub g Y active reg values digits x h g₀)) =
          (fun h g₀=>(cfg).column z.board (C).fieldBits (some f) mouth
            (menu.publicData sh floor count hub g Y active reg values digits x h g₀)) :=by
      funext h g₀
      exact (fmt.fields z.board f mouth (fun _=>0)
        (menu.publicRow sh floor count hub g Y active reg values digits x h g₀)).2
    rw [←eqn]
    exact r.2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
