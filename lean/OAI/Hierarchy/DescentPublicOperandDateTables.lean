import OAI.Hierarchy.DescentPublicOperandBankRead

namespace OAI
/-! # Query and all seven operand fields from the preceding date's public inputs -/
namespace Hierarchy.DescentResetOperandSetup.Chart.Format
open DescentSIMDLookup DescentResetPublicOperandBook
noncomputable section
variable {C : DescentResetOperandSetup.Chart} {p : Config} {n h : ℕ}
  (fmt : C.Format (n:=n) p) (board : NonlinearExpanders.Graph n h)

theorem publicColumn_zero (width : ℕ) (f : Option (Fin 7)) (j : Fin C.members) :
    fmt.publicColumn board width (fun _=>0) f j=0 :=by
  have empty : (fun i : Fin (p.inputs n)=>((0 : Cell C.fallbackBits).cast
      (congrArg (2^·) fmt.publicWidth)))=(fun _=>0) :=by
    funext i
    apply Fin.ext
    simp
  unfold publicColumn
  rw [empty]
  simp [Config.column,Config.mixed,DescentFallbackOperandBranch.Config.header,Config.basic]

end
end Hierarchy.DescentResetOperandSetup.Chart.Format

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


private theorem cast_read {a b M N H G w : ℕ} {e : Expr} {m : Memory w}
    {x : Fin H→Fin G→Cell a} (bits : a=b) (lanes : M=N) (r : Source e x M m) :
    Source e (fun h g=>(x h g).cast (congrArg (2^·) bits)) N m :=by
  subst b
  subst N
  exact r

def publicRow {H G} (values : (ports).Values H G)
    (digits : (ports).casts.bits=(C).fallbackBits) (x : ℕ) (h : Fin H) (g₀ : Fin G)
    (j : Fin (C).fallbackInputs) : Cell (C).fallbackBits :=
  ((ports).value values x h g₀ ((cfg).port (j.cast idx))).cast (congrArg (2^·) digits)

theorem public_tables {H G w} (values : (ports).Values H G) (m : Memory w)
    (digits : (ports).casts.bits=(C).fallbackBits) (lanes : (ports).casts.lanes=(C).lanes)
    (ready : (C).Ready (banks w) w base) (space : (C).endAddress base<2^w)
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j x lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j x lo
      t.Fits w base ∧ Source t (values.coord j x lo) (ports).casts.lanes m)
    (packet : ∀f j x,let t:=(ports).packets.src (ports).packetBase f j x
      t.Fits w (ports).castBase ∧ Source t (values.packet f j x) (ports).casts.lanes ((C).packetMemory base (banks w) m))
    (live : active.Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (registers : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (x : ℕ) :
    let final:=((C).code base w (banks w) menu.tables).image m
    let src:=menu.publicInput sh floor count hub g Y active reg x
    let row:=menu.publicRow sh floor count hub g Y active reg values digits x
    (∀j,let e:=DescentOperandFamilyBook.expr menu.tables.fallbackQuery (C).lanes ((C).fallbackQuery base) j src
        e.Fits w ((C).endAddress base) ∧
        Source e (fun h g₀=>menu.tables.fallbackQuery j (row h g₀)) (C).lanes final) ∧
    (∀j,let e:=DescentOperandFamilyBook.expr menu.tables.fallbackFields (C).lanes ((C).fallbackFields base) j src
        e.Fits w ((C).endAddress base) ∧
        Source e (fun h g₀=>menu.tables.fallbackFields j (row h g₀)) (C).lanes final) :=by
  let fmt : (C).Format (n:=(v).middle.rotorBits) cfg:=
    ⟨rfl,rfl,rfl,menu.wordSize,menu.publicInputIndex⟩
  have prior:=public_input_prefix menu sh floor count hub g Y active reg values m ready space aux coords packet live registers x
  exact (C).public_pages base (banks w) menu.tables m space _
    (menu.publicRow sh floor count hub g Y active reg values digits x)
    (fun i=>(prior i).1) (fun i=>cast_read digits lanes (prior i).2)
    (fun j=>fmt.publicColumn_zero z.board _ none j)
    (fun j=>fmt.publicColumn_zero z.board (C).fieldBits (some (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
