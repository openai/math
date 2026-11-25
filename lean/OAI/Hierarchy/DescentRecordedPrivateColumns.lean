import OAI.Hierarchy.DescentPrivateOperandBankRead
import OAI.Hierarchy.DescentResetRecordedPrimary

namespace OAI
/-! The private gate ROM reads the same four physical scalars as the public gate ROM. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 500000
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "successor" => a.successor
local notation "C" => (successor).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation "banks" w:arg => menu.banks sh floor count hub g Y w
local notation "base" => (successor).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload

private theorem transfer {u v w H G M : ℕ} {e : Expr} {mem : Memory w}
    {X : Fin H→Fin G→Cell u} {Y : Fin H→Fin G→Cell v}
    (width : u=v) (same : ∀h g,(X h g).val=(Y h g).val) (read : Source e X M mem) :
    Source e Y M mem:=by
  subst v
  have agree:X=Y:=funext (fun h=>funext (fun g=>Fin.ext (same h g)))
  rwa [←agree]

private theorem private_column_at {n d width : ℕ} {plan : Chart} {config : DescentResetPublicOperandBook.Config}
    (board : NonlinearExpanders.Graph n d) (fmt : plan.Format (n:=n) config) (mouth : Fin plan.members)
    (arg : Fin config.args) (node : Fin config.nodes) (digit : Fin 8)
    (inputs : Fin 4 → Cell plan.rotorBits) (regs : Fin 4 → Cell config.fieldBits)
    (back : mouth.cast fmt.members = finProdFinEquiv (arg,node)) (same : ∀ i, (inputs i).val = (regs i).val) :
    fmt.privateColumn board width inputs digit mouth =
      (config.rotor.flatReg board config.multiplicity config.grain config.split node.val arg.val digit regs : Cell width) := by
  let point : Fin config.args × Fin config.nodes := finProdFinEquiv.symm (mouth.cast fmt.members)
  let old : Fin 4 → Cell config.fieldBits := fun i => (inputs i).cast (congrArg (2^·) fmt.rotor)
  let read (t : Fin config.args × Fin config.nodes) (v : Fin 4 → Cell config.fieldBits) :=
    (config.rotor.flatReg board config.multiplicity config.grain config.split t.2.val t.1.val digit v : Cell width)
  have pointEq : point = (arg,node) :=
    (congrArg finProdFinEquiv.symm back).trans (finProdFinEquiv.symm_apply_apply _)
  have inputEq : old = regs := funext fun i => Fin.ext (same i)
  exact (congrArg (fun t=>read t old) pointEq).trans (congrArg (read (arg,node)) inputEq)

theorem private_columns {w H G} (values : (ports).Values H G) (m : Memory w)
    (digits : (ports).casts.bits=(C).fallbackBits) (lanes : (ports).casts.lanes=(C).lanes)
    (ready : (C).Ready (banks w) w base) (space : (C).endAddress base<2^w)
    (registers : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (x : ℕ) (arg : Fin (C).retained.args) (node : Fin (C).retained.nodes) :
    let payload:=menu.publicData sh floor count hub g Y active reg values digits x
    let final:=((C).code base w (banks w) menu.tables).image m
    let mouth:=finProdFinEquiv (arg,node)
    (let e:=DescentOperandFamilyBook.expr menu.tables.rotorQuery (C).lanes ((C).rotorQuery base) mouth reg
     e.Fits w ((C).endAddress base) ∧ Source e (fun h k=>((cfg).rotor.flatReg z.board (cfg).multiplicity
       (cfg).grain (cfg).split node.val arg.val 0 ((cfg).reg (payload h k)) : Cell (C).queryBits)) (C).lanes final) ∧
    (∀f : Fin 7,let e:=DescentOperandFamilyBook.expr menu.tables.rotorFields (C).lanes ((C).rotorFields base) (finProdFinEquiv (f,mouth)) reg
     e.Fits w ((C).endAddress base) ∧ Source e (fun h k=>((cfg).rotor.flatReg z.board (cfg).multiplicity
        (cfg).grain (cfg).split node.val arg.val f.succ ((cfg).reg (payload h k)) : Cell (C).fieldBits)) (C).lanes final):=by
  let payload:=menu.publicData sh floor count hub g Y active reg values digits x
  let val:=fun (h:Fin H) (k:Fin G) i=>(cfg).reg (payload h k) i
  let f:=(C).code base w (banks w) menu.tables
  let fmt:(C).Format (n:=(successor).middle.rotorBits) cfg:=⟨rfl,rfl,rfl,menu.wordSize,menu.publicInputIndex⟩
  have snap:=(C).public_snapshots base (banks w) menu.tables m ready space
  have order:base≤(C).publicEnd base:=
    snap.1.trans (show (C).packetEnd base≤(C).publicEnd base from Nat.le_add_right ..)
  have inputs (i) : Source (reg i) (fun h k=>val h k i) (C).lanes (f.image m):=by
    apply transfer (digits.trans menu.wordSize) (fun h k=>
      (menu.public_control_registers sh floor count hub g Y active reg values digits x h k i).symm)
    rw [←lanes]
    intro q
    exact (eval_below _ _ _ _ (registers i).1 snap.2.2.2.2).trans ((registers i).2 q)
  have qzero (j) : menu.tables.rotorQuery j (fun _=>0)=0:=by
    simp [tables,Chart.Format.laws,Chart.Format.privateColumn,DescentRotorOperandQueryROM.Shape.flatReg]
  have fzero (j) : menu.tables.rotorFields j (fun _=>0)=0:=by
    simp [tables,Chart.Format.laws,Chart.Format.privateColumn,DescentRotorOperandQueryROM.Shape.flatReg]
  have stored:=(C).private_pages base (banks w) menu.tables m space reg val
    (fun i=>ProtocolRAMGeneratedWrite.fits_mono _ order (registers i).1) inputs qzero fzero
  let mouth : Fin (C).members := finProdFinEquiv (arg,node)
  have atMouth (width : ℕ) (h : Fin H) (k : Fin G) (digit : Fin 8) :
      fmt.privateColumn z.board width (val h k) digit mouth =
        ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split node.val arg.val digit (val h k) : Cell width) := by
    exact private_column_at z.board fmt mouth arg node digit (val h k) (val h k) (Fin.ext rfl) (fun _=>rfl)
  have query:=stored.1 mouth
  constructor
  · refine ⟨query.1, transfer rfl ?_ query.2⟩
    intro h k
    exact congrArg Fin.val (atMouth _ h k 0)
  · intro digit
    have fieldResult:=stored.2 (finProdFinEquiv (digit,mouth))
    refine ⟨fieldResult.1, transfer rfl ?_ fieldResult.2⟩
    intro h k
    have selected := (fmt.«fields» z.board digit mouth (val h k) (fun _=>0)).1
    exact congrArg Fin.val (selected.trans (atMouth _ h k digit.succ))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
