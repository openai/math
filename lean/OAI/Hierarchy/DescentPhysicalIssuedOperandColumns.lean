import OAI.Hierarchy.DescentPhysicalSelectedDigits
import OAI.Hierarchy.DescentRecordedPrivateColumns
import OAI.Hierarchy.DescentResetConvertedOld
import OAI.Hierarchy.DescentPhysicalOperandBounds

namespace OAI
/-! Read both output channels from the same physically installed reset operand menu. -/
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
local notation "banks" w:arg => menu.banks sh floor count hub g Y w
local notation "base" => (v).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload

local notation "H" => (C).placement.newHosts
local notation "G" => (C).placement.groups
local notation "R" => (C).retained
variable {w U : ℕ} (m : Memory w) (values : (publicPorts (a:=a) sh floor count hub g Y active reg).Values a.successor.setup.placement.newHosts a.successor.setup.placement.groups)
variable (digits : (publicPorts (a:=a) sh floor count hub g Y active reg).casts.bits=a.successor.setup.fallbackBits) (lanes : (publicPorts (a:=a) sh floor count hub g Y active reg).casts.lanes=a.successor.setup.lanes)
variable (x : Fin a.successor.setup.placement.blocks) (arg : Fin a.successor.setup.retained.args) (n : Fin a.successor.setup.retained.nodes)
variable (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (hostEq : a.successor.setup.placement.oldHosts=a.successor.setup.retained.hosts) (groupEq : a.successor.setup.placement.groups*a.successor.setup.placement.blocks=a.successor.setup.retained.grouped)
variable (X : a.successor.setup.seven.Packets) (strips : a.successor.setup.retained.Strips)
local notation "s" => banks w
local notation "Ys" => (C).assignedDigits hostEq groupEq (s).which X strips
variable (signed : Fin a.successor.setup.strip→Fin a.successor.setup.placement.oldHosts→Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.signedBits)
variable (hubWord : Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell a.successor.setup.fieldBits) (tickets : Fin a.successor.setup.strip→Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→Cell a.successor.setup.fieldBits)
local notation "raw" => (C).carriedRow (s) name (Ys) signed x arg n hubWord tickets
local notation "payload" => menu.publicData sh floor count hub g Y active reg values digits x.val
local notation "at_" => (finProdFinEquiv (arg,n) : Fin (C).members)
local notation "dst" => ((C).code base w (s) menu.tables).image m
local notation "pubSrc" => menu.publicInput sh floor count hub g Y active reg x.val
local notation "oldCell" f:arg h:arg k:arg => ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  (s).primary name (Ys) ((R).outputID 1 f arg n) x h k).val : Cell (C).fieldBits)
local notation "rot" width:arg f:arg h:arg k:arg => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
   n.val arg.val f ((cfg).reg ((payload) h k)) : Cell width)
local notation "pub" width:arg f:arg h:arg k:arg => (cfg).column z.board width f at_ ((payload) h k)

include lanes in
theorem request_columns (ready : (C).Ready (s) w base) (room : (C).endAddress base<2^w)
    (moved : (C).Moved base (s) name (((C).sources base w (s)).image m) (Ys) signed)
    (mark : Expr) (fee : Fin (C).strip→Expr)
    (marked : mark.Fits w ((C).casts base) ∧ Source mark hubWord (C).lanes dst)
    (dated : ∀j,(fee j).Fits w ((C).casts base) ∧ Source (fee j) (tickets j) (C).lanes dst)
    (aux : ∀j,((ports).aux j).Fits w base ∧ Source ((ports).aux j) (values.aux j) (ports).casts.lanes m)
    (coords : ∀j x lo,let t:=(ports).coordinates.src (ports).coordinateBase (ports).saved j x lo
      t.Fits w base ∧ Source t (values.coord j x lo) (ports).casts.lanes m)
    (packet : ∀f j x,let t:=(ports).packets.src (ports).packetBase f j x
      t.Fits w (ports).castBase ∧ Source t (values.packet f j x) (ports).casts.lanes ((C).packetMemory base (s) m))
    (live : active.Fits w base ∧ Source active values.active (ports).casts.lanes m)
    (regs : ∀j,(reg j).Fits w base ∧ Source (reg j) (values.register j) (ports).casts.lanes m)
    (blank : ∀h k,((cfg).oldConfig.header ((cfg).basic ((payload) h k)) 0).val=0 →
      ((cfg).reg ((payload) h k) 1).val=0)
    (label : ∀h k (hv:h.val<U),((cfg).oldConfig.header ((cfg).basic ((payload) h k)) 0).val≠0 →
      ((cfg).reg ((payload) h k) 3).val=((C).placement.shape (name ⟨h.val,hv⟩)).val)
    (two : 2<2^(C).fieldBits) :
    let carried:=(C).carried base x arg n mark fee
    (Source ((C).selected base menu.tables none x arg n carried reg pubSrc)
      (fun h k=>queryDigit (a:=a) ((C).cable.query ((raw) h k)) (rot (C).queryBits 0 h k)
        (pub (C).queryBits none h k)) (C).lanes dst) ∧
    ∀f : Fin 7, Source ((C).selected base menu.tables (some f) x arg n carried reg pubSrc)
      (fun h k=>(((oldCell f h k).val+((C).cable.priceField f ((raw) h k)).val+
        (rot (C).fieldBits f.succ h k).val+(pub (C).fieldBits (some f) h k).val:ℕ) : Cell (C).fieldBits))
      (C).lanes dst:=by
  have public_:=menu.public_columns sh floor count hub g Y active reg values m digits lanes ready room
    aux coords packet live regs x.val arg n
  have private_:=menu.private_columns sh floor count hub g Y active reg values m digits lanes ready room regs x.val arg n
  have previous:=(C).carried_source base (s) menu.tables m room ready name (Ys) signed x arg n hubWord tickets
    moved mark fee marked.2 (fun j=>(dated j).2)
  obtain ⟨a₀,b₀,c₀,d₀,e₀,g₀,h₀,k₀⟩:=(C).order base
  have fit:=(C).carried_fits base (show (C).casts base<2^w by omega) x arg n mark fee marked.1 (fun j=>(dated j).1)
  have tag (h k) : (C).cable.header ((raw) h k) 0=
      ((DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch menu.keep name (Ys)
        ((R).outputID 0 0 arg n) x h k).val:Cell (C).fieldBits):=rfl
  have indices : (finProdFinEquiv.symm at_ : Fin (cfg).args×Fin (cfg).nodes)=(arg,n):=Equiv.symm_apply_apply _ _
  constructor
  · apply (C).selected_query base (s) menu.tables m x arg n _ reg pubSrc raw _ _ _ room fit.1 previous
      private_.1.2 public_.1.2
    intro h k
    simpa only [indices] using menu.query_owner name ((payload) h k) at_ hostEq groupEq X strips (s).which
      x arg n h k ((raw) h k) (tag h k) (blank h k) (label h k)
  · intro f
    have prior:=(C).oldValue_source base (s) menu.tables m room name (Ys) signed moved ready x arg n f
    apply (C).selected_field base (s) menu.tables m x arg n _ reg pubSrc f raw _ _ _ _ room fit.1 previous prior
      (private_.2 f).2 (public_.2 f).2
    intro h k
    apply Nat.mod_eq_of_lt
    have primary : (s).primary = menu.keep := rfl
    simpa only [indices, primary] using menu.posted_field_room name ((payload) h k) at_ hostEq groupEq X strips (s).which
      x arg n h k ((raw) h k) (tag h k) (blank h k) (label h k) f two

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
