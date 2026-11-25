import OAI.Hierarchy.DescentVenueQuantityState
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! The receiver's occurrence bit controls every register in its private and public
operand decoders. The coarse depth is the previously measured Walsh depth. -/
namespace Hierarchy.DescentResetControlRegisters
open DescentSIMDLookup DescentVenueQuantityPlanes ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Chart where
  dims : Dims
  bits : ℕ

namespace Chart
variable (c : Chart)
local notation "M" => c.dims.lanes
local notation "S" => c.dims.shapes
local notation "raw" => c.dims.oldHosts*S
local notation "rows" => c.dims.hosts*chunks c.dims.groups M

def span (n : ℕ) :=2^Nat.clog 2 n
def bank (base n : ℕ) : Bank:=⟨base,Nat.clog 2 n⟩
def first (base : ℕ) := State.roof c.dims base
def oldHost (base : ℕ) :=c.first base+span rows
def shape (base : ℕ) :=c.oldHost base+span raw
def scale (base : ℕ) :=c.shape base+span raw
def table (base : ℕ) :=c.scale base+2^c.bits
def endAddress (base : ℕ) :=c.table base+2^(c.bits+M)
def count :=span rows+span raw+span raw+2^c.bits+2^(c.bits+M)

theorem size (base : ℕ) : c.endAddress base=c.first base+c.count:=by
  simp [endAddress,table,scale,shape,oldHost,count,Nat.add_assoc]
theorem translated (base : ℕ) : c.endAddress base=base+c.endAddress 0:=by
  rw [c.size base,c.size 0]
  unfold first
  rw [State.shift]
  omega

/-- A short scalar replicated only on genuinely occupied lanes. -/
def masked (index : ℕ) : ℕ :=
  let mask : Cell (1*M) := (index % 2^M : ℕ)
  let val : Cell c.bits := (index / 2^M : ℕ)
  (encode c.bits M fun j=>if (encode 1 M).symm mask j=0 then 0 else val).val

def literal (i : ℕ) : ℕ :=
  if _h:i<span rows then i/chunks c.dims.groups M
  else let j:=i-span rows
       if j<span raw then j/S
       else let k:=j-span raw
            if k<span raw then k%S
            else let t:=k-span raw
                 if t<2^c.bits then t*2^M else c.masked (t-2^c.bits)

def hostId (base : ℕ) (inverse : Bank) : Expr:=
  .lookup inverse (.lookup (bank (c.first base) rows) .row)

def active (base x : ℕ) : Expr :=
  .lookup (bank (State.out c.dims base+x*rows) rows) .row

def broadcast (base x : ℕ) (scalar : Expr) : Expr :=
  .lookup ⟨c.table base,c.bits+M⟩ (.op .add (.lookup ⟨c.scale base,c.bits⟩ scalar) (c.active base x))

def live (base x : ℕ) :=c.broadcast base x (.lit 1)
def ports (base cap x : ℕ) (inverse depth levels : Bank) : Fin 4→Expr
  | 0=>c.broadcast base x (.lit cap)
  | 1=>c.broadcast base x (.lookup levels (.lookup depth (.lookup (bank (c.oldHost base) raw) (c.hostId base inverse))))
  | 2=>.lit 0
  | 3=>c.broadcast base x (.lookup (bank (c.shape base) raw) (c.hostId base inverse))


end Chart
end
end Hierarchy.DescentResetControlRegisters

end OAI
