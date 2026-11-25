import OAI.Hierarchy.DescentTerminalIssuedPrivateCount
import OAI.Hierarchy.DescentTerminalMaskAllocation

namespace OAI
/-! # The distinct-private-word scan reads the three reached scalar channels -/
namespace Hierarchy.DescentTerminalPrivateSourceChannels
open DescentTerminalVertexFields DescentTerminalChronologicalBooks DescentKernelHistory DescentSIMDLookup
open DescentTerminalSiteShelves DescentTerminalRecipeRows DescentTerminalIssuedPrivateCount
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- Source order of the private-count lookup. -/
def family : Fin 3→Fin 8 := ![3,6,7]

theorem low_digit (a d n : ℕ) {groups:ℕ} (g:Fin groups) (width:a*groups≤d) :
    digit a g.val (n%2^d)=digit a g.val (n%2^(a*groups)) := by
  rw [←digit_clip a (n%2^d) g,Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 width)]

variable {q t H N A p groups blocks shops wb d : ℕ}
    (source:Fin 3→Bank) (channels:MaskAllocation.Channels blocks) (maskBase:ℕ) (m:Memory wb)
    (b:Fin blocks) (i:Fin shops) (g:Fin groups)
local notation "fieldSize" => familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p)
local notation "machine" => MaskAllocation.shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) channels maskBase
local notation "meas" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)
local notation "cell" => cellAt (meas machine m i) (finProdFinEquiv (g,b))
local notation "chunk" => observed (d:=d) source m (Fin.val (finProdFinEquiv (b,i)))
variable (placed:∀f,(channels.primitive b (family f)).base=(source f).base+b.val*shops)
    (capacity:∀f,shops≤(channels.primitive b (family f)).size)
    (room:shops≤2^wb)
    (covers : ∀ f : Fin 3,
      familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (family f) * groups ≤ d)

include placed capacity room covers in
/-- Masking the complete grouped source down to the lookup input width preserves
the selected group's field, even if the physical RAM word has arbitrary high bits. -/
theorem group_read (f:Fin 3) :
    (cell (family f)).val=digit (fieldSize (family f)) g.val (chunk f).val := by
  have addr:(source f).base+b.val*shops+i.val=(source f).base+(finProdFinEquiv (b,i)).val := by
    change _=(source f).base+(i.val+shops*b.val)
    ring
  rw [cell_digit, measured_channel]
  change digit (fieldSize (family f)) g.val
      (((channels.bank (finProdFinEquiv (b,(family f).succ))).read m (i.val:Computability.VPVNP.BurstRAM.Word wb)).val %
        2^(fieldSize (family f)*groups)) =
    digit (fieldSize (family f)) g.val ((m ((source f).base+(finProdFinEquiv (b,i)).val)).val % 2^d)
  rw [MaskAllocation.Channels.primitive_at,Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le room),
    Nat.mod_eq_of_lt (i.isLt.trans_le (capacity f)),placed,addr]
  exact (low_digit _ d _ g (covers f)).symm

include placed capacity room covers in
theorem nodes_read : nodes N chunk g.val=venueField cell nodeCount := by
  have cap: (cell 3).val<2^(Nat.clog 2 (N+1)):=by
    have limit: (cell 3).val<2^(1*Nat.clog 2 (N+1)) := (cell 3).isLt
    simpa only [Nat.one_mul] using limit
  have seen := group_read (q := q) (t := t) (H := H) (N := N) (A := A) (p := p)
    source channels maskBase m b i g placed capacity room covers (0 : Fin 3)
  change (cell 3).val=digit (1*Nat.clog 2 (N+1)) g.val (chunk 0).val at seen
  rw [Nat.one_mul] at seen
  rw [venue_digit]
  change digit (Nat.clog 2 (N+1)) g.val (chunk 0).val=digit (Nat.clog 2 (N+1)) 0 (cell 3).val
  rw [←seen]
  simp [digit,Nat.mod_eq_of_lt cap]

include placed capacity room covers in
theorem argc_read (u:Fin N) : argc N A chunk g.val u=venueField cell (nodeArity u) := by
  rw [venue_digit]
  exact congrArg (digit (Nat.clog 2 (A+1)) u.val)
    (group_read source channels maskBase m b i g placed capacity room covers (1:Fin 3)).symm

include placed capacity room covers in
theorem arg_read (u:Fin N) (j:Fin A) : arg q H chunk g.val u j=venueField cell (nodeArg u j) := by
  rw [venue_digit]
  exact congrArg (digit (Nat.clog 2 (q+H+1)) (finProdFinEquiv (u,j)).val)
    (group_read source channels maskBase m b i g placed capacity room covers (2:Fin 3)).symm

/-- The address fit of the actual private-count frame supplies the cast bound
for every host index of a populated block. -/
theorem host_room {base:ℕ} (ok:DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (b:Fin blocks) : shops≤2^wb := by
  have more:shops≤blocks*shops:=by simpa using Nat.mul_le_mul_right shops (Nat.succ_le_of_lt (Nat.zero_lt_of_lt b.isLt))
  have stop:=ok.limit
  omega

variable (site:Site) (r:∀v:Fin site.nodes,Recipe (Fin t) (Fin (site.arity v))) (birth:Birth r)
    (hN:∀v,Fintype.card (r v).Node≤N) (hA:∀v u,(r v).arity u≤A) (v:Fin site.nodes)
local notation "nr" => fun u=>Fin.castLE (hN v) (ordinal (birth.atom v) u)

include placed capacity covers in
/-- The same RAM state supplies every required active input to the private count.
The previous population, arity and operand publications can be used independently. -/
theorem receipts {base:ℕ} (ok:DescentTerminalPointerFrame.Room source base d (blocks*shops) wb)
    (population:venueField cell nodeCount=Fintype.card (r v).Node)
    (lengths:∀u,venueField cell (nodeArity (nr u))=(r v).arity u)
    (refs:∀u (j:Fin ((r v).arity u)),venueField cell (nodeArg (nr u) (j.castLE (hA v u)))=
      ((r v).operand u j).elim (fun x=>x.val+1) (fun x=>q+(ordinal (birth.hidden v) x).val+1)) :
    Receipts (q:=q) (hid:=H) site r birth hN hA v chunk g.val := by
  have host:=host_room source ok b
  exact ⟨(nodes_read source channels maskBase m b i g placed capacity host covers).trans population,
    fun u=>(argc_read source channels maskBase m b i g placed capacity host covers (nr u)).trans (lengths u),
    fun u j=>(arg_read source channels maskBase m b i g placed capacity host covers (nr u) (j.castLE (hA v u))).trans (refs u j)⟩


end
end Hierarchy.DescentTerminalPrivateSourceChannels

end OAI
