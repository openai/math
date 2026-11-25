import OAI.Hierarchy.DescentTerminalResetBanks

namespace OAI
/-! # The primitive token and flat arity in the same physical reset memory -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentPackedZip DescentPrimitivePalette
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
namespace ResetOutput
variable (v : ResetOutput) (base : ℕ)
def terminalArity (x : Fin v.metadata.chart.blocks) : Bank :=
  let md:=v.metadata
  md.chart.bank (md.chart.inputsEnd (v.primitiveEnd base) md.paidBits md.spanBits) 1 x

theorem terminal_arity_room {w : ℕ} (room : v.metadataEnd base<2^w) (x : Fin v.metadata.chart.blocks) :
    (v.terminalArity base x).Fits w (v.metadataEnd base) ∧ v.metadata.chart.rows ≤ (v.terminalArity base x).size :=
  v.metadata.chart.valid _ room 1 x
end ResetOutput

namespace PhysicalReset.FinalInputs
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "pr" => (v).primitive
local notation "c" => (pr).chart
local notation "md" => (v).metadata
local notation "c₁" => (md).chart
local notation "born" => (v).birthEnd b
local notation "meta" => (v).primitiveEnd b
local notation "G" => z.menu.gadget
local notation "s" => z.menu.stageBits
local notation "Z" => z.menu.grain
local notation "op" => z.menu.op
local notation "t" => printedBits G s Z op

def tokenImage (entry : Memory w) := (pr).finalMem G s Z op born z.roles entry
def terminalImage (entry : Memory w) :=
  (c₁).metadataImage meta (md).paidBits (md).spanBits (paid u) z.spans (z.tokenImage entry)

theorem role_arity_at (fit : z.Room) (entry : Memory w)
    (bits : (c).bits=t)
    (cells : Fin (c).blocks→Fin (c).nodes→Fin (c).hosts→Fin (c).groups→PrintedInput t)
    (small : ∀x n h g,DescentResetPrimitivePage.localRole (cells x n h g)<2^(pr).rawBits)
    (retained : ∀x n,Source (z.roles.retained x n) (fun h g=>DescentResetPrimitivePage.oldWord (cells x n h g)) (c).lanes entry)
    (fresh : ∀x n,Source (z.roles.fresh x n) (fun h g=>(DescentResetPrimitivePage.localRole (cells x n h g):Cell (pr).rawBits)) (c).lanes entry)
    (relay : ∀x n,Source (z.roles.relay x n) (fun h g=>DescentResetPrimitivePage.relayFlag (cells x n h g)) (c).lanes entry)
    (amount : Fin (c₁).blocks→Fin (c₁).hosts→Fin (c₁).groups→Cell (md).paidBits)
    (sp : Fin (c₁).blocks→Fin (c₁).nodes→Fin u.operand.slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (md).spanBits)
    (arity : Fin (c₁).blocks→Fin (c₁).nodes→Fin (c₁).hosts→Fin (c₁).groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤u.operand.slots)
    (live : ∀x n j h g,sp x n j h g≠0 ↔ n.val<(amount x h g).val ∧ j.val<arity x n h g)
    (count : ∀x,Source ((paid u) x) (amount x) (c₁).lanes (z.tokenImage entry))
    (ranges : ∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.tokenImage entry)) :
    (∀x,Reads ((v).terminalRole b x) (fun h g=>encode (c).bits (c).nodes
      (fun n=>((emit G s Z op (cells x n h g)).val:Cell (c).bits))) (c).lanes (z.terminalImage entry)) ∧
    ∀x,Reads ((v).terminalArity b x) (fun h g=>encode (c₁).bits (c₁).nodes (fun n=>
      if n.val<(amount x h g).val then (arity x n h g:Cell (c₁).bits) else 0)) (c₁).lanes (z.terminalImage entry) := by
  have below:meta ≤ a.endAddress floor:=((v).terminal_order b).2.2
  have rd:=(pr).issued G s Z op born z.roles entry fit.roleFields (below.trans_lt fit.endFits)
    bits cells small retained fresh relay
  have late:=((c₁).metadataAny meta (md).paidBits (md).spanBits (paid u) z.spans (z.tokenImage entry)
    fit.count fit.spans fit.endFits).2.1
  constructor
  · intro x j
    obtain ⟨bound,size⟩:=(v).terminal_role_room b fit.endFits x
    have lo:=bound.2.2
    have rowLt : (row _ _ _ j).val<(c).rows := (row _ _ _ j).isLt
    have addr : ((v).terminalRole b x).base+(row _ _ _ j).val< meta :=by omega
    exact (late _ (.inl addr)).trans (rd x j)
  · intro x
    have read:=(c₁).metadataRead meta (md).paidBits (md).spanBits (paid u) z.spans (z.tokenImage entry)
      amount sp arity bounded live fit.count fit.spans count ranges fit.endFits 1 x
    simpa only [terminalImage, ResetOutput.terminalArity, show (1:Fin 2)≠0 by decide, ite_false] using read

/-- Observable at the final complete reset date on the same original execution. -/
theorem dated_role_arity (fit : z.Room) {before mid dst : Memory w}
    (ran : (date z).Runs before dst) (operands : u.throughOperandDate.Runs before mid)
    (bits : (c).bits=t)
    (cells : Fin (c).blocks→Fin (c).nodes→Fin (c).hosts→Fin (c).groups→PrintedInput t)
    (small : ∀x n h g,DescentResetPrimitivePage.localRole (cells x n h g)<2^(pr).rawBits)
    (retained : ∀x n,Source (z.roles.retained x n) (fun h g=>DescentResetPrimitivePage.oldWord (cells x n h g)) (c).lanes (z.roleInput mid))
    (fresh : ∀x n,Source (z.roles.fresh x n) (fun h g=>(DescentResetPrimitivePage.localRole (cells x n h g):Cell (pr).rawBits)) (c).lanes (z.roleInput mid))
    (relay : ∀x n,Source (z.roles.relay x n) (fun h g=>DescentResetPrimitivePage.relayFlag (cells x n h g)) (c).lanes (z.roleInput mid))
    (amount : Fin (c₁).blocks→Fin (c₁).hosts→Fin (c₁).groups→Cell (md).paidBits)
    (sp : Fin (c₁).blocks→Fin (c₁).nodes→Fin u.operand.slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (md).spanBits)
    (arity : Fin (c₁).blocks→Fin (c₁).nodes→Fin (c₁).hosts→Fin (c₁).groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤u.operand.slots)
    (live : ∀x n j h g,sp x n j h g≠0 ↔ n.val<(amount x h g).val ∧ j.val<arity x n h g)
    (count : ∀x,Source ((paid u) x) (amount x) (c₁).lanes (z.tokenImage (z.roleInput mid)))
    (ranges : ∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.tokenImage (z.roleInput mid))) :
    (∀x,Reads ((v).terminalRole b x) (fun h g=>encode (c).bits (c).nodes
      (fun n=>((emit G s Z op (cells x n h g)).val:Cell (c).bits))) (c).lanes dst) ∧
    ∀x,Reads ((v).terminalArity b x) (fun h g=>encode (c₁).bits (c₁).nodes (fun n=>
      if n.val<(amount x h g).val then (arity x n h g:Cell (c₁).bits) else 0)) (c₁).lanes dst := by
  rw [PhysicalReset.date_image z fit ran operands]
  exact z.role_arity_at fit (z.roleInput mid) bits cells small retained fresh relay amount sp arity bounded live count ranges

end PhysicalReset.FinalInputs
end
end Hierarchy.DescentDatedAddressBook

end OAI
