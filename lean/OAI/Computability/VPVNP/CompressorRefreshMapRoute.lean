import OAI.Computability.VPVNP.CompressorRefreshMapCallWords
import OAI.Computability.VPVNP.CompressorRecordRegisterSetup

/-!
# Selecting the refresh map's grid row and port

The grid ordinal is the header of the accepted term record. The second dispatch key is
the port consumed by the refresh, recovered from the promoted site ordinal and the
residual lane count. A fixed native register setup supplies both keys and the comparison
constants. The finite table order is the one used by the actual term writer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.MapRoute

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh NewSlots PhaseRecipe
open OperandInputs PairSimulation NodeArguments RefreshMapOperands MotifConversion
open scoped Fin.CommRing

/-- The route keys consisting of the stored grid ordinal, the runtime port ordinal, and the
literals zero and one. -/
def fields (degree stride : ℕ) (I : Input) : Fin 4 → Expr :=
  let block := ArgumentSite.blockIndex degree I.parent.siteOrd I.lanes
  ![.load (I.termBase.add (block.mul (.lit stride))),ArgumentSite.portIndex degree I.parent.siteOrd I.lanes,
    .lit 0,.lit 1]

variable {bits g t pcs regs params : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Enumerates the demand grid in its finite-set list order, retaining membership for each
route case. -/
noncomputable def gridCases : List B.refresh.grid.demands :=
  List.ofFn fun i : Fin B.refresh.grid.demands.toList.length =>
    ⟨B.refresh.grid.demands.toList[i.val],Finset.mem_toList.mp (List.getElem_mem i.isLt)⟩

variable (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (oldDir newDir : IncidenceDirectory bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (start stride : ℕ)
  (m : Memory bits) (I : Input)

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t stride start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D
local notation "dem" => blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X)
local notation "f" => fields D stride I

/-- Keys and comparison constants before the two decrement chains execute. -/
structure Keys (r : Fin 4 → W bits) : Prop where
  grid : ∃ j : Fin (gridCases B).length, r 0 = word j.val ∧ j.val < 2^bits ∧
    (gridCases B)[j.val] = demandGrid B.refresh (fun _ => zero_lt_one) (dem p.1)
  party : r 1 = word p.2.val
  zero : r 2 = 0
  one : r 3 = 1

theorem values {fit : N ≤ 2^bits} (pub : Fin 5 → W bits) (state : W bits)
    (args : Describes I pub state m X p P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (wide : D < 2^bits) : Keys B X p (fun i => (f i).eval pub state m) := by
  let block := ArgumentSite.blockIndex D I.parent.siteOrd I.lanes
  let row := SupplyScan.recordBase X term stride p.1
  have hb : block.eval pub state m = word (DemandScan.blocks X p.1).val :=
    ArgumentSite.blockIndex_eval X p pub state m _ _ args.site args.lanes wide
  have address : term + word (DemandScan.blocks X p.1).val * word stride = row := by rw [DemandScan.blocks_val]; rfl
  have hkey : (f 0).eval pub state m = m row.val := by
    change m (I.termBase.eval pub state m + block.eval pub state m * word stride).val = _
    rw [args.termBase,hb,address]
  have ⟨hrow,hval⟩ := List.getElem?_eq_some_iff.mp (stored.readback p.1).1
  let i : Fin (gridCases B).length := ⟨(m row.val).val,by simpa [gridCases,row] using hrow⟩
  refine ⟨⟨i,?_,(m row.val).isLt,?_⟩,ArgumentSite.portIndex_eval X p pub state m _ _ args.site args.lanes wide,rfl,rfl⟩
  · exact hkey.trans (Fin.ext (Nat.mod_eq_of_lt (m row.val).isLt).symm)
  · apply Subtype.ext
    simp only [gridCases,List.getElem_ofFn,i,row]
    convert! hval using 0

/-- The compiled key loader consumes no guesses and jumps to the first grid comparison.
Every probe is one of the loads in the four fixed expressions. -/
theorem setup {fit : N ≤ 2^bits} (M : Machine bits pcs regs params) (c : Config bits pcs regs)
    (inputs : Fin 6 → Fin regs) (vm : Fin (RegisterSetup.regCount f) ↪ Fin regs) (pc : ℕ → Fin pcs)
    (link : RegisterSetup.Linked vm inputs M pc (RegisterSetup.lines f)) (safe : ∀ i j, vm i ≠ inputs j)
    (entry : c.pc = pc 0) (args : Describes I (fun i => c.reg (inputs i.castSucc)) (c.reg (inputs (Fin.last 5))) m
      X p P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (wide : D < 2^bits) :
    ∃ ev d, ev.length = (RegisterSetup.lines f).length ∧ countProbes ev = (∑ i, (f i).loads) ∧
      choiceBits ev = [] ∧ d.pc = pc (RegisterSetup.lines f).length ∧ d.privateMem = c.privateMem ∧
      d.persistent = c.persistent ∧ Keys B X p (fun i => d.reg (vm (RegisterSetup.output f i))) ∧
      (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧ ∀ fuel bs, execute M.program (fuel+ev.length) c m bs =
        (execute M.program fuel d m bs).map (fun r => ⟨ev++r.events,r.result⟩) := by
  obtain ⟨ev,d,len,probes,path,done,priv,pers,vals,frame,run⟩ := RegisterSetup.execute_setup_trace f inputs vm M m pc link safe c entry
  exact ⟨ev,d,len,probes,path,done,priv,pers,(funext vals) ▸ values B X choice p A child parent oldDir newDir ties
    start stride m I _ _ args stored wide,frame,run⟩

end CompressorRecords.PortRefresh.MapRoute

end VPVNP
end Computability
end OAI
