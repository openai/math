import OAI.Computability.VPVNP.PairRefreshResidentImage
import OAI.Computability.VPVNP.PairSimulationMapHandlerRun
import OAI.Computability.VPVNP.CompressorRefreshMapCallData

/-!
# Executing the selected resident refresh map

The selected interpreter receives descriptor words computed from the level
arrays and resident bits from the two node buffers. Its raw operand, selector,
and histogram ranges are supplied by the concrete packed workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.RefreshResidentImage.Plan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe OperandInputs PairSimulation NodeArguments MotifConversion NewSlots RefreshMapOperands NetworkKernel
open scoped Fin.CommRing

variable {bits g t hist shared pcs regs : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
  (T : Plan B t hist shared)
  (pc : T.Address → Fin pcs) (dfs : Fin 9 ↪ Fin regs) (saved : VertexImage.Saved ↪ Fin regs)
  (common : Fin shared ↪ Fin regs) (own : T.Local ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11) (installed : T.Installed pc dfs saved common own done M)

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)

variable (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (oldDir newDir : IncidenceDirectory bits) (start : ℕ) (m : Memory bits)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh hD hd choice
local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t (Plan.stride T) start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D
local notation "ws" => groupedWidths (bitWordFinEquiv _) (splitWidths X)
local notation "perm" => oldPortMatching (splitSlots X) (bitWordFinEquiv _)
local notation "inp" => T.inputs dfs saved common
local notation "vout" => ws (v,Prod.snd v)
local notation "vin" => ws (Equiv.symm perm (v,Prod.snd v))

variable (old : X.network.Half (oldSite X v)) (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
local notation "diagonalValue" => portDiagonal perm ws (Prod.fst v) (Prod.snd v) (oldHalf X v old) (segments X v P hD hd internal new)


open MotifEntry MotifDemandPadding MotifSelector LocalHistory
local notation "E₀" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand E₀)
local notation "idx" => (z,Prod.snd v)
local notation "L" => MapInline.layout B.refresh z (Prod.snd v)
local notation "u" => repetitions B.refresh (EntryInput.demand E₀)
local notation "d" => demandBits tieSource tieTarget (Prod.snd v) (EntryInput.demandBits E₀)
local notation "x" => mapHalf S.portSupply (fun _ => inputBits) (EntryInput.supplyBits E₀)
local notation "names" => Option.map (List.map (Plan.ordinal T))
  (Prod.fst (runEntry B.refresh (fun _ => zero_lt_one) (EntryInput.demand E₀) (EntryInput.payload E₀) (Prod.snd v) d x))
local notation "Wfields" => MapHandlerImage.Family.fields (Plan.family T) idx

include installed in
set_option maxHeartbeats 1600000 in
/-- The actual selected map exits at the caller's continuation or at a rejecting
opcode. Its histogram additions are the multiplicities of its emitted labels.
Words preceding the scratch directory and outside the histogram are preserved. -/
theorem map_native {fit : N ≤ 2^bits} {n limit : ℕ} (c : Config bits pcs regs)
    (entry : c.pc = T.family.target (T.handlerPC pc) idx)
    (banks : T.family.Apart dfs saved common (T.handlerReg own))
    (args : Describes T.input (fun i => c.reg (inp i.castSucc)) (c.reg (inp (Fin.last 5))) m
      X v P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice T.ties start T.stride fit m)
    (oldCols : oldDir.ActualColumns X m) (newCols : newDir.ActualColumns Y m)
    (oldData : NodeFields A child X (oldSite X v) old c.privateMem)
    (newData : NodeFields A parent Y (promotedSites v) new c.privateMem)
    (top maxWidth directory histBase : ℕ)
    (hdir : T.directory.eval (fun i => c.reg (inp i.castSucc)) (c.reg (inp (Fin.last 5))) m = word directory)
    (hhist : T.histogram.eval (fun i => c.reg (inp i.castSucc)) (c.reg (inp (Fin.last 5))) m = word histBase)
    (oldEnd : A.base child + (packed X (oldSite X v) old).length ≤ top)
    (newEnd : A.base parent + (packed Y (promotedSites v) new).length ≤ top)
    (oldWidth : X.maxWireWidth ≤ maxWidth) (newWidth : (Y).maxWireWidth ≤ maxWidth)
    (inputsEnd : top+2*maxWidth ≤ directory) (histEnd : histBase+hist ≤ directory)
    (workEnd : directory+MapCallWords.headCapacity D H+2*u ≤ limit)
    (capacity : MapWorkspace.Capacity B.refresh bits n limit) (copyBound : u ≤ n)
    (wide : D < 2^bits) (tableWidth : MapConstants.widthThreshold B.refresh ≤ bits) :
    ∃ out es, ChildScan.Prefix M m c out [] es ∧
      es.length ≤ MapArgumentWriter.clock T.directory Wfields + MapInline.cap B.refresh T.ordinal z v.2 u ∧
      countProbes es = ∑ i, ((MapArgumentWriter.recipes T.directory Wfields) i).loads ∧ choiceBits es = [] ∧
      (if (names).isSome then out.pc = done else M.code out.pc = .reject) ∧ out.persistent = c.persistent ∧
      (∀ j, (∀ i, j ≠ own i) → out.reg j = c.reg j) ∧
      (∀ q : W bits, q.val < directory → (∀ l : Fin hist, q ≠ word (histBase+l.val)) → out.privateMem q = c.privateMem q) ∧
      ∀ l : Fin hist, out.privateMem (word (histBase+l.val)) = c.privateMem (word (histBase+l.val)) +
        (((names).getD []).count l : W bits) := by
  let R := MapCallWords.regions B X choice v A child parent old new directory histBase
  let loc := (L).corePC (L).locations
  let ord := MapCallWords.regions_ordered B X choice v A child parent old new z (L).core loc top maxWidth directory
    histBase limit oldEnd newEnd oldWidth newWidth inputsEnd histEnd workEnd
  let Wk := MapWorkspace.workspace (MapInline.callProgram L) R d x capacity copyBound ord
  let pub := fun i : Fin 5 => c.reg (inp i.castSucc)
  let state := c.reg (inp (Fin.last 5))
  let addr := T.directory.eval pub state m
  have dirFit : directory < 2^bits := by have := capacity.room; omega
  have addrVal : addr.val = directory := (congrArg Fin.val hdir).trans (Nat.mod_eq_of_lt dirFit)
  have hhead := MapCallWords.plannedHeads_eval B X choice v A child parent old new oldDir newDir T.ties start T.stride
    pub state m T.input T.directory T.histogram directory histBase hdir hhist args stored wide
  have vals := MapCallWords.values_eq B X choice v A child parent oldDir newDir T.ties start T.stride pub state m
    T.input T.heads old new z (L).core loc Wk args oldCols newCols stored wide rfl hhead.1 hhead.2.1 hhead.2.2.1 hhead.2.2.2
  have resident := MapCallData.resident_packed B X choice v A child parent old new z (L).core loc T.ties start T.stride m
    c.privateMem R capacity copyBound ord addr addrVal.ge stored oldData newData rfl
  have argc : Fintype.card (MapCallSetup.Arg (Tie D) (Fin D × Fin H)) ≤ MapCallWords.headCapacity D H := le_max_right _ _
  have room : addr.val+Fintype.card (MapCallSetup.Arg (Tie D) (Fin D × Fin H)) ≤ 2^bits := by have := capacity.room; omega
  have histVal (l : Fin hist) : (word (bits := bits) (histBase+l.val)).val = histBase+l.val :=
    Nat.mod_eq_of_lt (by have := l.isLt; omega)
  have dirCell (j : MapDirectoryInit.Row (L).core) :
      (Wk.directory+(j.val : W bits)).val = directory+j.val := by
    change ((directory : W bits)+(j.val : W bits)).val = _
    rw [← Nat.cast_add]
    apply Nat.mod_eq_of_lt
    have bound := ord.directoryEnd
    change directory + (MapPortAgreement.ports S.portSupply v.2 (L).core.edgeOrder).length ≤ directory + MapCallWords.headCapacity D H at bound
    have := j.isLt
    have := capacity.room
    omega
  have histBefore (l : Fin hist) : (word (bits := bits) (histBase+l.val)).val < addr.val := by
    rw [histVal,addrVal]; exact (Nat.add_lt_add_left l.isLt _).trans_le histEnd
  obtain ⟨out,es,run,len,probes,choices,branch,per,regs',mem',counts⟩ :=
    T.family.native (T.handlerPC pc) dfs saved common (T.handlerReg own) done M
      (T.handler_rows pc dfs saved common own done M installed) banks (fun _ => zero_lt_one) E₀ tableWidth c m Wk
      entry room vals resident (fun l => Or.inl (histBefore l))
      (fun l j eqn => by
        have h : histBase+l.val = directory+j.val := (histVal l).symm.trans ((congrArg Fin.val eqn).trans (dirCell j))
        have := l.isLt; omega)
  refine ⟨out,es,run,len,probes,choices,branch,per,fun q hq => regs' q (fun _ => hq _),?_,counts⟩
  intro q hq notHist
  apply mem' q (Or.inl (hq.trans_le addrVal.ge))
  refine ⟨⟨Or.inl ?_,Or.inl ?_,notHist⟩,fun j eqn => ?_⟩
  · change q.val < directory + MapCallWords.headCapacity D H
    omega
  · change q.val < directory + MapCallWords.headCapacity D H + u
    omega
  · have eqv := (congrArg Fin.val eqn).trans (dirCell j)
    omega

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

end VPVNP
end Computability
end OAI
