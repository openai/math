import OAI.Computability.VPVNP.PairRefreshResidentReads
import OAI.Computability.VPVNP.PairRefreshResidentMapExact

/-! # A successful refresh kernel has a fixed trace and upper scratch

The chronological diagonal and dispatch prefix preserves the actual inputs
of the selected handler. The resulting trace and upper-scratch update are
determined by these input words, the two node halves and the incoming scratch.
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


local notation "dx" => List.length (RegisterSetup.lines (Plan.diagonal T)) + (7*(vout+vin)+9)
local notation "rx" => List.length (RegisterSetup.lines (Plan.route T)) +
  RefreshResidentDispatch.chainTicks (Fin.val (Equiv.symm (RefreshResidentDispatch.gridOrder B) z)) (Fin.val (Prod.snd v))
local notation "mx" => MapArgumentWriter.clock (Plan.directory T) Wfields + MapInline.cap B.refresh (Plan.ordinal T) z (Prod.snd v) u
local notation "dp" => ∑ i, Expr.loads ((Plan.diagonal T) i)
local notation "rp" => ∑ i, Expr.loads ((Plan.route T) i)
local notation "mp" => ∑ i, Expr.loads ((MapArgumentWriter.recipes (Plan.directory T) Wfields) i)

include installed in
set_option maxHeartbeats 2000000 in
theorem native_success_exact {fit : N ≤ 2^bits} {n limit : ℕ} (c : Config bits pcs regs) (entry : c.pc = T.diagSetup pc 0)
    (banks : Banks T dfs saved common own)
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
    (wide : D < 2^bits) (wo : vout < 2^bits) (wi : vin < 2^bits)
    (tableWidth : MapConstants.widthThreshold B.refresh ≤ bits) (endAddr : ℕ) (savedScratch : DFS.Scratch bits endAddr)
    (incoming : DFS.scratch endAddr c.privateMem = savedScratch)
    (diagonalOK : diagonalValue = (1 : ℤ)) (namesOK : (names).isSome = true) :
    let pub := fun i : Fin 5 => c.reg (inp i.castSucc)
    let state := c.reg (inp (Fin.last 5))
    let es := T.successEvents X choice v m old new tableWidth pub state
    ∃ out, ChildScan.Prefix M m c out [] es ∧ es.length ≤ dx + rx + mx ∧
      countProbes es = dp + (rp + mp) ∧ choiceBits es = [] ∧ out.pc = done ∧ out.persistent = c.persistent ∧
      (∀ j, (∀ i, j ≠ own i) → out.reg j = c.reg j) ∧
      (∀ q : W bits, q.val < directory → (∀ l : Fin hist, q ≠ word (histBase+l.val)) →
        out.privateMem q = c.privateMem q) ∧
      (∀ l : Fin hist, out.privateMem (word (histBase+l.val)) = c.privateMem (word (histBase+l.val)) +
        (((names).getD []).count l : W bits)) ∧
      DFS.scratch endAddr out.privateMem = T.mapUpper X choice v A child parent old new
        top maxWidth directory histBase oldEnd newEnd oldWidth newWidth inputsEnd histEnd workEnd
        capacity copyBound tableWidth endAddr savedScratch := by
  intro pub state es
  obtain ⟨mid,front,flen,fprobes,fpath,midPC,frame,mem,pers⟩ :=
    T.front_exact pc dfs saved common own done M installed X choice v A child parent oldDir newDir start m old new
      c entry banks args stored oldCols newCols oldData newData wide wo wi diagonalOK
  have inputs (i) : mid.reg (inp i) = c.reg (inp i) := frame _ (fun j => (banks.inputs j i).symm)
  have midPub : (fun i : Fin 5 => mid.reg (inp i.castSucc)) = pub := funext fun i => inputs i.castSucc
  have midState : mid.reg (inp (Fin.last 5)) = state := inputs (Fin.last 5)
  obtain ⟨out,call,clen,cprobes,cpath,exit,per,regs',memory,counts,updated⟩ :=
    T.map_native_exact pc dfs saved common own done M installed X choice v A child parent oldDir newDir start m old new
      mid midPC banks.handler (midPub.symm ▸ midState.symm ▸ args) stored oldCols newCols (mem ▸ oldData)
      (mem ▸ newData) top maxWidth directory histBase (midPub.symm ▸ midState.symm ▸ hdir)
      (midPub.symm ▸ midState.symm ▸ hhist) oldEnd newEnd oldWidth newWidth inputsEnd histEnd workEnd capacity
      copyBound wide tableWidth endAddr savedScratch (mem ▸ incoming) namesOK
  rw [midPub,midState] at call clen cprobes cpath
  let pre := T.frontEvents X choice v m old new pub state
  let tail := T.family.successEvents (fun _ => zero_lt_one) E₀ tableWidth pub state m
  change pre.length = _ at flen
  change countProbes pre = _ at fprobes
  change choiceBits pre = [] at fpath
  change tail.length ≤ _ at clen
  change countProbes tail = _ at cprobes
  change choiceBits tail = [] at cpath
  refine ⟨out,front.trans call,?_,?_,?_,exit,per.trans pers,fun j hj => (regs' j hj).trans (frame j hj),
    fun q hq hn => (memory q hq hn).trans (congrFun mem q),?_,updated⟩
  · change (pre++tail).length ≤ _
    rw [List.length_append,flen]
    exact Nat.add_le_add_left clen _
  · change countProbes (pre++tail) = _
    rw [countProbes_append,fprobes,cprobes,Nat.add_assoc]
  · change choiceBits (pre++tail) = []
    rw [PrimedInputRAM.Flow.choiceBits_append,fpath,cpath,List.nil_append]
  · intro l
    rw [counts,mem]

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

end VPVNP
end Computability
end OAI
