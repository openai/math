import OAI.Computability.VPVNP.PairRefreshResidentDiagonal
import OAI.Computability.VPVNP.PairRefreshResidentMap

/-!
# The complete resident refresh kernel on the host RAM

The diagonal multiplier and the selected interpreter execute in one native
segment. A failing diagonal reaches its own reject instruction. Otherwise
the actual grid/party handler determines the return or rejection and the
histogram updates.
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

/-- The refresh image's local registers are disjoint from each DFS, saved, and shared register
bank. -/
structure Banks : Prop where
  dfs : ∀ a b, own a ≠ dfs b
  saved : ∀ a b, own a ≠ saved b
  common : ∀ a b, own a ≠ common b

variable {T dfs saved common own} in
theorem Banks.inputs (h : Banks T dfs saved common own) (a j) : own a ≠ inp j := by
  change own a ≠ (T.source j).elim dfs (Sum.elim saved common)
  cases T.source j with
  | inl i => exact h.dfs a i
  | inr s => cases s with
    | inl i => exact h.saved a i
    | inr i => exact h.common a i

variable {T dfs saved common own} in
theorem Banks.handler (h : Banks T dfs saved common own) : T.family.Apart dfs saved common (T.handlerReg own) :=
  ⟨fun _ j => h.dfs _ j,fun _ j => h.saved _ j,fun _ j => h.common _ j⟩

include installed in
set_option maxHeartbeats 2000000 in
/-- Execute the full resident refresh kernel. The branch choice is exactly
the mathematical diagonal test followed by the map on the two node halves. -/
theorem native {fit : N ≤ 2^bits} {n limit : ℕ} (c : Config bits pcs regs) (entry : c.pc = T.diagSetup pc 0)
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
    (tableWidth : MapConstants.widthThreshold B.refresh ≤ bits) :
    let emitted := if diagonalValue = (1 : ℤ) then names else none
    ∃ out es, ChildScan.Prefix M m c out [] es ∧ es.length ≤ dx + rx + mx ∧
      countProbes es = dp + (if diagonalValue = (1 : ℤ) then rp + mp else 0) ∧ choiceBits es = [] ∧
      (if emitted.isSome then out.pc = done else M.code out.pc = .reject) ∧ out.persistent = c.persistent ∧
      (∀ j, (∀ i, j ≠ own i) → out.reg j = c.reg j) ∧
      (∀ q : W bits, q.val < directory → (∀ l : Fin hist, q ≠ word (histBase+l.val)) → out.privateMem q = c.privateMem q) ∧
      ∀ l : Fin hist, out.privateMem (word (histBase+l.val)) = c.privateMem (word (histBase+l.val)) +
        ((emitted.getD []).count l : W bits) := by
  dsimp only
  obtain ⟨mid,es,first,len,probes,path,pc',frame,mem,per⟩ := T.diagonal_native pc dfs saved common own done M
    installed X choice v A child parent oldDir newDir start m old new c entry banks.inputs args stored oldCols newCols
    oldData newData wide wo wi
  by_cases ok : diagonalValue = (1 : ℤ)
  · simp only [ite_eq_left ok] at pc' ⊢
    have inputEq (j) : mid.reg (inp j) = c.reg (inp j) := frame _ (fun i => (banks.inputs i j).symm)
    have pubEq : (fun i : Fin 5 => mid.reg (inp i.castSucc)) = (fun i : Fin 5 => c.reg (inp i.castSucc)) :=
      funext fun i => inputEq i.castSucc
    have args' := pubEq.symm ▸ (inputEq (Fin.last 5)).symm ▸ args
    obtain ⟨next,rs,second,rlen,rprobes,rpath,rpc,rframe,rmem,rper⟩ :=
      RefreshResidentDispatch.load_and_dispatch B T.input T.stride (T.routeVM own) (T.routePC pc)
        (fun z' j => T.family.target (T.handlerPC pc) (z',j)) (T.bad pc) X v choice A child parent oldDir newDir
        T.ties start m M mid inp (T.routeSetup pc) (T.route_link pc dfs saved common own done M installed)
        (fun _ j => banks.inputs _ j) pc' (dite_eq_right (Nat.lt_irrefl _))
        (T.dispatch_link pc dfs saved common own done M installed) args' stored wide
    have allregs (j) (hj : ∀ i, j ≠ own i) : next.reg j = c.reg j :=
      (rframe j (fun _ => hj _)).trans (frame j hj)
    have eqr (j) : next.reg (inp j) = c.reg (inp j) := allregs _ (fun i => (banks.inputs i j).symm)
    have pub' : (fun i : Fin 5 => next.reg (inp i.castSucc)) = (fun i : Fin 5 => c.reg (inp i.castSucc)) :=
      funext fun i => eqr i.castSucc
    have mem' := rmem.trans mem
    obtain ⟨out,ms,third,mlen,mprobes,mpath,mpc,mper,mframe,mmem,histogram⟩ :=
      T.map_native pc dfs saved common own done M installed X choice v A child parent oldDir newDir start m old new next
        rpc banks.handler (pub'.symm ▸ (eqr (Fin.last 5)).symm ▸ args) stored oldCols newCols (mem' ▸ oldData)
        (mem' ▸ newData) top maxWidth directory histBase (pub'.symm ▸ (eqr (Fin.last 5)).symm ▸ hdir)
        (pub'.symm ▸ (eqr (Fin.last 5)).symm ▸ hhist) oldEnd newEnd oldWidth newWidth inputsEnd histEnd
        workEnd capacity copyBound wide tableWidth
    refine ⟨out,(es++rs)++ms,(first.trans second).trans third,?_,?_,?_,mpc,mper.trans (rper.trans per),
      fun j hj => (mframe j hj).trans (allregs j hj),fun q hq hn => (mmem q hq hn).trans (congrFun mem' q),?_⟩
    · rw [List.length_append,List.length_append,len,rlen]
      exact Nat.add_le_add_left mlen _
    · rw [countProbes_append,countProbes_append,probes,rprobes,mprobes,Nat.add_assoc]
      rfl
    · rw [PrimedInputRAM.Flow.choiceBits_append,PrimedInputRAM.Flow.choiceBits_append,path,rpath,mpath]; rfl
    · intro l
      rw [histogram,mem']
  · simp only [ite_eq_right ok] at pc' ⊢
    refine ⟨mid,es,first,?_,?_,path,?_,per,frame,fun q _ _ => congrFun mem q,?_⟩
    · rw [len]; omega
    · simpa using probes
    · rw [pc']; exact T.rejection pc dfs saved common own done M installed
    · intro l
      simp [mem]

/-- The external probe bound depends only on the fixed motif and the recipes
of the enclosing role. Internal instructions additionally scale with the two
diagonal widths and the number of motif copies. -/
theorem uniform : ∃ C : ℕ, ∀ (grid : B.refresh.grid.demands) (port : Fin D) (outWidth inWidth copies : ℕ),
    let fields := T.family.fields (grid,port)
    let cost := (RegisterSetup.lines T.diagonal).length + (7*(outWidth+inWidth)+9) +
      ((RegisterSetup.lines T.route).length + RefreshResidentDispatch.chainTicks
        ((RefreshResidentDispatch.gridOrder B).symm grid).val port.val) +
      (MapArgumentWriter.clock T.directory fields + MapInline.cap B.refresh T.ordinal grid port copies)
    (∑ i, (T.diagonal i).loads) + ((∑ i, (T.route i).loads) +
      ∑ i, ((MapArgumentWriter.recipes T.directory fields) i).loads) ≤ C ∧
      cost ≤ C * (outWidth+inWidth+copies+1) := by
  obtain ⟨K,bound⟩ := T.family.uniform
  let fixed := (RegisterSetup.lines T.diagonal).length + (RegisterSetup.lines T.route).length + 9 +
    RefreshResidentDispatch.chainTicks (MapRoute.gridCases B).length D
  let reads := (∑ i, (T.diagonal i).loads) + ∑ i, (T.route i).loads
  refine ⟨fixed+7+K+reads,fun grid port wo wi copies => ?_⟩
  obtain ⟨probe,work⟩ := bound (grid,port) copies
  change (∑ i, ((MapArgumentWriter.recipes T.directory (T.family.fields (grid,port))) i).loads) ≤ K at probe
  change MapArgumentWriter.clock T.directory (T.family.fields (grid,port)) +
    MapInline.cap B.refresh T.ordinal grid port copies ≤ K*(copies+1) at work
  dsimp only
  constructor
  · dsimp [reads]; omega
  · let n := wo+wi+copies+1
    have gfit := ((RefreshResidentDispatch.gridOrder B).symm grid).isLt
    have pfit := port.isLt
    have fixedBound : (RegisterSetup.lines T.diagonal).length + (7*(wo+wi)+9) +
        ((RegisterSetup.lines T.route).length + RefreshResidentDispatch.chainTicks
          ((RefreshResidentDispatch.gridOrder B).symm grid).val port.val) ≤ fixed + 7*(wo+wi) := by
      dsimp [fixed,RefreshResidentDispatch.chainTicks]; omega
    have h1 : fixed ≤ fixed*n := Nat.le_mul_of_pos_right _ (by dsimp [n]; omega)
    have h2 : 7*(wo+wi) ≤ 7*n := Nat.mul_le_mul_left _ (by dsimp [n]; omega)
    have h3 : K*(copies+1) ≤ K*n := Nat.mul_le_mul_left _ (by dsimp [n]; omega)
    change _ ≤ (fixed+7+K+reads)*n
    rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
    omega

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

end VPVNP
end Computability
end OAI
