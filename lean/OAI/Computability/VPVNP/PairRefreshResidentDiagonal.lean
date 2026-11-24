import OAI.Computability.VPVNP.PairRefreshResidentImage

/-!
# Running both diagonal tests inside the installed refresh image

The register recipes read the actual width and offset columns. The comparison
loops read both resident node halves, testing the precise integer multiplier
of the refresh kernel before any histogram update.
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

private theorem tick_log (n : ℕ) :
    choiceBits (List.replicate n (.tick : Event bits)) = [] ∧ countProbes (List.replicate n (.tick : Event bits)) = 0 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ,choiceBits,countProbes] using ih

include installed in
/-- The diagonal loader and both comparisons form one linked prefix, including
the rejecting branch and the frame on every other live operand. -/
theorem diagonal_native {fit : N ≤ 2^bits} (c : Config bits pcs regs) (entry : c.pc = T.diagSetup pc 0)
    (safe : ∀ i j, own i ≠ inp j)
    (args : Describes T.input (fun i => c.reg (inp i.castSucc)) (c.reg (inp (Fin.last 5))) m
      X v P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice T.ties start T.stride fit m)
    (oldCols : oldDir.ActualColumns X m) (newCols : newDir.ActualColumns Y m)
    (oldData : NodeFields A child X (oldSite X v) old c.privateMem)
    (newData : NodeFields A parent Y (promotedSites v) new c.privateMem)
    (wide : D < 2^bits) (wo : vout < 2^bits) (wi : vin < 2^bits) :
    ∃ d es, ChildScan.Prefix M m c d [] es ∧
      es.length = (RegisterSetup.lines T.diagonal).length + (7*(vout+vin)+9) ∧
      countProbes es = ∑ i, (T.diagonal i).loads ∧ choiceBits es = [] ∧
      d.pc = (if diagonalValue = (1 : ℤ) then T.routeSetup pc 0 else T.bad pc) ∧
      (∀ j, (∀ i, j ≠ own i) → d.reg j = c.reg j) ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨es,mid,len,probes,path,pc',mem,per,ready,frame,run⟩ := DiagonalFrame.setup_trace X v P hD hd internal
    A child parent oldDir newDir Q src term T.input m M c inp (T.diagVM own) (T.diagReg own) (T.diagSetup pc)
    (T.diag_link pc dfs saved common own done M installed) (fun i j => safe _ j) (T.outputs own) entry args oldCols
    newCols stored.segments wide
  have next : mid.pc = T.comparePC pc 0 0 := pc'.trans (dite_eq_right (Nat.lt_irrefl _))
  have old' : NodeFields A child X _ old mid.privateMem := mem ▸ oldData
  have new' : NodeFields A parent Y _ new mid.privateMem := mem ▸ newData
  obtain ⟨d,tail,final,mem',per',regs'⟩ := RefreshDiagonal.compare_arguments X v P hD hd internal
    (T.compare_link pc dfs saved common own done M installed) A child parent old new mid next old' new' ready wo wi
  let n := 7*(vout+vin)+9
  have first : ChildScan.Prefix M m c mid [] es := run
  change PrimedCounter.GuessWord.Prefix M mid (List.replicate n .tick) d at tail
  have counts := tick_log (bits := bits) n
  have second : ChildScan.Prefix M m mid d [] (List.replicate n .tick) := by
    intro fuel more
    simpa only [counts.1] using tail.execute fuel m more
  refine Exists.intro d ?_
  refine Exists.intro (es ++ List.replicate n (.tick : Event bits)) ?_
  constructor
  · exact first.trans second
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))))

  · rw [List.length_append,len,List.length_replicate]
    rfl
  · rw [countProbes_append,probes,counts.2,Nat.add_zero]
    rfl
  · rw [PrimedInputRAM.Flow.choiceBits_append,path,counts.1,List.nil_append]
  · exact final
  · intro j hj
    exact (regs' j (fun ⟨i,e⟩ => hj _ e.symm)).trans (frame j (fun i => hj _))
  · exact mem'.trans mem
  · exact per'.trans per

end CompressorRecords.PortRefresh.RefreshResidentImage.Plan

end VPVNP
end Computability
end OAI
