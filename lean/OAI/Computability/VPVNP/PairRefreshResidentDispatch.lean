import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.CompressorRefreshMapRoute
import OAI.Computability.VPVNP.PairSimulationResidentDispatchImage
import OAI.Computability.VPVNP.PairNodeChildLoop
import Mathlib.Data.List.NodupEquivFin

/-!
# Native dispatch on the refresh term header and promoted port

The ordinal comparison chains use the finite order of the stored demand grid.
The port chain uses the promoted port's numerical order. Together the operand
loader and the two chains reach the corresponding motif interpreter in the host
RAM, with an exact instruction count and external probe count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.RefreshResidentDispatch

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open NewSlots PhaseRecipe OperandInputs PairSimulation NodeArguments MotifConversion
open scoped Fin.CommRing

variable {bits g t pcs regs params : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Bijection between finite dispatch ordinals and the admissible refresh demand profiles in
the route's grid-case order. -/
noncomputable def gridOrder : Fin (MapRoute.gridCases B).length ≃ B.refresh.grid.demands :=
  (finCongr (List.length_ofFn (f := _))).trans
    ((List.Nodup.getEquiv _ B.refresh.grid.demands.nodup_toList).trans
      (Equiv.subtypeEquivRight fun _ => Finset.mem_toList))

theorem gridOrder_apply (i : Fin (MapRoute.gridCases B).length) :
    gridOrder B i = (MapRoute.gridCases B)[i.val] := by
  apply Subtype.ext
  simp only [MapRoute.gridCases,List.getElem_ofFn]
  rfl

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)

variable (I : Input) (stride : ℕ)
local notation "f" => MapRoute.fields D stride I
variable (vm : Fin (RegisterSetup.regCount (MapRoute.fields (2^S.portExponent) stride I)) ↪ Fin regs)
  (place : ResidentDispatchImage.Address B.refresh.grid.demands (Fin (2^S.portExponent)) → Fin pcs)
  (target : B.refresh.grid.demands → Fin (2^S.portExponent) → Fin pcs) (bad : Fin pcs)

include place target vm in
/-- Install the demand and party dispatch chains with their setup registers, successful handler
targets, and rejection target. -/
noncomputable def image : ResidentDispatchImage.Image B.refresh.grid.demands (Fin D)
    (MapRoute.gridCases B).length D pcs regs where
  grids := gridOrder B
  parties := Equiv.refl _
  place := place
  target := target
  bad := bad
  grid := vm (RegisterSetup.output f 0)
  party := vm (RegisterSetup.output f 1)
  zero := vm (RegisterSetup.output f 2)
  one := vm (RegisterSetup.output f 3)

local notation "R" => image B I stride vm place target bad

theorem distinct : (R).Distinct := by
  constructor <;> intro eqn <;> have h := congrArg Fin.val (vm.injective eqn) <;> norm_num [RegisterSetup.output] at h

variable (X : State S.portExponent (S.portExponent+g))
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent))
local notation "dem" => blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X)
local notation "selected" => demandGrid B.refresh (fun _ => zero_lt_one) (dem (Prod.fst p))

/-- Native ticks used to select a grid ordinal and port along the two consecutive comparison
chains. -/
def chainTicks (grid port : ℕ) := 1 + ((2 * grid + 1) + (2 * port + 1))

theorem keys_hit (M : Machine bits pcs regs params) (linked : (R).Linked M)
    (c : Config bits pcs regs) (entry : c.pc = place (.inl ()))
    (keys : MapRoute.Keys B X p (fun i => c.reg (vm (RegisterSetup.output f i))))
    (wide : D < 2^bits) :
    ∃ d, PrimedCounter.GuessWord.Prefix M c
        (List.replicate (chainTicks ((gridOrder B).symm selected).val p.2.val) .tick) d ∧
      d.pc = target selected p.2 ∧
      (∀ q, (∀ i, q ≠ vm i) → d.reg q = c.reg q) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨j, key, fit, get⟩ := keys.grid
  have select : gridOrder B j = selected := (gridOrder_apply B j).trans get
  obtain ⟨d, path, pc, frame, mem, per⟩ := (R).native M linked (distinct B I stride vm place target bad)
    j p.2 fit (p.2.isLt.trans wide) c entry key keys.party keys.one
  refine ⟨d, ?_, ?_, fun q hq => frame q (hq _) (hq _) (hq _), mem, per⟩
  · rwa [← select, Equiv.symm_apply_apply]
  · exact pc.trans (congrArg (fun z => target z p.2) select)

private theorem tick_counts (n : ℕ) :
    choiceBits (List.replicate n (.tick : Event bits)) = [] ∧ countProbes (List.replicate n (.tick : Event bits)) = 0 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ, choiceBits, countProbes] using ih

variable (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (A : Arena) (child parent : ℕ) (oldDir newDir : IncidenceDirectory bits)
  (ties : Fin t ≃ Tie (2^S.portExponent)) (start : ℕ) (m : Memory bits)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t stride start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D

/-- The concrete field loader followed by both ordinal chains. The instruction
bound depends on the finite template and the chosen ordinal, independently of
the sizes of the bitstrings consumed by the motif. -/
theorem load_and_dispatch {fit : N ≤ 2^bits} (M : Machine bits pcs regs params) (c : Config bits pcs regs)
    (inputs : Fin 6 → Fin regs) (pc : ℕ → Fin pcs)
    (link : RegisterSetup.Linked vm inputs M pc (RegisterSetup.lines f)) (safe : ∀ i j, vm i ≠ inputs j)
    (entry : c.pc = pc 0) (next : pc (RegisterSetup.lines f).length = place (.inl ()))
    (linked : (R).Linked M)
    (args : Describes I (fun i => c.reg (inputs i.castSucc)) (c.reg (inputs (Fin.last 5))) m
      X p P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (wide : D < 2^bits) :
    ∃ d es, ChildScan.Prefix M m c d [] es ∧
      es.length = (RegisterSetup.lines f).length + chainTicks ((gridOrder B).symm selected).val p.2.val ∧
      countProbes es = ∑ i, (f i).loads ∧ choiceBits es = [] ∧ d.pc = target selected p.2 ∧
      (∀ q, (∀ i, q ≠ vm i) → d.reg q = c.reg q) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨es,mid,len,probes,path,pc',mem,per,keys,frame,run⟩ :=
    MapRoute.setup B X choice p A child parent oldDir newDir ties start stride m I M c inputs vm pc link safe entry args stored wide
  obtain ⟨d,tail,done,frame',mem',per'⟩ := keys_hit B I stride vm place target bad X p M linked mid (pc'.trans next) keys wide
  let n := chainTicks ((gridOrder B).symm selected).val p.2.val
  have first : ChildScan.Prefix M m c mid [] es := run
  change PrimedCounter.GuessWord.Prefix M mid (List.replicate n .tick) d at tail
  have counts := tick_counts (bits := bits) n
  have second : ChildScan.Prefix M m mid d [] (List.replicate n .tick) := by
    intro fuel more
    simpa only [counts.1] using tail.execute fuel m more
  refine ⟨d,es ++ List.replicate n .tick,first.trans second,?_,?_,?_,done,fun q hq => (frame' q hq).trans (frame q hq),
    mem'.trans mem,per'.trans per⟩
  · rw [List.length_append,len,List.length_replicate]
  · rw [countProbes_append,probes,counts.2,Nat.add_zero]
  · rw [PrimedInputRAM.Flow.choiceBits_append,path,counts.1,List.nil_append]

end CompressorRecords.PortRefresh.RefreshResidentDispatch

end VPVNP
end Computability
end OAI
