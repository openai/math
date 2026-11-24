import OAI.Computability.VPVNP.PairShrinkRoleChild
import OAI.Computability.VPVNP.PairShrinkRoleHidden
import OAI.Computability.VPVNP.PairSimulationResidentMapLoopExact

/-!
# Joining the child, hidden and resident-map stages of a shrinking visit

A directory load before each stage prepares its input registers. The native
reads pass the exact remaining tape through these loads and through the
deterministic resident maps. The join accounts for every private-memory write
and preserves the pending DFS stack on successful returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS Compression CompressorRecords
open NodeArguments NodeArguments.ChildScan
open ShrinkHiddenGuess
open scoped Fin.CommRing

variable {w endAddr a g p r k : ℕ} {α β : Type*}

variable {X : State a g} (A : Arena) (T : IncidenceDirectory w) (m : Memory w)
  (older cap : ℕ) (desc : Word w → ChildArguments.Descriptor w X)
  (args : List (Child X) → Args w) (seed : List (Child X) → List Row)
  (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
  (loadChild : Setup w endAddr) (loadHidden : List (Child X) → Setup w endAddr)
  (loadMaps : List (Child X) → List Row → Setup w endAddr)

/-- Trace, scratch and stream decoder for the actual three scans. The
directory loads receive the values chosen by all preceding stages. -/
noncomputable def visitReader : Reader w endAddr Unit :=
  bind loadChild.reader fun _ =>
  bind (ChildArguments.reader A T m older cap desc) fun xs =>
  bind (loadHidden xs).reader fun _ =>
  bind (hiddenReader (args xs) m (seed xs)) fun es =>
  bind (loadMaps xs es).reader fun _ => ResidentMapLoop.Exact.mapReader (maps xs es)

/-- Exactness of a shrinking visit in the DFS machine. The operand loads
supply the required register values before each native reader; the resident
entry callbacks check the selected matrix occurrences on the prepared scratch. -/
theorem native_exactOn {M : Machine w p r k} {dfs : Fin 9 ↪ Fin r} {visit : Fin p}
    {domain : Word w → Scratch w endAddr → Prop}
    {beginChild childInput : Word w → Config w p r → Prop}
    {afterChild hiddenInput : List (Child X) → Word w → Config w p r → Prop}
    {afterHidden : List (Child X) → List Row → Word w → Config w p r → Prop}
    (mapLoop : ResidentMapLoop.Program p r)
    (mapInv : List (Child X) → List Row → Word w → Config w p r → Prop)
    (mapBase : List (Child X) → List Row → ℕ)
    (start : ∀ node c top pending, domain node (scratch endAddr c.privateMem) →
      Entry dfs endAddr visit node c top pending → beginChild node c)
    (load₁ : Realizes loadChild.reader M m dfs beginChild (fun _ => childInput))
    (children : Realizes (endAddr := endAddr) (ChildArguments.reader A T m older cap desc)
      M m dfs childInput afterChild)
    (load₂ : ∀ xs, Realizes (loadHidden xs).reader M m dfs
      (afterChild xs) (fun _ => hiddenInput xs))
    (hidden : ∀ xs, Realizes (endAddr := endAddr) (hiddenReader (args xs) m (seed xs)) M m dfs
      (hiddenInput xs) (afterHidden xs))
    (load₃ : ∀ xs es, Realizes (loadMaps xs es).reader M m dfs (afterHidden xs es)
      (fun _ => ResidentMapLoop.Exact.Entry mapLoop (mapInv xs es) (mapBase xs es)
        (maps xs es).length))
    (linked : mapLoop.Linked M) (stable : ∀ xs es node, mapLoop.Stable (mapInv xs es node))
    (apart : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → dfs i ≠ mapLoop.cursor)
    (items : ∀ xs es, ResidentMapLoop.Exact.Items mapLoop M m dfs (mapInv xs es)
      (mapBase xs es) (maps xs es))
    (room : ∀ xs es, mapBase xs es + (maps xs es).length < 2 ^ w) :
    (hook (visitReader A T m older cap desc args seed maps loadChild loadHidden loadMaps)).ExactOn
      domain M visit mapLoop.done dfs m := by
  let stages := load₁.bind fun _ => children.bind fun xs => (load₂ xs).bind fun _ =>
    (hidden xs).bind fun es => (load₃ xs es).bind fun _ =>
      (ResidentMapLoop.Exact.maps_realizes mapLoop linked (stable xs es) apart (maps xs es)
        (mapBase xs es) (items xs es) (room xs es)).weakenPost (fun _ _ _ h => h.1)
  apply stages.exactOn _ start
  have cs : Splits (endAddr := endAddr) (ChildArguments.reader A T m older cap desc) :=
    fun _ _ _ _ _ h => ChildArguments.splitBits A T m older cap desc h
  have hs xs : Splits (endAddr := endAddr) (hiddenReader (args xs) m (seed xs)) :=
    hiddenReader_split (args xs) m (seed xs)
  have ms xs es : Splits (ResidentMapLoop.Exact.mapReader (maps xs es)) :=
    fun _ _ _ _ _ h => ResidentMapLoop.Exact.splitBits (items xs es |>.quiet) h
  have all := loadChild.splits.bind fun _ => cs.bind fun xs => (loadHidden xs).splits.bind fun _ =>
    (hs xs).bind fun es => (loadMaps xs es).splits.bind fun _ => ms xs es
  exact fun node saved bs out rest _ h => all node saved bs out rest h

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
