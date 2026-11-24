import OAI.Computability.VPVNP.PairSimulationLeafRoleExecution
import OAI.Computability.VPVNP.PairSimulationLeafImageHandler
import OAI.Computability.VPVNP.PairSimulationLeafImageWrites

/-!
# Exactness of the cursor-leaf segment in the eleven-operand vertex table

The physical domain contains the node packet, the 38 cached auxiliary operands
and the ten geometry words reached through the DFS end pointer. Together these
determine the parser on the actual private memory at entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM RegisterOperands PrimedCounter.GuessWord DFS NodeArguments CursorNetwork
open LeafStartup
open scoped Fin.CommRing Classical

set_option synthInstance.maxSize 10000

variable {p r w endAddr : ℕ} (pc : Label → Fin p) (dfs : Fin 9 ↪ Fin r) (priv : Private ↪ Fin r)
  (apart : Apart dfs priv) (ret : Fin p) (A : Machine w p r 11) (data : Fin 10 → Word w)

/-- The domain's typed scratch contains the complete physical record used at entry. -/
theorem stored_actual (base : ℕ) (mem : Word w → Word w) (lo : endAddr ≤ base)
    (hi : base+10 ≤ 2^w)
    (h : LeafGeometryLoad.Stored endAddr base (rawScratch (scratch endAddr mem)) data) :
    LeafGeometryLoad.Stored endAddr base mem data := by
  have lower (n : ℕ) (hn : endAddr ≤ n) (hw : n < 2^w) : endAddr ≤ (n : Word w).val := by
    rwa [Fin.val_natCast,Nat.mod_eq_of_lt hw]
  constructor
  · simpa only [rawScratch,lower endAddr (le_refl _) (by omega),↓reduceDIte,scratch] using h.pointer
  · intro i
    have small := i.isLt
    simpa only [rawScratch,lower (base+i.val) (by omega) (by omega),↓reduceDIte,scratch] using h.values_at i

/-- Read the decoder's row or shadow field from its corresponding slot in the ten geometry
words. -/
def addressFields (j : LeafAddress.Field) := data (LeafGeometryLoad.slot (.address j))

private theorem verification_fields :
    LeafVisit.fields (M := verification pc dfs priv apart ret A data) pubSlot = addressFields data := by
  funext j
  simp only [LeafVisit.fields,Function.comp_apply,verification,shadow,publicData,pubSlot,addressFields,Fin.addCases_left]

variable {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}
  (D : PrimedCounter.Data Q s) {b l e degree pad : ℕ} [NeZero (b+l)] (hD : 1 < b+l)
  (hd : 2+pad=2^degree) (budget : ProcessorBudget n (b+l) e w)
  (R : LeafArena.Regions) (cap base : ℕ) (fit : R.stackBase + Fintype.card ScalarPort*n^40 < 2^w)
  (m : Memory w) (clock : ℕ)

/-- The parser uses the field words stored in the geometry record. -/
noncomputable def parser : HookParser w endAddr :=
  withReload (LeafHandler.parser D budget.tags budget.capFits (LeafVisit.storage R fit)
    (LeafVisit.loaded D budget R fit (addressFields data) m) clock)

/-- The saved scratch and node satisfy the leaf visit's input conditions, and the same scratch
stores the geometry record used to decode its address. -/
def Domain (node : Word w) (saved : Scratch w endAddr) :=
  LeafVisit.Domain (e := e) D hD hd R cap (addressFields data) node saved ∧
    LeafGeometryLoad.Stored endAddr base (rawScratch saved) data

theorem native_exact (inj : Function.Injective pc) (rows : Contains pc dfs priv apart ret A)
    (op : LeafFront.Operands (LeafImage.front (enter ∘ bodyPC pc) (bodyReg dfs priv apart) pubSlot (caller ret))
      (verification pc dfs priv apart ret A data) m D R b l cap)
    (hsize : data (LeafGeometryLoad.slot .size) = (n : Word w)) (arenaLow : endAddr ≤ R.arguments.start)
    (geometryLow : endAddr ≤ base) (geometryFits : base+10 ≤ 2^w)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ clock)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length+clock ≤ n^40) :
    (parser (endAddr := endAddr) data D budget R fit m clock).ExactOn (Domain (e := e) data D hD hd R cap base)
      A (loadPC pc (.inl ())) ret dfs m := by
  let V := verification pc dfs priv apart ret A data
  have size : V.publicData (pubSlot .size) = (n : Word w) := by
    simpa only [V,verification,shadow,publicData,pubSlot,Fin.addCases_left] using hsize
  have semantic := LeafVisit.image_exact (M := V) (endAddr := endAddr) D hD hd budget R cap fit
    (enter ∘ bodyPC pc) (bodyReg dfs priv apart) pubSlot (caller ret) m clock
    (verification_linked pc dfs priv apart ret A data inj) op size arenaLow time room
  unfold LeafVisit.leafParser at semantic
  rw [verification_fields pc dfs priv apart ret A data] at semantic
  have keep : PreservesOperands pc dfs priv apart ret := fun j i h =>
    value_outside dfs priv apart i (LeafImage.destination_mem _ _ _ _ j _ h)
  apply exact pc dfs priv apart ret A data inj rows keep _ _ base m
  · intro node c h
    exact stored_actual data base c.privateMem geometryLow geometryFits h.2
  · exact ⟨fun node s h => semantic.success node s h.1,
      fun node bs c top pending h => semantic.reject node bs c top pending h.1⟩

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
