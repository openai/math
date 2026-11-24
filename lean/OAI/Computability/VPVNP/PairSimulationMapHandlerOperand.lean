import OAI.Computability.VPVNP.PairSimulationMapHandlerRun
import OAI.Computability.VPVNP.PairSimulationMapHandlerClock

/-!
# Calling a grouped matrix on its prepared physical operands

The selected role's data are one entry input and the associated resident wire
and descriptor addresses. The native writer reads its six real operands and
publishes the descriptor at the evaluated base. This interface retains every
register and memory frame needed to continue at the next resident row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerOperand

open MotifSelector MotifGrid MotifBlocks MotifConversion MapConstants MotifEntry
open BurstRAM.PrivateRAM CompressorRecords.PhaseRecipe MapHandlerImage
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'} {t shared p r w : ℕ}
  (F : MapHandlerImage.Family B t shared) (hp : ∀ i, 0 < p₀ i) (I : LocalHistory.EntryInput B)
  (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)

/-- The demand-grid point and party selecting the handler for this entry. -/
noncomputable abbrev index : Index B := (demandGrid B hp I.demand, I.party)

/-- The selected handler's map call table layout. -/
noncomputable abbrev layout := F.layout (index hp I)

/-- Memory locations and size bounds for running the selected map on this entry's bits. -/
noncomputable abbrev Workspace := MapEntry.Program.Workspace (MapInline.callProgram (layout F hp I))
  I.demand I.payload (demandBits src dst I.party I.demandBits)
  (mapHalf G (fun _ ↦ inputBits) I.supplyBits) t w

/-- Parameter ordinals reported by the entry evaluator, or `none` on rejection. -/
noncomputable abbrev names := (runEntry B hp I.demand I.payload I.party
  (demandBits src dst I.party I.demandBits) (mapHalf G (fun _ ↦ inputBits) I.supplyBits)).1.map
    (List.map F.ordinal)

variable (c : Config w p r) (m : BurstRAM.Memory w)

/-- Value of the selected handler's `j`-th public operand at entry. -/
noncomputable abbrev pub (j : Fin 5) := c.reg (F.inputs dfs saved common (index hp I) j.castSucc)

/-- Value of the sixth operand, used as the state word in descriptor expressions. -/
noncomputable abbrev state := c.reg (F.inputs dfs saved common (index hp I) (Fin.last 5))

/-- Descriptor base address evaluated from the handler's six operands and external memory. -/
noncomputable abbrev addr := (F.base (index hp I)).eval (pub F hp I dfs saved common c)
  (state F hp I dfs saved common c) m

/-- Numerical and semantic facts established by the selected physical shrink
or refresh operand materializer, at the handler's actual entry configuration. -/
structure Prepared (X : Workspace F hp I) : Prop where
  fit : (addr F hp I dfs saved common c m).val + Fintype.card (MapCallSetup.Arg D E) ≤ 2 ^ w
  fields : ∀ a, (F.field (index hp I) a).eval (pub F hp I dfs saved common c)
    (state F hp I dfs saved common c) m =
      MapCallSetup.values (layout F hp I).core ((layout F hp I).corePC (layout F hp I).locations)
        X a
  resident : MapArgumentWriter.ResidentFields (layout F hp I).core
    ((layout F hp I).corePC (layout F hp I).locations) X
    (addr F hp I dfs saved common c m) c.privateMem
  histogram : ∀ l : Fin t, ((X.hist + l.val : ℕ) : BurstRAM.Word w).val <
      (addr F hp I dfs saved common c m).val ∨
    (addr F hp I dfs saved common c m).val + Fintype.card (MapCallSetup.Arg D E) ≤
      ((X.hist + l.val : ℕ) : BurstRAM.Word w).val
  directory : ∀ (l : Fin t) (i : MapDirectoryInit.Row (layout F hp I).core),
    ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)

/-- This is the physical step consumed by the resident loop. The bound is the
selected handler's clock; its exact external count is the operand expression loads. -/
theorem native (pc : F.Address → Fin p) (own : F.PrivateReg ↪ Fin r) (advance : Fin p)
    (M : Machine w p r 11) (installed : ∀ a,
      M.code (pc a) = (F.text pc dfs saved common own advance a).resize w)
    (banks : F.Apart dfs saved common own) (hw : widthThreshold B ≤ w) (X : Workspace F hp I)
    (hpc : c.pc = F.target pc (index hp I)) (prepared : Prepared F hp I dfs saved common c m X) :
    let i := index hp I
    let a := addr F hp I dfs saved common c m
    ∃ out es, NodeArguments.ChildScan.Prefix M m c out [] es ∧
      es.length ≤ F.clock i (repetitions B I.demand) ∧ BurstRAM.countProbes es = F.probes i ∧
      BurstRAM.choiceBits es = [] ∧
      (if (names F hp I).isSome then out.pc = advance else M.code out.pc = .reject) ∧
      out.persistent = c.persistent ∧
      (∀ q, (∀ b : F.Local i, q ≠ F.localReg own i b) → out.reg q = c.reg q) ∧
      (∀ q, q.val < a.val ∨ a.val + Fintype.card (MapCallSetup.Arg D E) ≤ q.val →
        MapCallSetup.Outside (layout F hp I).core ((layout F hp I).corePC (layout F hp I).locations)
          X q →
        out.privateMem q = c.privateMem q) ∧
      ∀ l : Fin t, out.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) =
        c.privateMem ((X.hist + l.val : ℕ) : BurstRAM.Word w) +
          (((names F hp I).getD []).count l : BurstRAM.Word w) :=
  F.native pc dfs saved common own advance M installed banks hp I hw c m X hpc
    prepared.fit prepared.fields prepared.resident prepared.histogram prepared.directory

end PairSimulation.MapHandlerOperand

end VPVNP
end Computability
end OAI
