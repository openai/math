import OAI.Computability.VPVNP.PairSimulationShrinkMapImage
import OAI.Computability.VPVNP.PairSimulationShrinkGatherBank
import OAI.Computability.VPVNP.PairSimulationShrinkLayoutBranch

/-!
# The shrinking map image with both physical layout gathers

The item reader selects its matrix by the recorded grid and party. At that
address a further header read chooses one of two layouts. Its gather copies
the appropriate old-child and surviving fields before entering the writer.
Only completion of the writer and matrix advances the resident row cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM Compression.ShrinkMotif MotifSelector MotifGrid
open MotifBlocks MotifConversion MapHandlerImage

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F) (S : Registers shared)

/-- Instruction labels for the resident map image, each five-row layout branch, and the gathers. -/
noncomputable abbrev GatherAddress := Address F ⊕ (Index B × Fin 5) ⊕ G.Address

/-- The role's shared registers, handler and gather banks, and layout selection register. -/
noncomputable abbrev GatherRegister := Fin shared ⊕ F.PrivateReg ⊕ G.PrivateReg ⊕ Unit

variable (pc : GatherAddress F G → Fin p) (dfs : Fin 9 ↪ Fin r)
  (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)
  (own : F.PrivateReg ↪ Fin r) (gatherReg : G.PrivateReg ↪ Fin r) (temp : Fin r) (ret : Fin p)

/-- Placement of the resident map image within the full instruction table. -/
noncomputable abbrev corePC : Address F → Fin p := pc ∘ Sum.inl

/-- Address of row `l` in the layout branch for grid point `z` and party `j`. -/
noncomputable abbrev layoutPC (z : B.grid.demands) (j : Fin 6) (l : Fin 5) :=
  pc (.inr (.inl ((z,j), l)))

/-- Placement of the field gather instructions within the full table. -/
noncomputable abbrev gatherPC : G.Address → Fin p := pc ∘ Sum.inr ∘ Sum.inr

/-- Descriptor writer entry reached after gathering operands for grid point `z` and party `j`. -/
noncomputable abbrev writer (z : B.grid.demands) (j : Fin 6) :=
  F.target (handlerPC F (corePC F G pc)) (z,j)

/-- Dispatches a resident item's grid and party to the first row of its layout branch. -/
noncomputable def gatherCases :=
  { cases F S (corePC F G pc) common with target := fun z j ↦ layoutPC F G pc z j 0 }

/-- Original reader, loop and matrix rows retain their jumps. The dispatch
targets now enter the actual layout branch and field gather for each matrix. -/
noncomputable def gatherText : GatherAddress F G → Instr 5 p r 11
  | .inl (.inr (.inr (.inl l))) => (gatherCases F G S pc common).text l
  | .inl l => text F S (corePC F G pc) dfs saved common own ret l
  | .inr (.inl ((z,j),l)) => ShrinkLayoutBranch.code (layoutPC F G pc z j)
    ((S.headerReg common) 0) ((S.headerReg common) 10) temp
    (G.entry (gatherPC F G pc) (writer F G pc) z j) l
  | .inr (.inr l) => G.text (gatherPC F G pc) dfs saved common gatherReg (writer F G pc) l

/-- Each constituent's link inside this single installed word-RAM table. -/
structure GatherLinked (M : Machine w p r 11) : Prop where
  header : MapResidentInputs.HeaderLinked M (inputPC F (corePC F G pc) ∘ Sum.inl)
    (S.headerReg common) (loopPC F (corePC F G pc) false)
  item : MapResidentInputs.ItemLinked M (inputPC F (corePC F G pc) ∘ Sum.inr)
    (S.headerReg common) (casePC F (corePC F G pc) (.inl ()))
  loop : (loop F S (corePC F G pc) common ret).Linked M
  dispatch : (gatherCases F G S pc common).Linked M
  layout : ∀ z j, ShrinkLayoutBranch.Linked M (layoutPC F G pc z j)
    ((S.headerReg common) 0) ((S.headerReg common) 10) temp
    (G.entry (gatherPC F G pc) (writer F G pc) z j)
  gather : ∀ l, M.code (gatherPC F G pc l) =
    (G.text (gatherPC F G pc) dfs saved common gatherReg (writer F G pc) l).resize w
  matrix : ∀ l, M.code (handlerPC F (corePC F G pc) l) =
    (F.text (handlerPC F (corePC F G pc)) dfs saved common own
      (loopPC F (corePC F G pc) true) l).resize w
  bad : M.code (badPC F (corePC F G pc)) = .reject

theorem gatherLinked (M : Machine w p r 11) (install : ∀ a, M.code (pc a) =
    (gatherText F G S pc dfs saved common own gatherReg temp ret a).resize w) :
    GatherLinked F G S pc dfs saved common own gatherReg temp ret M := by
  obtain ⟨h, i⟩ := MapResidentInputs.linked M (inputPC F (corePC F G pc)) (S.headerReg common)
    (loopPC F (corePC F G pc) false) (casePC F (corePC F G pc) (.inl ()))
    (fun a ↦ install (.inl (.inl a)))
  refine ⟨h, i, ⟨install (.inl (.inr (.inl false))), install (.inl (.inr (.inl true)))⟩,
    fun a ↦ install (.inl (.inr (.inr (.inl a)))), ?_, fun a ↦ install (.inr (.inr a)),
    fun a ↦ install (.inl (.inr (.inr (.inr (.inl a))))),
    install (.inl (.inr (.inr (.inr (.inr ())))))⟩
  intro z j l
  exact (install (.inr (.inl ((z,j),l)))).trans (ShrinkLayoutBranch.resize_code ..)

private noncomputable def number (A : Type*) [Finite A] : A ≃ Fin (Nat.card A) := by
  classical
  letI := Fintype.ofFinite A
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- Numbers the instruction labels of the map image with both gathers. -/
noncomputable def gatherLocations := number (GatherAddress F G)

/-- Numbers the registers used by the map image with both gathers. -/
noncomputable def gatherRegisters := number (GatherRegister F G)

/-- Embeds the role's shared registers into the combined segment's numbered bank. -/
noncomputable def gatherShared : Fin shared ↪ Fin (Nat.card (GatherRegister F G)) :=
  Function.Embedding.inl.trans (gatherRegisters F G).toEmbedding

/-- Embeds the map handlers' private registers into the combined segment's numbered bank. -/
noncomputable def gatherMatrix : F.PrivateReg ↪ Fin (Nat.card (GatherRegister F G)) :=
  Function.Embedding.inl.trans (Function.Embedding.inr.trans (gatherRegisters F G).toEmbedding)

/-- Embeds the field gathers' private registers into the combined segment's numbered bank. -/
noncomputable def gatherLocal : G.PrivateReg ↪ Fin (Nat.card (GatherRegister F G)) :=
  Function.Embedding.inl.trans (Function.Embedding.inr.trans
    (Function.Embedding.inr.trans (gatherRegisters F G).toEmbedding))

/-- Number of the scratch register that computes the layout field's address and reads its bit. -/
noncomputable def layoutTemp := gatherRegisters F G (.inr (.inr (.inr ())))

/-- The final-vertex instruction segment for the shrinking map list, including
the materialization of every physical operand field in its selected layout. -/
noncomputable def segmentWithGather : VertexImage.Segment where
  count := Nat.card (GatherAddress F G)
  privateRegs := Nat.card (GatherRegister F G)
  entry := inputPC F (corePC F G (gatherLocations F G)) (.inl 0)
  row place dfs saved locals ret i :=
    gatherText F G S (place ∘ gatherLocations F G) dfs saved ((gatherShared F G).trans locals)
      ((gatherMatrix F G).trans locals) ((gatherLocal F G).trans locals)
      (locals (layoutTemp F G)) ret ((gatherLocations F G).symm i)

theorem gatherSegment_rows (place : Fin (Nat.card (GatherAddress F G)) → Fin p)
    (locals : Fin (Nat.card (GatherRegister F G)) ↪ Fin r) (M : Machine w p r 11)
    (h : ∀ a, M.code (place a) =
      ((segmentWithGather F G S).row place dfs saved locals ret a).resize w)
    (a : GatherAddress F G) :
    M.code ((place ∘ gatherLocations F G) a) =
      (gatherText F G S (place ∘ gatherLocations F G) dfs saved ((gatherShared F G).trans locals)
        ((gatherMatrix F G).trans locals) ((gatherLocal F G).trans locals)
        (locals (layoutTemp F G)) ret a).resize w := by
  simpa [segmentWithGather] using h (gatherLocations F G a)

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
