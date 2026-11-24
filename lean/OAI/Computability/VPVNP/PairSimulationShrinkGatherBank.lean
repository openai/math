import OAI.Computability.VPVNP.PairShrinkPartyNative
import OAI.Computability.VPVNP.PairSimulationMapHandlerImage

/-!
# Relocatable gather code before each shrinking map writer

Each grid, party and layout has a finite instruction range. The range copies
all of the party's AB and surviving fields into its own staging slots and
then jumps to the descriptor writer for that same grid and party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkGatherBank

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open Compression.ShrinkEnergy CompressorRecords CompressorRecords.PhaseRecipe
open MotifBlocks MotifGrid MotifConversion

variable {K : Type} [Field K] {factor : ℝ}
variable {B : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {t shared p r w : ℕ}

/-- Select a shrinking gather by its demand grid point, one of the six motif parties, and the
surviving layout bit. -/
abbrev Key (B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor) :=
  B.grid.demands × Fin 6 × Bool

/-- One fixed shrinking stage uses old and new degree exponents chosen in the schedule. -/
structure Family (_F : MapHandlerImage.Family B t shared) where
  /-- Exponent of the old degree for this shrinking stage. Its degree and color count determine
  the thick-wire frame count. -/
  a : ℕ
  /-- Exponent of the new degree used to determine the number of subdivisions of each surviving
  role. -/
  b : ℕ
  /-- Call-header expressions for each grid point and party, supplying the level, motif,
  argument and hidden-slot geometry, and histogram address. -/
  operands : MapHandlerImage.Index B → ShrinkCallHeader.Operands
  /-- Expression for the parent node whose packet supplies the surviving half-wire bits for a
  grid-point and party handler. -/
  node : MapHandlerImage.Index B → Expr

variable {F : MapHandlerImage.Family B t shared} (G : Family F)

namespace Family

private def handler (i : Key B) : MapHandlerImage.Index B := (i.1, i.2.1)

/-- The four role subdivision counts computed from the stage's old degree, color count, and new
degree. -/
noncomputable def profile := subdivisions (2 ^ G.a) (Shrink.colors G.a) (2 ^ G.b)

/-- Number of thick-wire frames in an AB column, equal to one quarter of the old degree times
the number of color patterns. -/
def thickCount := 2 ^ (Shrink.colors G.a) * 2 ^ G.a / 4

/-- Positions in the ordered list of AB and surviving frames incident to the selected party in
the given layout. -/
noncomputable abbrev Visits (i : Key B) :=
  Fin (ShrinkPartyColumns.visits i.2.1 i.2.2 G.thickCount G.profile).length

/-- Register-setup and frame-copy recipe for each visit, using the selected party's header
operands and parent node expression. -/
noncomputable def setup (i : Key B) : G.Visits i → ResidentColumn.Setup :=
  ShrinkPartyColumns.gather i.2.1 i.2.2 G.thickCount G.profile
    (ShrinkPartyNative.setups (G.operands (handler i)) (G.node (handler i)) G.a G.b i.2.1 i.2.2)

/-- Instruction address consisting of a grid, party, and layout key and a label in that key's
resident column gather. -/
noncomputable abbrev Address := (i : Key B) × ResidentColumn.Label (G.setup i)
/-- Private evaluator register identified by its gather key, frame visit, and operand-compiler
register index. -/
noncomputable abbrev PrivateReg := (i : Key B) × (v : G.Visits i) ×
  Fin (RegisterSetup.regCount ((G.setup i v).operands))

variable (loc : G.Address → Fin p)
variable (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)
variable (own : G.PrivateReg ↪ Fin r) (writer : B.grid.demands → Fin 6 → Fin p)

/-- Place an instruction of the selected resident column gather at its assigned machine program
counter. -/
def rowPC (i : Key B) (l : ResidentColumn.Label (G.setup i)) := loc ⟨i, l⟩

/-- Embed one frame visit's operand-compiler registers into the gather family's private
register allocation. -/
noncomputable def vm (i : Key B) (v : G.Visits i) :
    Fin (RegisterSetup.regCount ((G.setup i v).operands)) ↪ Fin r :=
  (⟨fun a ↦ ⟨i, v, a⟩, fun _ _ h ↦ eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2⟩ :
    Fin _ ↪ G.PrivateReg).trans own

/-- A party with no frames goes directly to its writer. -/
noncomputable def entry (z : B.grid.demands) (j : Fin 6) (l : Bool) :=
  ResidentColumn.start (G.setup (z, j, l)) (G.rowPC loc (z, j, l)) (writer z j) 0

/-- Five-bit template instructions for insertion at arbitrary program locations. -/
noncomputable def text : G.Address → Instr 5 p r 11
  | ⟨i, l⟩ => ResidentColumn.instruction (G.setup i) (G.vm own i)
      (F.inputs dfs saved common (handler i)) (G.rowPC loc i) (writer i.1 i.2.1) l

/-- Installation gives the precise code equation required by the linked native party theorem. -/
theorem linked (M : Machine w p r 11)
    (install : ∀ a, M.code (loc a) = (G.text loc dfs saved common own writer a).resize w)
    (i : Key B) (l : ResidentColumn.Label (G.setup i)) :
    M.code (G.rowPC loc i l) = ResidentColumn.instruction (G.setup i) (G.vm own i)
      (F.inputs dfs saved common (handler i)) (G.rowPC loc i) (writer i.1 i.2.1) l := by
  have twice (op : Instr 2 p r 11) : (op.resize 5).resize w = op.resize w := by
    cases op <;> try rfl
    case constant d a n => simp only [Instr.resize, resize_literal (by decide : 2 ≤ 5)]
  rw [show G.rowPC loc i l = loc ⟨i,l⟩ from rfl, install]
  change (ResidentColumn.instruction (w := 5) _ _ _ _ _ _).resize w = _
  rw [← ResidentColumn.resize_instruction (w := 5), twice, ResidentColumn.resize_instruction]

/-- The gather's private register bank is disjoint from the DFS, saved bootstrap, and shared
registers that provide its inputs. -/
structure Apart : Prop where
  dfs : ∀ x j, own x ≠ dfs j
  saved : ∀ x j, own x ≠ saved j
  common : ∀ x j, own x ≠ common j

/-- No scratch operand can clobber one of the six input registers. -/
theorem safe (apart : G.Apart dfs saved common own) (i : Key B) (v : G.Visits i)
    (a : Fin (RegisterSetup.regCount ((G.setup i v).operands))) (j : Fin 6) :
    G.vm own i v a ≠ F.inputs dfs saved common (handler i) j := by
  unfold MapHandlerImage.Family.inputs
  rcases F.source (handler i) j with h | h | h
  · exact apart.dfs _ h
  · exact apart.saved _ h
  · exact apart.common _ h

/-- A returning gather preserves the loop, DFS and saved bootstrap registers for its writer. -/
theorem preserved (apart : G.Apart dfs saved common own) (i : Key B) {M : Machine w p r 11}
    {row : G.Visits i → ResidentColumn.Row} {mem : Memory w} {cfg out : Config w p r}
    {events : List (Event w)}
    (res : ResidentColumn.Result (G.setup i) (G.vm own i) M (writer i.1 i.2.1) row
      (List.finRange _) mem cfg out events) :
    (∀ j, out.reg (dfs j) = cfg.reg (dfs j)) ∧
      (∀ j, out.reg (saved j) = cfg.reg (saved j)) ∧
      (∀ j, out.reg (common j) = cfg.reg (common j)) :=
  ⟨fun j ↦ res.regs _ (fun _ _ _ ↦ (apart.dfs _ j).symm),
   fun j ↦ res.regs _ (fun _ _ _ ↦ (apart.saved _ j).symm),
   fun j ↦ res.regs _ (fun _ _ _ ↦ (apart.common _ j).symm)⟩

section Execution

open CompressorRecords.ShrinkSlots

variable {g : ℕ} {δ : ℝ} {X : State G.a (packingLaneBits G.a g)}
variable {ready : Ready (2 ^ G.a) (2 * 2 ^ G.a + 1) (2 ^ G.b) δ} {sel : X.ShrinkSelection B}
variable {m : X.packingData.Motif} {party : Fin 6} (z : B.grid.demands)
variable (J : ShrinkPartyNative.Job X B ready sel m party w)
local notation "side" => selectedLayout X B sel
local notation "key" => Prod.mk z (Prod.mk party side)
local notation "flatRow" => ShrinkPartyColumns.gather party side G.thickCount G.profile J.row

/-- Enter the installed gather for the selected stage, grid point, party and layout.
Its returning configuration is already at that grid point's descriptor writer. -/
theorem execute {endAddr : ℕ} (M : Machine w p r 11)
    (install : ∀ a, M.code (loc a) = (G.text loc dfs saved common own writer a).resize w)
    (apart : G.Apart dfs saved common own)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
    {level absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
    {heads : SlotLevel.Heads}
    (old : J.OldPublished (G.operands (z, party)) pub state mem level T origin)
    (next : J.SupplyPublished (G.operands (z, party)) (G.node (z, party)) pub state mem heads
      absolute U layer pitch)
    (cfg : Config w p r) (entry : cfg.pc = G.entry loc writer z party side)
    (hp : ∀ j : Fin 5, cfg.reg (F.inputs dfs saved common (z, party) j.castSucc) = pub j)
    (hs : cfg.reg (F.inputs dfs saved common (z, party) (Fin.last 5)) = state)
    (packets : J.Packets endAddr cfg.privateMem) :
    ∃ events out, ResidentColumn.Result (G.setup key) (G.vm own key) M (writer z party)
      flatRow (List.finRange _) mem cfg out events ∧ J.Assembled cfg.privateMem out.privateMem ∧
      (∀ j, out.reg (dfs j) = cfg.reg (dfs j)) ∧
      (∀ j, out.reg (saved j) = cfg.reg (saved j)) ∧
      (∀ j, out.reg (common j) = cfg.reg (common j)) := by
  obtain ⟨ev, out, run, assembled⟩ := ShrinkPartyNative.native_party J (G.operands (z, party))
    (G.node (z, party)) pub state mem old next M (G.vm own key)
    (F.inputs dfs saved common (z, party))
    (G.rowPC loc key) (writer z party) (G.linked loc dfs saved common own writer M install key)
    (G.safe dfs saved common own apart key) cfg entry hp hs packets
  exact ⟨ev, out, run, assembled, G.preserved dfs saved common own writer apart key run⟩

/-- The successful trace and upper scratch are fixed functions of the selected job and inputs.
The gather has no reads outside the stated region and keeps the lower private stack. -/
theorem execute_exact {endAddr : ℕ} (M : Machine w p r 11)
    (install : ∀ a, M.code (loc a) = (G.text loc dfs saved common own writer a).resize w)
    (apart : G.Apart dfs saved common own)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
    {level absolute : Word w} {T U : IncidenceDirectory w} {origin layer pitch : ℕ}
    {heads : SlotLevel.Heads}
    (old : J.OldPublished (G.operands (z, party)) pub state mem level T origin)
    (next : J.SupplyPublished (G.operands (z, party)) (G.node (z, party)) pub state mem heads
      absolute U layer pitch)
    (allowed : ℕ → Prop) (sites : ∀ c i, (J.row c i).ReadSafe
      (ShrinkPartyNative.setups (G.operands (z, party)) (G.node (z, party)) G.a G.b party side c i)
        allowed pub state mem)
    (cfg : Config w p r) (entry : cfg.pc = G.entry loc writer z party side)
    (hp : ∀ j : Fin 5, cfg.reg (F.inputs dfs saved common (z, party) j.castSucc) = pub j)
    (hs : cfg.reg (F.inputs dfs saved common (z, party) (Fin.last 5)) = state)
    (packets : J.Packets endAddr cfg.privateMem) :
    let es := J.trace (G.operands (z, party)) (G.node (z, party)) pub state mem
    ∃ out, ResidentColumn.Result (G.setup key) (G.vm own key) M (writer z party)
      flatRow (List.finRange _) mem cfg out es ∧ J.Assembled cfg.privateMem out.privateMem ∧
      SourceTransport.Reads allowed es ∧
      DFS.scratch endAddr out.privateMem = J.updated endAddr (DFS.scratch endAddr cfg.privateMem) ∧
      (∀ a : Word w, a.val < endAddr → out.privateMem a = cfg.privateMem a) ∧
      (∀ j, out.reg (dfs j) = cfg.reg (dfs j)) ∧
      (∀ j, out.reg (saved j) = cfg.reg (saved j)) ∧
      (∀ j, out.reg (common j) = cfg.reg (common j)) := by
  intro es
  obtain ⟨out, run, assembled, reads, upper, lower⟩ := ShrinkPartyNative.native_party_reads J
    (G.operands (z, party)) (G.node (z, party)) pub state mem old next M (G.vm own key)
    (F.inputs dfs saved common (z, party)) (G.rowPC loc key) (writer z party)
    (G.linked loc dfs saved common own writer M install key) (G.safe dfs saved common own apart key)
    allowed sites cfg entry hp hs packets
  exact ⟨out, run, assembled, reads, upper, lower, G.preserved dfs saved common own writer
    apart key run⟩

end Execution

end Family

end PairSimulation.ShrinkGatherBank

end VPVNP
end Computability
end OAI
