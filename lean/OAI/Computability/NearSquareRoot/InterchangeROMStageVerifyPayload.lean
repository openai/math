import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyLayout
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalPayload

/-! # Verified native repair of an arbitrary-width packet using a selected template -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.Template.Data
open InterchangeROMRepair InterchangeSpectralFibre InterchangeROMRepair.Physical
  StageScript IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip.Dims Space
  InterchangeROM

variable {j threshold f : ℕ} {x : Data} {P G S : Tape} {D : Type}

abbrev Ground (x : Data) := ZMod (x.modulusIndex+1)
abbrev WideIndex (x : Data) := Fin (Raw.rowCount x.m)
abbrev CheckIndex (x : Data) := Fin (Raw.checkCount x.m)
abbrev Address (x : Data) (P G S : Tape) (f : ℕ) := Physical.Positions P G S x.a x.m x.b f
abbrev Wide (x : Data) (P G S : Tape) (f : ℕ) (D : Type) :=
  Physical.Bank x.Ground (Fin x.labels) (x.Address P G S f × D) x.WideIndex
abbrev Short (x : Data) (P G S : Tape) (f : ℕ) (D : Type) :=
  Physical.Bank x.Ground (Fin x.labels) (x.Address P G S f × D) x.CheckIndex

def spec (x : Data) : Spec x.Ground x.WideIndex x.CheckIndex x.m :=
  Raw.decode x.modulusIndex (Raw.rowCount x.m) (Raw.checkCount x.m) x.m x.repair

def half (x : Data) : x.Ground := (Raw.halfCode x.modulusIndex : ℕ)

theorem half_eq (h : Valid j threshold x) : 2*x.half = 1 :=
  Raw.halfCode_spec (good_prime h) (by rw [good_modulus h]; exact h.1.2.1)

theorem spec_accepts (h : Valid j threshold x) : accepts x.spec (Sizes.pencilOrder x.m) x.half = true :=
  (Raw.valid_iff ..).mp h.2.2.2.2.1

variable [Fact (x.modulusIndex+1).Prime] [NeZero x.b]

/-- The pointwise pencil in the predictor uses the selected ground matrices,
minor inverse and the permuted native atlas with the physical payload attached. -/
def stagePayload (h : Valid j threshold x) :
    x.Wide P G S f D → x.Wide P G S f D :=
  eval (withPayload D (nativeLayout h P G S f)).perm
    (stageBank x.rect (rowSel h) (colSel h) x.spec x.middleMatrix)

theorem schedule_payload (h : Valid j threshold x) (data : x.Wide P G S f D) :
    schedule x.spec x.half (flags ∘ Prod.fst) (lift (directions false x.half))
      (lift (directions true x.half)) ((stagePayload h)^[Sizes.pencilOrder x.m]) data =
        swapPayload data := by
  exact schedule_payload_of_pull (rowSel h) (colSel h) (nativeLayout h P G S f)
    (fun q v z => native_pull h q v P G S f z) x.middleMatrix (minor_factor h) x.spec _ x.half (half_eq h)
    (spec_accepts h) data

/-- The schedule compiler on the actual selected literals realizes the native
interchange whenever its generated leaf implementations satisfy their local tape
contracts. The input, output and peak allowance use the compiler's public ABI. -/
theorem command_payload (h : Valid j threshold x)
    (wide : x.Wide P G S f D → List Tree) (short : x.Short P G S f D → List Tree)
    (n : ℕ) (hw : ∀ y, (wide y).length = n)
    (leaf : Leaf → List Tree → List Tree) (dom : Leaf → List Tree → Prop)
    (charge : Leaf → List Tree → Allowance) (cmd : Leaf → Cmd) (header : Tree) (env : Env)
    (act : Realizes leaf dom charge cmd header env)
    (sem : LeafSemantics leaf x.spec x.half (flags ∘ Prod.fst) (lift (directions false x.half))
      (lift (directions true x.half)) (stagePayload h) wide short)
    (good : LeafDomains dom wide short) (data : x.Wide P G S f D)
    (deck : Deck) (base : ℕ) (bg : DeckCap base deck) :
    let d := Sizes.pencilOrder x.m
    let budget := allowance leaf charge header (steps n d) (wide data)
    BoundedFits env (command cmd (steps n d)) (pile 0 (packet header (wide data)) deck)
      (pile 0 (packet header (wide (swapPayload data))) deck) budget.time (base+budget.cap) budget.depth := by
  let d := Sizes.pencilOrder x.m
  have run := command_bounded act _ _ (ready_steps sem good n hw d data) deck base bg
  dsimp only at run ⊢
  rwa [run_steps sem n hw,schedule_payload h] at run

end Interchange.Template.Data

end

end NearSquareRoot
end Computability
end OAI
