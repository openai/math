import OAI.Computability.BorderVNP.PackedCutCircuit
import OAI.Computability.BorderVNP.ShortenStaticRowsOccupancy

/-!
# Boolean serializer for the old-band rectangles

Every reserved output row has a statically known kind and band. Its enable
bit uses only the old-row occupancy, old charge bit, and the band's matchedBand
flag. Empty matched intervals still own both hooks. Absent rows emit the
designated padding-site loop with width zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows.Serializer

open Crossing SeedIntervals VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Occupancy, old charge and endpoint orientation input pins. -/
inductive Flag | occupied | charged | positive deriving DecidableEq
instance : Fintype Flag := ⟨{.occupied,.charged,.positive}, by intro f; cases f <;> simp⟩

/-- Input words for one reserved row. Terminal words are the two seed-site addresses. -/
inductive Word | oldSrc | oldDst | span | terminalPos | terminalNeg | pad deriving DecidableEq
instance : Fintype Word := ⟨{.oldSrc,.oldDst,.span,.terminalPos,.terminalNeg,.pad}, by intro f; cases f <;> simp⟩

/-- Word columns of each candidate edge row. Its occupancy bit is emitted separately. -/
inductive Column | src | dst | width deriving DecidableEq
instance : Fintype Column := ⟨{.src,.dst,.width}, by intro f; cases f <;> simp⟩

/-- One fixed input block per candidate row. -/
abbrev Input (w : ℕ) := Flag ⊕ (Word × Fin w)

/-- Occupancy and three word-valued columns of one output row. -/
abbrev Output (w : ℕ) := Unit ⊕ (Column × Fin w)

/-- A tail and a residual band always remain in the old exterior. -/
def isPrefix {D : ℕ} : Band D → Bool
  | some (_,true) => true
  | _ => false

/-- Kind 0 is the old source hook, kind 1 the destination hook, kind 2 the retained cable. -/
def enabled (kind : Fin 3) (matchedBand : Bool) (flag : Flag → Bool) : Bool :=
  flag .occupied && (if kind.val = 2 then !(flag .charged && matchedBand) else flag .charged && matchedBand)

/-- Word columns of the physically occupied candidate, before the padding mux. -/
def activeWord (kind : Fin 3) (positive : Bool) (v : Word → ℕ) : Column → ℕ
  | .width => v .span
  | .src => if kind.val = 1 then v .oldDst else v .oldSrc
  | .dst => if kind.val = 2 then v .oldDst else
      if (if kind.val = 0 then positive else !positive) then v .terminalPos else v .terminalNeg

/-- Arithmetic specification of a serialized row, including all unused candidate holes. -/
def columnValue (kind : Fin 3) (matchedBand : Bool) (flag : Flag → Bool) (v : Word → ℕ) (column : Column) : ℕ :=
  if enabled kind matchedBand flag then activeWord kind (flag .positive) v column
  else if column = .width then 0 else v .pad

private def enableBit {w : ℕ} (kind : Fin 3) (matchedBand : Bool) : Expr (Input w) :=
  let matched := (.input (.inl .charged) : Expr (Input w)).and (.const matchedBand)
  (.input (.inl .occupied) : Expr (Input w)).and (if kind.val = 2 then matched.not else matched)

private def activeBit {w : ℕ} (kind : Fin 3) (column : Column) (i : Fin w) : Expr (Input w) :=
  let f (v : Word) : Expr (Input w) := .input (.inr (v,i))
  match column with
  | .width => f .span
  | .src => if kind.val = 1 then f .oldDst else f .oldSrc
  | .dst => if kind.val = 2 then f .oldDst else
      let flag : Expr (Input w) := .input (.inl .positive)
      mux (if kind.val = 0 then flag else flag.not) (f .terminalPos) (f .terminalNeg)

private def rowBit {w : ℕ} (kind : Fin 3) (matchedBand : Bool) : Output w → Expr (Input w)
  | .inl _ => enableBit kind matchedBand
  | .inr (c,i) => mux (enableBit kind matchedBand) (activeBit kind c i)
      (if c = .width then .const false else .input (.inr (.pad,i)))

private theorem enable_eval {w : ℕ} (kind : Fin 3) (matchedBand : Bool) (z : Input w → Bool) :
    (enableBit kind matchedBand).eval z = enabled kind matchedBand (z ∘ Sum.inl) := by
  by_cases h : kind.val = 2 <;> simp [enableBit,enabled,h,StatementCircuit.Expr.eval]

private theorem active_eval {w : ℕ} (kind : Fin 3) (c : Column) (z : Input w → Bool) :
    value (fun i => (activeBit kind c i).eval z) =
      activeWord kind (z (.inl .positive)) (fun v => value (fun i => z (.inr (v,i)))) c := by
  cases c
  · by_cases hk : kind.val = 1 <;> simp [activeBit,activeWord,hk,StatementCircuit.Expr.eval]
  · by_cases h₂ : kind.val = 2 <;> by_cases h₀ : kind.val = 0 <;> cases hpos : z (.inl .positive) <;>
      simp [activeBit,activeWord,h₂,h₀,hpos,mux_eval,StatementCircuit.Expr.eval]
  · rfl

private theorem row_value {w : ℕ} (kind : Fin 3) (matchedBand : Bool) (z : Input w → Bool) (c : Column) :
    value (fun i => (rowBit kind matchedBand (.inr (c,i))).eval z) =
      columnValue kind matchedBand (z ∘ Sum.inl) (fun f => value (fun i => z (.inr (f,i)))) c := by
  have hzero (n : ℕ) : value (fun _ : Fin n => false) = 0 := by
    induction n with | zero => rfl | succ n ih => simp [value, ih]
  cases hp : enabled kind matchedBand (z ∘ Sum.inl)
  · cases c <;> simp [rowBit,columnValue,mux_eval,enable_eval,hp,StatementCircuit.Expr.eval,hzero]
  · simpa only [rowBit,columnValue,mux_eval,enable_eval,hp,ite_true,Function.comp_apply] using active_eval kind c z

private theorem row_size {w : ℕ} (kind : Fin 3) (matchedBand : Bool) (z : Output w) :
    (rowBit kind matchedBand z).size ≤ 64 := by
  rcases z with _ | ⟨c,i⟩
  · by_cases h : kind.val = 2 <;> simp [rowBit,enableBit,h,StatementCircuit.Expr.size]
  · by_cases h₂ : kind.val = 2 <;> by_cases h₁ : kind.val = 1 <;> by_cases h₀ : kind.val = 0 <;>
      cases c <;> simp [rowBit,enableBit,activeBit,h₂,h₁,h₀,mux,StatementCircuit.Expr.size]

variable {R σ : Type*} [Fintype R] [Fintype σ] {w : ℕ}

/-- Emit all padded rows on shared input pins. No gate list is replicated across bits of a cable. -/
noncomputable def frame (kind : R → Fin 3) (matchedBand : R → Bool)
    (source : Frame σ (R × Input w)) : Frame σ (R × Output w) :=
  source.step fun (z : R × Output w) => (rowBit (kind z.1) (matchedBand z.1) z.2).rename (Prod.mk z.1)

/-- Linear row-count bound with only a linear word-bit multiplier for the final mux stage. -/
theorem frame_size (kind : R → Fin 3) (matchedBand : R → Bool) (source : Frame σ (R × Input w)) :
    (frame kind matchedBand source).size ≤ source.size + Fintype.card R * (64*(1+3*w)) := by
  unfold frame
  have he := Frame.step_size_le source
    (fun (z : R × Output w) => (rowBit (kind z.1) (matchedBand z.1) z.2).rename (Prod.mk z.1)) 64
    (fun z => by simpa using row_size (kind z.1) (matchedBand z.1) z.2)
  have hc : Fintype.card Column = 3 := by decide
  simpa [Output,hc,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using he

/-- The shared-gate circuit returns exactly the specified occupancy and all three field words. -/
theorem frame_eval (kind : R → Fin 3) (matchedBand : R → Bool) (source : Frame σ (R × Input w))
    (x : σ → Bool) (r : R) :
    let z := fun i => source.eval x (r,i)
    (frame kind matchedBand source).eval x (r,.inl ()) = enabled (kind r) (matchedBand r) (z ∘ Sum.inl) ∧
      ∀ c, value (fun i => (frame kind matchedBand source).eval x (r,.inr (c,i))) =
        columnValue (kind r) (matchedBand r) (z ∘ Sum.inl) (fun f => value (fun i => z (.inr (f,i)))) c := by
  simp only [frame,Frame.step_eval,StatementCircuit.Expr.eval_rename]
  exact ⟨enable_eval _ _ _, fun c => row_value _ _ _ c⟩

end Shortening.StaticRows.Serializer

end BorderVNP
end Computability
end OAI
