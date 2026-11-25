import OAI.Hierarchy.DescentResetGateCalls
import OAI.Hierarchy.DescentRotorSliceRecords
import OAI.Hierarchy.DescentNamedRotor

namespace OAI
/-! # Actual reusable ROM requests at the unary sites of the trivalent reset rotor -/

namespace Hierarchy.DescentResetGates
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open Computability.BorderVNP.Crossing DescentRotor DescentPhysicalSplit
open scoped BigOperators Classical
noncomputable section
open private Physical.endpoint from OAI.Hierarchy.DescentRotorNetwork
open private Physical.encode Physical.encode_local from OAI.Hierarchy.DescentNamedRotor
variable {K E : Type} [Field K] [Fintype E] {n h C w u : ℕ} (G : Graph n h)
variable {hw : 0<w} {src dst : E→Fin (2^n)} {pay : ℝ} (P : BaseCircuit K G C w u hw src dst pay) (D : ℕ)
abbrev RomKey (G : Graph n h) (C w : ℕ) := Fin (Fintype.card (Entry G.arcs C w))
local notation "N" => Physical.host G.arcs D P.layers C w u
local notation "Q" => Physical.rotor G P D

/-- A root reads its single spine word, decodes the true row's two demand words and all supply
port words, then selects the same scalar ROM entry used by the configured powered layer. -/
def addressTable (r : Fin P.layers) (digit : Fin u) : (N).Tables (Entry G.arcs C w) := fun v wire pins =>
  (P.rotation r,⟨v,Physical.bundle P.layers u w (pins ⟨(v,false),rfl⟩) r digit,
    Physical.bundle P.layers u w (pins ⟨(v,true),rfl⟩) r digit,
    fun p=>Physical.bundle P.layers u (C*w) (wire (Physical.endpoint G.arcs v p)) r digit⟩)

def rootAddress (v : Fin (2^n)) (z : Tuple N v) (r : Fin P.layers) (digit : Fin u) : RomKey G C w :=
  key G.arcs C w (rootTable N (addressTable G P D r digit) v z)

def rotorGates : (Q).Site → Type
  | ⟨_,.inl false⟩ => Fin P.layers × Fin u
  | ⟨_,.inl true⟩ => Unit
  | ⟨_,.inr _⟩ => Unit

instance rotorGatesFinite (t : (Q).Site) : Fintype (rotorGates G P D t) := by
  rcases t with ⟨v,(_|_)|i⟩ <;> dsimp [rotorGates] <;> infer_instance

def rotorRequest : (t : (Q).Site)→ rotorGates G P D t→(Q).Assignment→Ports (fun _ : Physical.Pin (2^n)=>P.layers*(u*w))→Request (RomKey G C w)
  | ⟨v,.inl false⟩,⟨r,digit⟩,a,_ => .lookup (rootAddress G P D v ((decode N a).2 v 0) r digit)
  | ⟨_,.inl true⟩,_,_,_ => .check true
  | ⟨v,.inr i⟩,_,a,x =>
    let left := (decode N a).2 v i.castSucc
    let right := (decode N a).2 v i.succ
    .check (decide (left=right ∧ left i=args N (decode N a).1 x v i))

def rotorCalls : Calls Q (RomKey G C w) where
  Gate := rotorGates G P D
  request := rotorRequest G P D

variable (menu : ∀π,Configures K G.arcs C w π)
local notation "romWord" => rom G.arcs C w (fixedTable menu)

/-- No selected field table is an operand. The only field read at a root is a product of
one immutable ROM entry for each installed layer and carried digit. -/
theorem rotor_correct : Correct Q romWord (rotorCalls G P D) (Physical.rotorTables G P D) := by
  intro a x t
  have read := DescentPhysicalSplit.read_eq N (Physical.hostTables G.arcs P.tables) a x t
  refine read.trans ?_
  rcases t with ⟨v,(_|_)|i⟩
  · change (∏ r,∏digit,P.tables r v _ _ _) = ∏p : Fin P.layers × Fin u,romWord (rootAddress G P D v ((decode N a).2 v 0) p.1 p.2)
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro r _
    apply Finset.prod_congr rfl
    intro k _
    simp only [rootAddress, rootTable, addressTable, P.selected]
    exact (DescentRotor.rom_read G.arcs C w (fixedTable menu) (P.rotation r) v _ _ _).symm
  · change (1:K)=∏ _ : Unit,(if true then 1 else 0)
    simp
  · change Attachment.tap i _ _ _=∏ _ : Unit,(if decide _ then (1:K) else 0)
    simp [Attachment.tap]

def namedRotorCalls : Calls (Physical.namedRotor G P D) (RomKey G C w) :=
  (rotorCalls G P D).adapt (Physical.rawBits src dst u) id (Physical.encode G P)

theorem namedRotor_correct : Correct _ romWord (namedRotorCalls G P D) (Physical.namedTables G P D) :=
  (rotorCalls G P D).adapt_correct _ _ _ romWord _ (rotor_correct G P D menu) (Physical.encode_local (D:=D) G P)

end
end Hierarchy.DescentResetGates

end OAI
