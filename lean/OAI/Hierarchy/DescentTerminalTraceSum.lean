import OAI.Hierarchy.DescentTerminalGroupPool
import OAI.Hierarchy.DescentTerminalLocalFactors
import OAI.Hierarchy.CatalystSubstitutionNetwork

namespace OAI
/-! # One static scalar/padding circuit and the multiplicity of its histories -/

namespace Hierarchy.DescentTerminalHost
open CatalystSubstitution ThreeFlat Routing
open ProtocolStackContraction Computability.BorderVNP.Crossing DescentTerminalPorts
open scoped Classical BigOperators
noncomputable section

/-- A deterministic transcript and the public payload select at most one
terminal interpretation. Summing the authentic histories contributes one
copy of each state, without any characteristic-dependent coefficient. -/
theorem sum_decoded {A B F : Type*} [Fintype A] [Fintype B] [AddCommMonoid F]
    (decode : A → Option B) (unique : ∀b,∃! a,decode a=some b) (f : A → F) (g : B → F)
    (no : ∀a,decode a=none→f a=0) (yes : ∀a b,decode a=some b→f a=g b) :
    (∑a,f a)=∑b,g b := by
  choose pick hp only using unique
  let emb : B ↪ A := ⟨pick,fun i j h=>Option.some.inj ((hp i).symm.trans ((congrArg decode h).trans (hp j)))⟩
  calc
    _ = ∑ a ∈ Finset.univ.map emb,f a := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ missing
      cases h : decode a with
      | none => exact no a h
      | some b =>
        exact (missing (Finset.mem_map.mpr ⟨b,Finset.mem_univ _,(only b a h).symm⟩)).elim
    _ = _ := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun b _=>yes (pick b) b (hp b)

variable {F : Type} [Field F] {V J : Type} [Fintype V] [Fintype J] {bins W : ℕ}

def logic (verify : BitNetwork F (Fintype.card V)) (scalar : Fin bins → F)
    (dataPin : DescentTerminalLocalFactors.Pin J bins W → V) : BitNetwork F (Fintype.card V) :=
  plugPair verify (DescentTerminalLocalFactors.network F J W scalar) (H:=Empty) Sum.inl (Sum.inl ∘ dataPin)

theorem logic_value (verify : BitNetwork F (Fintype.card V)) (scalar : Fin bins → F)
    (dataPin : DescentTerminalLocalFactors.Pin J bins W → V) (v : V → Bool) :
    TypedWiring.value (logic verify scalar dataPin) v = TypedWiring.value verify v *
      TypedWiring.value (DescentTerminalLocalFactors.network F J W scalar) (v ∘ dataPin) := by
  rw [logic,plugPair_value,Fintype.sum_unique]
  rfl

theorem logic_size (verify : BitNetwork F (Fintype.card V)) (scalar : Fin bins → F)
    (dataPin : DescentTerminalLocalFactors.Pin J bins W → V) :
    (logic verify scalar dataPin).cells+(logic verify scalar dataPin).internal =
      verify.cells+verify.internal+(Fintype.card J+bins*W) := by
  rw [logic,plugPair_cells,plugPair_internal,DescentTerminalLocalFactors.network_cells,
    DescentTerminalLocalFactors.network_internal,Fintype.card_empty]
  omega

/-- A selected graph carries real electrical endpoints and an embedding
of its occupied incident pairs into the predetermined finite group set. -/
structure Term (F : Type) (geo : ℕ) (P : Type) (bits : P→ℕ) (G : Type) [Fintype G] (w cap : ℕ) where
  graph : Network geo P bits
  table : graph.Tables F
  groupCode : DescentTerminalPorts.Group graph ↪ G
  cableCode : graph.Edge ↪ ℕ
  bound : ∀g,poolSize graph w groupCode g≤cap

variable {geo w cap : ℕ} {P G : Type} {bits : P→ℕ} [Fintype G]

def Term.counts (t : Term F geo P bits G w cap) := poolSize t.graph w t.groupCode
def Term.number (t : Term F geo P bits G w cap) := poolIndex t.graph w t.groupCode t.cableCode
def Term.place (t : Term F geo P bits G w cap) (g : G) (_ : Bool) :
    Fin (t.counts g) ↪ Fin cap := Fin.castLEEmb (t.bound g)

theorem Term.eval (t : Term F geo P bits G w cap) (hw : 0<w) (x : Ports bits) :
    let blank : Fin w → Bool := fun _=>false
    (∑ s : Slot G cap → Fin w → Bool,
      (if Linked t.place s then (1:F) else 0)*
      (if Padding t.place blank s then
        (if Slack t.graph (fun u=>s (slotOf t.graph t.number t.place false u)) then
          ∏ v,tableOf t.graph t.number t.place t.table hw x s v else 0) else 0))=t.graph.value t.table x :=
  physical_value_of t.graph t.number t.place t.table hw x

end
end Hierarchy.DescentTerminalHost

end OAI
