import OAI.ThreeFlat.Routing.CallTagSort
import OAI.ThreeFlat.Routing.CallTagWord
import OAI.ThreeFlat.FlipPins

namespace OAI
/-! # A tag verifier on flags and unit identifiers

Each of the two banks counts its earlier idle records and forms an identification
word at every position. A bitonic switch checks those words on the proposed
tags. All rank bits and all identification words are internal.
-/

namespace ThreeFlat.Routing.CallPool.CallTagVerifier

open scoped Classical BigOperators
noncomputable section

abbrev Pin (n d : ℕ) := (Fin (2^n) × Fin n) ⊕ (Bool × Fin (2^n) × Option (Fin d))
abbrev Bus (n d : ℕ) :=
  (Bool × Fin (2^n) × Fin n) ⊕ (Bool × Fin (2^n) × Fin (1+d+n))

def pins {n d : ℕ} (tags : Fin (2^n) → Fin n → Bool)
    (active : Bool → Fin (2^n) → Bool) (id : Bool → Fin (2^n) → Fin d → Bool) : Pin n d → Bool
  | .inl (i,j) => tags i j
  | .inr (b,i,none) => active b i
  | .inr (b,i,some j) => id b i j

def stagePin (n d : ℕ) : Option (Bool ⊕ Bool) → Type
  | none => SwitchPin n (1+d+n)
  | some (.inl _) => CallTagPrefix.Pin (2^n) n
  | some (.inr _) => CallTagWord.Pin (2^n) d n

instance (n d : ℕ) (g : Option (Bool ⊕ Bool)) : Fintype (stagePin n d g) := by
  rcases g with _ | (b | b) <;> dsimp [stagePin] <;> infer_instance

def mask {n : ℕ} : CallTagPrefix.Pin (2^n) n → Bool
  | .inl _ => true
  | .inr _ => false

def stage (F : Type*) [Zero F] [One F] (n d : ℕ) :
    (g : Option (Bool ⊕ Bool)) → BitNetwork F (Fintype.card (stagePin n d g))
  | none => CallTagSort.network F n (1+d+n)
  | some (.inl _) => TypedWiring.flipPins (CallTagPrefix.network F (2^n) n) mask
  | some (.inr _) => CallTagWord.network F (2^n) d n

def wire (n d : ℕ) : (g : Option (Bool ⊕ Bool)) → stagePin n d g → Pin n d ⊕ Bus n d
  | none, .inl k => .inl (.inl k)
  | none, .inr p => .inr (.inr p)
  | some (.inl b), .inl i => .inl (.inr (b,i,none))
  | some (.inl b), .inr p => .inr (.inl (b,p))
  | some (.inr b), .inl i => .inl (.inr (b,i,none))
  | some (.inr b), .inr (.inl (i,j)) => .inl (.inr (b,i,some j))
  | some (.inr b), .inr (.inr (.inl p)) => .inr (.inl (b,p))
  | some (.inr b), .inr (.inr (.inr p)) => .inr (.inr (b,p))

/-- The verifier's pins consist of proposed addresses and each side's unit metadata. -/
def network (F : Type*) [Zero F] [One F] (n d : ℕ) : BitNetwork F (Fintype.card (Pin n d)) :=
  TypedWiring.glue (stage F n d) (wire n d)

/-- The exact checked identification data depend only on the provided flags and unit fields. -/
def records {n d : ℕ} (active : Bool → Fin (2^n) → Bool)
    (id : Bool → Fin (2^n) → Fin d → Bool) (b : Bool) (i : Fin (2^n)) :=
  CallTagWord.word (active b i) (id b i) (CallTagPrefix.words n (fun t => !(active b t)) i)

theorem network_cells (F : Type*) [Zero F] [One F] (n d : ℕ) :
    (network F n d).cells ≤
      8192*(n+(1+d+n)+1)*(2^n)*(n+1)^2 + 2*(40*(2^n+2*(2^n*n))) + 2*(40*(2^n*(1+d+n))) := by
  simp only [network,TypedWiring.glue_cells,Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_bool,stage,
    TypedWiring.flipPins, BitNetwork.flipPins]
  have hs := CallTagSort.cells F n (1+d+n)
  have hp := CallTagPrefix.network_cells F (2^n) n
  have hw := CallTagWord.network_cells F (2^n) d n
  omega

theorem network_internal (F : Type*) [Zero F] [One F] (n d : ℕ) :
    (network F n d).internal ≤ 2*((2^n)*n)+2*((2^n)*(1+d+n)) +
      8193*(n+(1+d+n)+1)*(2^n)*(n+1)^2 +
      2*((2^n)*(n+1)+40*((2^n)+2*((2^n)*n)))+2*(40*((2^n)*(1+d+n))) := by
  simp only [network,TypedWiring.glue_internal,Fintype.sum_option,Fintype.sum_sum_type,Fintype.sum_bool,
    stage,TypedWiring.flipPins,BitNetwork.flipPins,Bus,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
  have hs := CallTagSort.internal F n (1+d+n)
  have hp := CallTagPrefix.network_internal F (2^n) n
  have hw := (CallTagWord.network_internal F (2^n) d n).trans (CallTagWord.network_cells F (2^n) d n)
  omega

end
end ThreeFlat.Routing.CallPool.CallTagVerifier

end OAI
