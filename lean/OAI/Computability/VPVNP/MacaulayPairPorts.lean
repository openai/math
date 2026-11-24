import OAI.Computability.VPVNP.MacaulayCallBank
import OAI.Computability.VPVNP.MacaulayExponentPack
import OAI.Computability.VPVNP.MacaulayScalarRoutines

/-! # Physical ports shared by the two ordinal scans and their entry routine -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open RAMTape UniversalCountStack

/-- `false` designates the source monomial and `true` the column. -/
inductive Field where
  | base (column : Bool) | box (column : Bool) | limit (column : Bool) | ordinal (column : Bool)
  | raw (column : Bool)
  | arity | marker | scale | mark | zero | one | packed | flag
  deriving DecidableEq, Fintype

/-- Private stack ports for the thirteen-register dense ordinal lookup with no public RAM
operands. -/
abbrev OrdBank := RAMTape.ISA.Port 13 0
/-- Private stack ports for the fifteen-register powered-monomial comparison with no public RAM
operands. -/
abbrev PowerBank := RAMTape.ISA.Port 15 0
/-- The disjoint private stacks used by ordinal lookup, residual-exponent packing and
powered-exponent comparison. -/
abbrev Private := OrdBank ⊕ (ExponentPack.Port ⊕ PowerBank)
/-- Complete call frame containing the shared monomial fields, private routine stacks and copy
scratch. -/
abbrev Port := CallBank.Port Field Private

/-- Query parameters for the two monomial scans and the optional shift and scale applied to the
source. -/
structure Inputs where
  /-- Number of variables in both monomials and number of iterations in the exponent packer. -/
  arity : ℕ
  /-- Total-degree bound for the source when false and for the column when true. -/
  degree : Bool → ℕ
  /-- Zero-based position to look up in each of the two bounded-degree monomial enumerations. -/
  ordinal : Bool → ℕ
  /-- Power applied to the source monomial after its possible multiplication by a variable. -/
  scale : ℕ
  /-- One-based coordinate incremented before powering the source. Zero selects an unshifted
  source. -/
  mark : ℕ

/-- Populate the public field stacks with scan parameters, unary markers, supplied raw keys,
output buffers and the zero and one words. -/
def values (w : ℕ) (d : Inputs) (raw : Bool → List Bool) (packed flag : List Bool) : Stacks Field
  | .base c => digits w (d.degree c+1)
  | .box c => digits w ((d.degree c+1)^d.arity)
  | .limit c => digits w (rawSize d.arity (d.degree c))
  | .ordinal c => digits w (d.ordinal c)
  | .raw c => raw c
  | .arity => digits w d.arity
  | .marker => List.replicate d.arity true
  | .scale => digits w d.scale
  | .mark => digits w d.mark
  | .zero => digits w 0
  | .one => digits w 1
  | .packed => packed
  | .flag => flag

/-- Install the public monomial query fields with all private stacks and copy scratch empty. -/
def publicBank (w : ℕ) (d : Inputs) (raw : Bool → List Bool) (packed flag : List Bool) : Stacks Port :=
  CallBank.clean (values w d raw packed flag)

theorem values_le {w B : ℕ} (d : Inputs) (raw : Bool → List Bool) (packed flag : List Bool)
    (hw : w ≤ B) (ht : d.arity ≤ B) (hr : ∀ c, (raw c).length ≤ B) (hp : packed.length ≤ B)
    (hf : flag.length ≤ B) (i : Field) : (values w d raw packed flag i).length ≤ B := by
  cases i <;> simp [values, hw, ht, hr, hp, hf]

theorem update_raw (w : ℕ) (d : Inputs) (raw : Bool → List Bool) (packed flag v : List Bool) (c : Bool) :
    Function.update (values w d raw packed flag) (.raw c) v =
      values w d (Function.update raw c v) packed flag := by
  funext i; cases i with
  | raw j => by_cases h : j=c <;> simp [values, h]
  | _ => rfl

theorem update_packed (w : ℕ) (d : Inputs) (raw : Bool → List Bool) (packed flag v : List Bool) :
    Function.update (values w d raw packed flag) .packed v = values w d raw v flag := by
  funext i; cases i <;> rfl

theorem update_flag (w : ℕ) (d : Inputs) (raw : Bool → List Bool) (packed flag v : List Bool) :
    Function.update (values w d raw packed flag) .flag v = values w d raw packed v := by
  funext i; cases i <;> rfl

/-- Embed a routine's internal ports into the joint private bank while preserving its external
fields and shared scratch port. -/
def embed {I : Type} (f : I → Private) : CallBank.Port Field I → Port
  | .internal i => .internal (f i)
  | .external k => .external k
  | .scratch => .scratch

theorem embed_injective {I : Type} (f : I → Private) (hf : Function.Injective f) :
    Function.Injective (embed f) := by
  rintro (i | i | _) (j | j | _) h <;> simp_all [embed, hf.eq_iff]

/-- Lift a cleaned private call into the shared bank. Ports outside the
installed private block and caller slots are empty throughout the lift. -/
theorem lift_call {I : Type} [DecidableEq I] (f : I → Private) (hf : Function.Injective f)
    (r : FiniteRoutine (CallBank.Port Field I)) {C n : ℕ} {x y : Stacks Field}
    (h : r.BoundedRun C n (CallBank.clean x) (CallBank.clean y)) :
    (r.onPorts (embed f)).BoundedRun C n (CallBank.clean x) (CallBank.clean y) := by
  let st : Stacks Port := CallBank.clean x
  have installed (y : Stacks Field) :
      installStacks (embed f) st (CallBank.clean y) = CallBank.clean y := by
    apply installStacks_frame (ports := embed f) (base := st) (target := CallBank.clean y)
      (small := CallBank.clean y) (embed_injective f hf)
    · intro k; cases k <;> rfl
    · rintro (k | i | _) hout <;> first | rfl | exact (hout (.external k) rfl).elim
  have hh := FiniteRoutine.BoundedRun.onPorts (a := r) (embed_injective f hf) st h (by
    rintro (k | i | _) hout <;> first | exact Nat.zero_le _ | exact (hout (.external k) rfl).elim)
  rwa [installed, installed] at hh

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
