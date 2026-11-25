import OAI.Computability.BorderVNP.FiniteOutputProduct
import OAI.Computability.BorderVNP.FinitePrivateReturnTape
import OAI.Computability.BorderVNP.FiniteTeamContraction
import OAI.Computability.BorderVNP.TeamSiteProcessor

/-! # Finite-field weights on the actual team processor

The field accumulator changes only on a successful native private halt, where
the finite control still holds the routine number, native state and all scanned
symbols. The signed block subsequently incorporates that halt's sign.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamPrivateTape UniversalMachine Filter
variable {Q Γ : Type} {p r k a m g : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Each routine's arbitrary field output depends on its true scanned symbols
and native terminal state and sign. -/
abbrev Returns (Q Γ F : Type*) (m a : ℕ) := Fin a → FieldSelect.Return Q Γ F m

/-- Decode the live finite-control head bits into the native symbol on every tape. -/
noncomputable def symbols (A : Alphabet Γ g) (bits : Fin (m*g) → Bool) : Fin m → Γ :=
  fun i => A.read (fun j => bits (finProdFinEquiv (i,j)))

omit [Field F] [Fintype F] in
/-- Decoding synchronized track heads reads precisely the original symbols. -/
theorem symbols_tracks (A : Alphabet Γ g) (ts : Fin m → SymbolTape Γ) :
    symbols A (heads (tracks A ts)) = fun i => (ts i).head := by
  funext i
  simpa only [symbols,heads,tracks,Equiv.symm_apply_apply,SymbolTape.track] using A.read_bits (ts i).head

/-- Compensate the original signed halt without dividing by any scalar. -/
def signed (sg : Bool) (z : F) : F := if sg then -z else z

omit [Fintype F] in
/-- The signed terminal multiplication converts the compensating field factor
back to the exact desired value, including zero in all characteristics. -/
theorem signed_cancel (sg : Bool) (z : F) :
    signed sg z * (if sg then -1 else 1) = z := by cases sg <;> simp [signed]

/-- The factor at a private stack control. Loading, sweeping and cleanup are neutral. -/
noncomputable def privateFactor (M : Macro Q Γ m g) (w : FieldSelect.Return Q Γ F m) :
    TeamPrivateCompiler.Control Q m g → F
  | .run (.inl (.ready q bs)) => match (trackTable M.alphabet M.table) q bs with
    | .halt true neg => signed neg (w q (symbols M.alphabet bs) neg)
    | _ => 1
  | _ => 1

/-- The actual processor's finite-control multiplier. Every preparation, probe,
handoff and sorting instruction is neutral. -/
noncomputable def factor {P : TeamOpcode.Program p r k a} (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) : Processor.Label P Q m g → F
  | .block (.loop _ (.privateCall _ j _ q)) => privateFactor (lib j) (w j) q
  | _ => 1

/-- The signed endpoint value retained by the final sorter. -/
def terminal {P : TeamOpcode.Program p r k a} (q : Processor.Label P Q m g) : F :=
  if Processor.negative q then -1 else 1

/-- The unchanged processor instruction table with a finite field accumulator. -/
noncomputable def code (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) :=
  FieldStack.productCode (Processor.code P lib) (factor lib w)

/-- Literal field program carrying the ordinary local validator and the finite accumulator. -/
noncomputable def machine [Fintype Q] (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) : UniversalMachine.Program :=
  FieldStack.clockedMachine TeamSite.Layout.input 36 (code P lib w)
    (FieldStack.productOutput (factor lib w) terminal) (Processor.start,Fintype.equivFin F 1)

/-- At the actual processor exponent 36, its field universal tensor on every
physical payload agrees with the weighted value of the original instruction table. -/
theorem eventually_value [Fintype Q] (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) :
    ∀ᶠ n : ℕ in atTop, ∀ payload : Word, let raw := programPrefix (machine P lib w) ++ payload
      raw.length = n → FPath.U F raw.get = FieldStack.productPaths (Processor.code P lib)
        (factor lib w) terminal (n^36) Processor.start (StackCompiler.labeledInput TeamSite.Layout.input raw) := by
  filter_upwards [FieldStack.eventually_prefix_value TeamSite.Layout.input 36 (by decide) (by decide)
    (code P lib w) (FieldStack.productOutput (factor lib w) terminal) (Processor.start,Fintype.equivFin F 1)] with n hn
  intro payload raw h
  simpa only [raw,machine,code,FieldStack.productCode_value,one_mul] using hn payload h

end FieldProcessor

end BorderVNP
end Computability
end OAI
