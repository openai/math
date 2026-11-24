import OAI.Computability.VPVNP.PairShrinkRoleSuffix
import OAI.Computability.VPVNP.PairShrinkRoleMapWitness

/-!
# Comparing a shrinking visit with its typed kernel reader

At a vertex the first guesses describe the placed old half-wires, and the
next guesses describe the hidden assignments. The native scratch after both
writes supplies the resident map checks. Matching those deterministic checks
to the chosen kernel gives equality of the suffix on every input tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS Compression CompressorRecords NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess

variable {w endAddr a g : ℕ} {R L : Type*} {X : State a g} {term : Term R X.network}
  (A : Arena) (T : IncidenceDirectory w) (m : Memory w)
  (older cap : ℕ) (desc : Word w → ChildArguments.Descriptor w X)
  (args : List (Child X) → Args w) (seed : List (Child X) → List Row)
  (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
  (loadChild : Setup w endAddr) (loadHidden : List (Child X) → Setup w endAddr)
  (loadMaps : List (Child X) → List Row → Setup w endAddr)

/-- The private cells used by the hidden scan, after storing the old
arguments and running the hidden-stage setup. -/
noncomputable def hiddenInputScratch (xs : List (Child X)) (node : Word w)
    (saved : Scratch w endAddr) :=
  (loadHidden xs).updated node
    (writePackets A (xs.map (Child.packet X older cap)) (loadChild.updated node saved))

private theorem some_suffix {α : Type*} (o : Option (α × List Bool)) (tail : List Bool) :
    o.map Prod.snd = some tail ↔ ∃ out, o = some (out, tail) := by
  cases o with
  | none => simp
  | some pair => obtain ⟨x,b⟩ := pair; simp

private theorem hook_suffix {α : Type*} (read : Reader w endAddr α) (node : Word w)
    (saved : Scratch w endAddr) (bits : List Bool) :
    ((hook read).read node saved bits).map Prod.snd = (read node saved bits).map Prod.snd := by
  cases hr : read node saved bits with
  | none => simp [hook, hr]
  | some pair => obtain ⟨x,b⟩ := pair; simp [hook, hr]

variable {H : Type} (rowData : H → List Row) (v : term.output.Site) (ord : Order (term.Preimage v))
  (node : Word w) (saved : Scratch w endAddr)

local notation "Old" => Placed term.place X.network.Half v
local notation "oldList" => children X v ord
local notation "beforeHidden" => hiddenInputScratch A older cap loadChild loadHidden
local notation "nativeReader" => visitReader A T m older cap desc args seed maps
  loadChild loadHidden loadMaps

/-- The child and hidden decoders give their exact typed prefixes. Only the
deterministic test on the resulting resident fields depends on the kernel. -/
theorem treeSuffix_of_maps {K : Old → Type} (C : ChoiceReader ((x : Old) × K x))
    (hidden : ∀ x, K x → H)
    (order : (desc node).sites = List.ofFn fun j => (ord.entries j).val)
    (enc : ∀ x k, C.encode ⟨x, k⟩ =
      (ChildArguments.placedReader v ord).encode x ++ stream (rowData (hidden x k)))
    (sound : ∀ xs bs tail out, hiddenReader (args xs) m (seed xs) node
      (beforeHidden xs node saved) bs = some (out, tail) →
      ∃ h, out.value = rowData h ∧ bs = stream (rowData h) ++ tail)
    (complete : ∀ xs h tail, ∃ out, hiddenReader (args xs) m (seed xs) node
      (beforeHidden xs node saved) (stream (rowData h) ++ tail) = some (out, tail) ∧
      out.value = rowData h)
    (checks : ∀ x h tail out, let xs := oldList x
      hiddenReader (args xs) m (seed xs) node (beforeHidden xs node saved)
        (stream (rowData h) ++ tail) = some (out, tail) →
      out.value = rowData h →
      ((ResidentMapLoop.Exact.scan node (maps xs out.value)
        ((loadMaps xs out.value).updated node out.updated)).isSome ↔ ∃ k, hidden x k = h))
    (bits : List Bool) :
    ((hook nativeReader).read node saved bits).map Prod.snd = (C.read bits).map Prod.snd := by
  rw [hook_suffix]
  apply Option.ext
  intro rest
  rw [some_suffix, some_suffix, visitReader_suffix_iff]
  constructor
  · rintro ⟨o,tail,out,childRun,hidRun,pass⟩
    obtain ⟨x,⟨rfl,part⟩,_⟩ := ChildArguments.reader_unique_placed A T m older cap desc v ord node
      (loadChild.updated node saved) order childRun
    obtain ⟨h,eqn,prefixEq⟩ := sound (oldList x) tail rest out hidRun
    rw [prefixEq] at hidRun
    obtain ⟨k,hk⟩ := (checks x h rest out hidRun eqn).mp pass
    refine ⟨⟨x, k⟩,(C.read_iff ..).mpr ?_⟩
    rw [enc, hk, List.append_assoc, ← prefixEq]
    exact part
  · rintro ⟨⟨x, k⟩,hr⟩
    have part := (C.read_iff ..).mp hr
    rw [enc, List.append_assoc] at part
    let xs := oldList x
    let remain := stream (rowData (hidden x k)) ++ rest
    let o := ChildArguments.outcome A T m older cap desc node (loadChild.updated node saved) xs
    obtain ⟨out,hidRun,eqn⟩ := complete xs (hidden x k) rest
    refine ⟨o,remain,out,?_,hidRun,(checks x (hidden x k) rest out hidRun eqn).mpr ⟨k,rfl⟩⟩
    rw [part]
    exact ChildArguments.reader_placed A T m older cap desc v ord node _ order x remain

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
