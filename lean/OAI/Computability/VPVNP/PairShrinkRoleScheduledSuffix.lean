import OAI.Computability.VPVNP.PairShrinkRoleTreeSuffix

/-!
# Exact suffix of a selected shrinking term

The map acceptance condition at a concrete shrinking vertex asks for each
resident six-party call to return its formal labels. On the stored child and
hidden arguments, this is precisely the condition for extending the hidden
fields to a kernel witness of the chosen term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression Compression.ShrinkMotif CompressorRecords NetworkKernel
open LocalHistory NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess
open private layout supplyWidth from OAI.Computability.VPVNP.PairShrinkRoleMapWitness

variable {K R : Type*} [Field K] [CommRing R] {S : BlockSchedule K} (B : S.Templates)
  (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g w endAddr : ℕ}
  (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
  (sel : X.ShrinkSelection B.shrink)
  (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)

private noncomputable abbrev termAt := (B.shrinkPassAt f hf i rfl X).step.term sel
local notation "Tr" => termAt B f hf i X sel
private noncomputable abbrev readerAt := (shrinkPassReaders B f hf i rfl X).termParsers sel
local notation "rdr" => readerAt B f hf i X sel
local notation "layoutAt" => layout B i X sel
local notation "widthAt" => supplyWidth B i X sel
local notation "hiddenRows" => ShrinkHiddenSlots.rows X layoutAt widthAt v
private noncomputable abbrev childOrder := (rdr).order.children v
local notation "orderAt" => childOrder B f hf i X sel v

set_option maxHeartbeats 2000000 in
-- The scheduled kernel includes the state reindexing and dependent map arguments.
/-- The physical reader and the selected term reader return the same remaining
stream, provided that each map scan tests its specified resident call. -/
theorem scheduledSuffix (new : (Tr).output.Half v)
    (placeholder : Placed (X.packingData.shrinkInternalOwner layoutAt)
      (internalLabel widthAt layoutAt) v)
    (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
    (desc : Word w → ChildArguments.Descriptor w X) (args : List (Child X) → Args w)
    (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
    (loadChild : Setup w endAddr) (loadHidden : List (Child X) → Setup w endAddr)
    (loadMaps : List (Child X) → List Row → Setup w endAddr)
    (node : Word w) (saved : Scratch w endAddr)
    (order : (desc node).sites = List.ofFn fun j => ((orderAt).entries j).val)
    (checks : ∀ (old : Placed (Tr).place X.network.Half v) hidden tail out,
      let xs := children (t := Tr) X v orderAt old
      hiddenReader (args xs) m (hiddenRows placeholder) node
        (hiddenInputScratch A older cap loadChild loadHidden xs node saved)
        (stream (hiddenRows hidden) ++ tail) = some (out, tail) →
      out.value = hiddenRows hidden →
      ((ResidentMapLoop.Exact.scan node (maps xs out.value)
        ((loadMaps xs out.value).updated node out.updated)).isSome ↔
        ∀ q : X.packingData.ResidentMap layoutAt v,
          (MapWitness.names B (MapWitness.input B i X sel v old new hidden q)).isSome))
    (bits : List Bool) :
    ((hook (visitReader A T m older cap desc args (fun _ => hiddenRows placeholder)
      maps loadChild loadHidden loadMaps)).read node saved bits).map Prod.snd =
      ((TreeDecode.nodeReader rdr v new).read bits).map Prod.snd := by
  refine treeSuffix_of_maps (term := Tr) (K := fun x => ((rdr).witness v x new).Choice)
    A T m older cap desc args (fun _ => hiddenRows placeholder) maps
    loadChild loadHidden loadMaps hiddenRows v orderAt node saved (TreeDecode.nodeReader rdr v new)
    (fun _ x => x.1) order ?_ ?_ ?_ ?_ bits
  · intro old x
    change (ChildArguments.placedReader (t := Tr) v orderAt).encode old ++
      ((shrinkPassReaders B f hf i rfl X).kernel sel v old new).encode x = _
    rw [ShrinkHiddenSlots.kernel_encode B f hf i X sel v old new x]
    rfl
  · intro xs bs tail out hit
    exact (hiddenReader_typed X layoutAt widthAt v (args xs) m placeholder hit).exists
  · intro xs hidden tail
    exact hiddenReader_encoded X layoutAt widthAt v (args xs) m placeholder hidden node _ tail
  · intro old hidden tail out xs hit val
    exact (checks old hidden tail out hit val).trans
      (MapWitness.exists_iff B f hf i X sel v old new hidden).symm

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
