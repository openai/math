import OAI.Computability.BorderVNP.PackedHistoryBroadcast
import OAI.Computability.BorderVNP.TransmissionHeaderFields
import OAI.Computability.BorderVNP.PackedHistoryOuterCapacity

/-! # Reading the dependent outer pack history from the native header copy

The first copied word is the evaluation mode. The reserved profile word begins
one address later, before the declarations and subtotal claims. The physical
bits include the forced zero suffix of the profile reservation. The public
profile equivalence decodes them to the original dependent history index and
its represented final state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP.BurstRAM VPVNP.VerifierNetwork Packing TeamContraction JointHeader
open DiagonalResidueRAM (word word_val)
open RoutingISA (readings)

variable {R d w reserve : ℕ}

/-- Read the first auxiliary field of the evaluation header from the actual RAM. -/
def profileRAM (m : Memory w) (base : ℕ) (i : Fin reserve) : Bool :=
  decide ((m (base+1+i.val)).val = 1)

/-- The profile precedes every declaration and subtotal word. The returned machine word
is exactly the Boolean field bit at the specified offset, also when the machine width is zero. -/
theorem profile_word_at {m : Memory w} {base tallyBits : ℕ} (profile : Fin reserve → Bool)
    (declarations : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt m base (evaluation (List.ofFn profile ++ declarations) tallyBits claims))
    (i : Fin reserve) : m (base+1+i.val) = word w (profile i).toNat := by
  have tail := FlatAt.right (xs := [true])
    (ys := (List.ofFn profile ++ declarations) ++ (DiagonalTallyRAM.broadcast tallyBits claims).flatten) copy
  have bank : FlatAt m (base+1) (List.ofFn profile) := tail.left.left
  have hi : i.val < (List.ofFn profile).length := by simp
  have h := bank ⟨i.val,hi⟩
  change m (base+1+i.val) = word w (List.ofFn profile)[i.val].toNat at h
  simpa only [List.getElem_ofFn] using h

/-- Optional zero padding of the common physical header leaves each profile read at
the same absolute address. -/
theorem profile_word_at_padded {m : Memory w} {base tallyBits extra : ℕ} (profile : Fin reserve → Bool)
    (declarations : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt m base (padded (evaluation (List.ofFn profile ++ declarations) tallyBits claims) extra))
    (i : Fin reserve) : m (base+1+i.val) = word w (profile i).toNat :=
  profile_word_at profile declarations claims copy.left i

/-- At positive width, the natural readings of every copied profile bit are precisely zero or one. -/
theorem profile_reading_at {m : Memory w} {base tallyBits extra : ℕ} (hw : 0 < w)
    (profile : Fin reserve → Bool) (declarations : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt m base (padded (evaluation (List.ofFn profile ++ declarations) tallyBits claims) extra))
    (i : Fin reserve) : readings m (base+1+i.val) = (profile i).toNat := by
  change (m _).val = _
  rw [profile_word_at_padded profile declarations claims copy, word_val _ _
    ((Bool.toNat_lt _).trans_le (Nat.one_lt_two_pow hw.ne'))]

/-- Decode the whole fixed-width bank directly from RAM, before consuming declarations
and tally bits. -/
theorem profileRAM_eq_of_copy {m : Memory w} {base tallyBits extra : ℕ} (hw : 0 < w)
    (profile : Fin reserve → Bool) (declarations : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt m base (padded (evaluation (List.ofFn profile ++ declarations) tallyBits claims) extra)) :
    profileRAM m base = profile := by
  funext i
  change decide (readings m (base+1+i.val) = 1) = profile i
  rw [profile_reading_at hw profile declarations claims copy i]
  cases profile i <;> rfl

/-- Reading the unpadded header gives the same entire profile bank. -/
theorem profileRAM_eq {m : Memory w} {base tallyBits : ℕ} (hw : 0 < w)
    (profile : Fin reserve → Bool) (declarations : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt m base (evaluation (List.ofFn profile ++ declarations) tallyBits claims)) :
    profileRAM m base = profile :=
  profileRAM_eq_of_copy (extra := 0) hw profile declarations claims (by simpa [padded] using copy)

/-- A valid physical profile copy has the zero machine word at every unused
reserved position, independently of any subsequent declaration or claim. -/
theorem profileRAM_padding {α : Type*} {active : ℕ} (order : α ≃ Fin active) (fit : active ≤ reserve)
    (ok : (α → Bool) → Prop) {m : Memory w} {base tallyBits extra : ℕ}
    (profile : Fin reserve → Bool) (valid : validProfile order fit ok profile)
    (declarations : List Bool) (claims : Fin R → Fin d → ℕ)
    (copy : FlatAt m base (padded (evaluation (List.ofFn profile ++ declarations) tallyBits claims) extra))
    (i : Fin reserve) (hi : active ≤ i.val) : m (base+1+i.val) = 0 := by
  rw [profile_word_at_padded profile declarations claims copy i,valid.2 i hi]
  rfl

/-- Removing the reserved zero suffix from a broadcast word restores all the bits
of the checked encoder, including encoders whose states carry capacity proofs. -/
theorem readProfile_of_broadcast {I α : Type*} {active : ℕ} (order : α ≃ Fin active)
    (fit : active ≤ reserve) (ok : (α → Bool) → Prop) (checked : I ≃ {g // ok g}) (q : I) :
    readProfile order fit ((acceptedBroadcastOfEquiv order fit ok checked) q).val = (checked q).val := by
  change readProfile order fit (paddedProfile order (checked q).val) = _
  funext i
  simp [readProfile,paddedProfile]

/-- Exact physical readback for any checked outer profile equivalence. The recovered active
bits are the actual encoder output, and its inverse on the full padded bank recovers the index. -/
theorem decodeBroadcastOfEquiv_of_copy {I α : Type*} {active : ℕ} (order : α ≃ Fin active)
    (fit : active ≤ reserve) (ok : (α → Bool) → Prop) (checked : I ≃ {g // ok g}) (q : I)
    {m : Memory w} {base tallyBits extra : ℕ} (hw : 0 < w)
    (declarations : List Bool) (claims : Fin R → Fin d → ℕ) :
    let E := acceptedBroadcastOfEquiv order fit ok checked
    FlatAt m base (padded (evaluation (List.ofFn (E q).val ++ declarations) tallyBits claims) extra) →
    (∃ passed, E.symm ⟨profileRAM m base,passed⟩ = q) ∧
      readProfile order fit (profileRAM m base) = (checked q).val := by
  intro E copy
  have h := profileRAM_eq_of_copy hw (E q).val declarations claims copy
  refine ⟨⟨h ▸ (E q).property, E.injective ((E.apply_symm_apply _).trans (Subtype.ext h))⟩,?_⟩
  rw [h]
  exact readProfile_of_broadcast order fit ok checked q

variable {K T : ℕ} {A : ℕ → Type*} {W G : ℕ → Type} [∀ j, Fintype (W j)] [∀ j, Fintype (G j)]
  {σ : Type*} [Fintype σ]
  (bottom : A 0) (epoch : ∀ j, (Fin K → A j) → ProfileSum (A (j+1)))
  (C : Codec (outerSystem T epoch) G) (rep : Represents A W) (step : Steps K T W G)
  (correct : LocalCorrect C rep step) (f : Frame σ (W 0)) (x : σ → Bool) (hx : rep 0 (f.eval x) bottom)
  (width : ℕ → ℕ) (order : ∀ j, G j ≃ Fin (width j)) (fit : broadcastWidth K width T ≤ reserve)

/-- The output state computed from a decoded physical profile represents exactly the
corresponding term of the dependent pack history. This also applies to factory histories,
whose term contains the physical pack and its routes. -/
theorem acceptedOuterBroadcast_state (q : (packHistory bottom epoch T).Index) :
    let bank := acceptedOuterBroadcast bottom epoch C rep step correct f x hx width order fit q
    rep T (output step T le_rfl (repeatLeaf K f T) x (readProfile (broadcastOrder K width order T) fit bank.val))
      ((packHistory bottom epoch T).term q) := by
  intro bank
  let Q := outerEquiv bottom epoch T (le_refl T)
  let idx := Q.symm q
  let code := encode C T (le_refl T) (repeatLeaf K bottom T) idx
  have read : readProfile (broadcastOrder K width order T) fit bank.val = code := by
    change readProfile (broadcastOrder K width order T) fit (paddedProfile (broadcastOrder K width order T) code) = code
    funext i
    simp [readProfile,paddedProfile]
  have hl (n : ℕ) : LeafState rep x n (repeatLeaf K bottom n) (repeatLeaf K f n) := by
    induction n with
    | zero => exact hx
    | succ n ih => exact fun _ => ih
  have hs := (semantics C rep step correct T le_rfl _ _ x (hl T) code).2 idx rfl
  rw [read]
  have finalState := outerEquiv_state bottom epoch T (le_refl T) idx
  change (packHistory bottom epoch T).term (Q idx) = _ at finalState
  rw [show Q idx = q from Q.apply_symm_apply q] at finalState
  exact finalState.symm ▸ hs

/-- Decoding from a valid physical RAM word recovers the unique history and its represented
final state. Distinct histories are distinguished even when their final packs agree. -/
theorem decodeOuterRAM {m : Memory w} {base : ℕ}
    (passed : validProfile (broadcastOrder K width order T) fit
      (fun g => flag step T le_rfl (repeatLeaf K f T) x g = true) (profileRAM m base)) :
    let E := acceptedOuterBroadcast bottom epoch C rep step correct f x hx width order fit
    let q := E.symm ⟨profileRAM m base,passed⟩
    (∃! i, (E i).val = profileRAM m base) ∧
      rep T (output step T le_rfl (repeatLeaf K f T) x
        (readProfile (broadcastOrder K width order T) fit (profileRAM m base)))
        ((packHistory bottom epoch T).term q) := by
  intro E q
  have eqv : E q = ⟨profileRAM m base,passed⟩ := E.apply_symm_apply _
  refine ⟨⟨q,congrArg Subtype.val eqv,fun i hi => E.injective (Subtype.ext (hi.trans (congrArg Subtype.val eqv).symm))⟩,?_⟩
  have state := acceptedOuterBroadcast_state bottom epoch C rep step correct f x hx width order fit q
  change rep T (output step T le_rfl (repeatLeaf K f T) x
    (readProfile (broadcastOrder K width order T) fit (E q).val)) ((packHistory bottom epoch T).term q) at state
  rwa [eqv] at state

/-- A genuine history written into the copied evaluation header decodes back to itself.
The subtotal bank, declaration bits and optional header padding may be arbitrary. -/
theorem decodeOuterRAM_of_copy {m : Memory w} {base tallyBits extra : ℕ} (hw : 0 < w)
    (q : (packHistory bottom epoch T).Index) (declarations : List Bool) (claims : Fin R → Fin d → ℕ) :
    let E := acceptedOuterBroadcast bottom epoch C rep step correct f x hx width order fit
    FlatAt m base (padded (evaluation (List.ofFn (E q).val ++ declarations) tallyBits claims) extra) →
    ∃ passed, E.symm ⟨profileRAM m base,passed⟩ = q := by
  intro E copy
  have h := profileRAM_eq_of_copy hw (E q).val declarations claims copy
  refine ⟨h ▸ (E q).property, ?_⟩
  apply E.injective
  exact (E.apply_symm_apply _).trans (Subtype.ext h)

/-- For the capacity-restricted factory encoder, accepted physical bits still
decode to the original unrestricted history index and its actual final routed pack. -/
theorem boundedOuterRAM_state (good : ∀ j, A j → Prop) (closed : Capacity.Closed (outerSystem T epoch) good)
    (leaf : {a // good 0 a}) (code : Codec (Capacity.restrict (outerSystem T epoch) good closed) G)
    (localOK : LocalCorrect code (fun j z a => rep j z a.val) step) (hLeaf : rep 0 (f.eval x) leaf.val)
    {m : Memory w} {base : ℕ} (passed : validProfile (broadcastOrder K width order T) fit
      (fun g => flag step T le_rfl (repeatLeaf K f T) x g = true) (profileRAM m base)) :
    let checked := acceptedOuterBounded epoch good closed leaf code rep step localOK f x hLeaf
    let E := acceptedBroadcastOfEquiv (broadcastOrder K width order T) fit _ checked
    let q := E.symm ⟨profileRAM m base,passed⟩
    rep T (output step T le_rfl (repeatLeaf K f T) x
      (readProfile (broadcastOrder K width order T) fit (profileRAM m base)))
      ((packHistory leaf.val epoch T).term q) := by
  intro checked E q
  have eqv : E q = ⟨profileRAM m base,passed⟩ := E.apply_symm_apply _
  have h := readProfile_of_broadcast (broadcastOrder K width order T) fit _ checked q
  change readProfile (broadcastOrder K width order T) fit (E q).val = (checked q).val at h
  rw [eqv] at h
  rw [h]
  exact acceptedOuterBounded_state epoch good closed leaf code rep step localOK f x hLeaf q

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
