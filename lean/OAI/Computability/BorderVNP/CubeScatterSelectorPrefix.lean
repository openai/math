import OAI.Computability.BorderVNP.CubeScatterSharedStreams
import OAI.Computability.BorderVNP.CubeISASelectorRead

/-! # Unique recovery of the physical selectors from a complete common prefix

At any fixed advertised coordinate the accepted packet trials determine the
order of the fixed-width selector words. Each valid little-endian ordinal
chooses exactly one summand. A short prefix, a long prefix, or an unused
ordinal fails the decoding test.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Tally VPVNP.BurstRAM VPVNP.RAMSerialization

variable {n K h : ℕ}

/-- Decode one complete selector field by the same little-endian ordinal used by the native reader. -/
def decodeSelector (n K h : ℕ) (bs : List Bool) : Option (Selector n K h) :=
  if hl : bs.length = selectorWidth n K h then
    let a := (VPVNP.RAMSerialization.wordBits (selectorWidth n K h)).symm (fun j => bs[j.val]'(by rw [hl]; exact j.isLt))
    if ha : a.val < Fintype.card (Selector n K h) then some ((selectorOrder n K h).symm ⟨a.val,ha⟩) else none
  else none

/-- Decoding a selected summand's physical prefix returns that summand. -/
theorem decodeSelector_encode (u : Selector n K h) : decodeSelector n K h (selectorStream u) = some u := by
  let a : Word (selectorWidth n K h) := ⟨(selectorOrder n K h u).val,
    (selectorOrder n K h u).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩
  have eq : (VPVNP.RAMSerialization.wordBits _).symm (fun j : Fin (selectorWidth n K h) =>
      (selectorStream u)[j.val]'(by rw [selectorStream_length]; exact j.isLt)) = a := by
    apply (VPVNP.RAMSerialization.wordBits _).injective
    rw [Equiv.apply_symm_apply]
    funext j
    simp only [selectorStream,List.getElem_ofFn]
    rfl
  simp only [decodeSelector,dite_eq_left (selectorStream_length u),eq]
  have ha : a.val < Fintype.card (Selector n K h) := (selectorOrder n K h u).isLt
  rw [dite_eq_left ha]
  exact congrArg some ((selectorOrder n K h).symm_apply_apply u)

/-- A raw word decodes precisely when it is the unique correct physical selector encoding. -/
theorem decodeSelector_iff (bs : List Bool) (u : Selector n K h) :
    decodeSelector n K h bs = some u ↔ bs = selectorStream u := by
  constructor
  · unfold decodeSelector
    split
    · rename_i hl
      dsimp only
      split
      · rename_i ha
        intro hu
        obtain rfl := Option.some.inj hu
        apply List.ext_getElem (hl.trans (selectorStream_length _).symm)
        intro j hj _
        let k : Fin (selectorWidth n K h) := ⟨j,hl ▸ hj⟩
        have eq := congrFun ((VPVNP.RAMSerialization.wordBits (selectorWidth n K h)).apply_symm_apply
          (fun t => bs[t.val]'(by rw [hl]; exact t.isLt))) k
        simp only [selectorStream,List.getElem_ofFn,Equiv.apply_symm_apply]
        exact eq.symm
      · simp
    · simp
  · rintro rfl
    exact decodeSelector_encode _

/-- Decode the exact number of summands in the physical packet trial list. -/
def decodeSelectors (n K h : ℕ) : ℕ → List Bool → Option (List (Selector n K h))
  | 0,bs => if bs = [] then some [] else none
  | k+1,bs => do
      let u ← decodeSelector n K h (bs.take (selectorWidth n K h))
      let us ← decodeSelectors n K h k (bs.drop (selectorWidth n K h))
      return u::us

/-- A raw prefix is accepted exactly for the ordered list of actual selectors whose
native bit encodings concatenate to that prefix. This includes zero-width selector fields. -/
theorem decodeSelectors_iff (count : ℕ) (bs : List Bool) (us : List (Selector n K h)) :
    decodeSelectors n K h count bs = some us ↔ us.length = count ∧ bs = us.flatMap selectorStream := by
  induction count generalizing bs us with
  | zero =>
    cases bs <;> cases us <;> simp [decodeSelectors]
  | succ k ih =>
    simp only [decodeSelectors,bind,Option.bind_eq_some_iff,pure,Option.some.injEq,decodeSelector_iff,ih]
    constructor
    · rintro ⟨u,head,tail,⟨len,rest⟩,rfl⟩
      exact ⟨by simp [len],by rw [List.flatMap_cons,← head,← rest,List.take_append_drop]⟩
    · cases us with
      | nil => simp
      | cons u us =>
        rintro ⟨len,rfl⟩
        refine ⟨u,?_,us,⟨by simpa using len,?_⟩,rfl⟩
        · rw [List.flatMap_cons,← selectorStream_length u,List.take_append_length]
        · rw [List.flatMap_cons,← selectorStream_length u,List.drop_append_length]

/-- Native fixed-width decoding of a valid symbol-pair prefix visits exactly the
summands at the true physical packets in their increasing trial order. -/
theorem commonSelectors_decode {d blocks : ℕ} (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (sym : Symbols d) :
    decodeSelectors n K h (packetVisits blocks i sym).length (commonSelectors select i sym) =
      some ((packetVisits blocks i sym).map select) := by
  apply (decodeSelectors_iff ..).mpr
  exact ⟨List.length_map _,by simp [commonSelectors,List.flatMap_map,Function.comp_def]⟩

/-- At a fixed grouping coordinate, equality of all shared selector prefixes
forces equality of the complete selector tuple, including packets on different rows. -/
theorem commonSelectors_injective {d blocks : ℕ} (i : Fin (n+1))
    {u v : Packet n d blocks → Selector n K h}
    (eq : ∀ sym : Symbols d, commonSelectors u i sym = commonSelectors v i sym) : u = v := by
  funext p
  let sym := p.1.1 i
  have decoded := (commonSelectors_decode u i sym).symm.trans
    ((congrArg (decodeSelectors n K h (packetVisits blocks i sym).length) (eq sym)).trans
      (commonSelectors_decode v i sym))
  exact List.map_inj_left.mp (Option.some.inj decoded) p ((mem_packetVisits ..).mpr rfl)

/-- For an advertised grouping coordinate, the collection of all raw shared selector
prefixes passes exactly when one complete tuple of physical selectors realizes them.
The grouping coordinate is fixed before this test, so its later minimality check can
use the reconstructed summands. -/
theorem validPrefixes_iff_existsUnique {d blocks : ℕ} (i : Fin (n+1)) (raw : Symbols d → List Bool) :
    (∀ sym, (decodeSelectors n K h (packetVisits blocks i sym).length (raw sym)).isSome) ↔
      ∃! u : Packet n d blocks → Selector n K h, ∀ sym, raw sym = commonSelectors u i sym := by
  classical
  constructor
  · intro valid
    choose us read using fun sym => Option.isSome_iff_exists.mp (valid sym)
    have decode (sym : Symbols d) := (decodeSelectors_iff ..).mp (read sym)
    have index (sym : Symbols d) (p : Packet n d blocks) (hp : p.1.1 i = sym) :
        (packetVisits blocks i sym).idxOf p < (us sym).length := by
      rw [(decode sym).1]
      exact List.idxOf_lt_length_iff.mpr ((mem_packetVisits ..).mpr hp)
    let u (p : Packet n d blocks) := (us (p.1.1 i))[(packetVisits blocks i (p.1.1 i)).idxOf p]'(index _ _ rfl)
    have atIndex (sym : Symbols d) (p : Packet n d blocks) (hp : p.1.1 i = sym) :
        u p = (us sym)[(packetVisits blocks i sym).idxOf p]'(index sym p hp) := by subst sym; rfl
    have hu (sym : Symbols d) : (packetVisits blocks i sym).map u = us sym := by
      apply List.ext_getElem ((List.length_map _).trans (decode sym).1.symm)
      intro k hk _
      have kl : k < (packetVisits blocks i sym).length := by simpa using hk
      let p := (packetVisits blocks i sym)[k]
      have mem : p ∈ packetVisits blocks i sym := List.getElem_mem kl
      have ord : (packetVisits blocks i sym).idxOf p = k := (packetVisits_nodup ..).idxOf_getElem k kl
      simpa only [List.getElem_map,ord] using atIndex sym p ((mem_packetVisits ..).mp mem)
    have field (sym : Symbols d) : raw sym = commonSelectors u i sym := by
      exact (decode sym).2.trans (by rw [← hu sym]; simp [commonSelectors,List.flatMap_map,Function.comp_def])
    exact ⟨u,field,fun v hv => commonSelectors_injective i fun sym => (hv sym).symm.trans (field sym)⟩
  · rintro ⟨u,fields,_⟩ sym
    rw [fields sym,commonSelectors_decode]
    rfl

end Cube.Scatter

end BorderVNP
end Computability
end OAI
