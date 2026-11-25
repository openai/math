import OAI.Computability.BorderVNP.ShortenSeedDescriptorEndpoints
import OAI.Computability.BorderVNP.CellSparseSemantics

/-! # Canonical hook words at a sewn terminal

A physical hook in the sewn layout already carries only the clipped interval.
Its local source index therefore starts at zero. At the gathered terminal the
interval starts at its public ordinal. Both orientation choices use that same
ordinal. The complete set of sparse rows forces every bit of the gathered word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open CellSparse Shortening Shortening.SeedIntervals Crossing
open scoped Classical

/-- Bind an already clipped physical hook to the common terminal word. -/
def directHook (desc : CutDescriptor) (hook gathered : Port) : Record :=
  .equal 1 desc.span hook (desc.terminalPort gathered)

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)
variable (binName : A → ℕ) (siteName : N.Site → ℕ) (positive : N.Edge → Bool) (a : A)

private abbrev Old (d : Fin D) := {e : N.Edge // bin e = some (perm d a)}

private noncomputable abbrev W (d : Fin D) (e : Old N bin perm a d) := (layout N bin perm m).width (e.val,some (d,true))

/-- Every axis interval in the ordered matched bundle has its public old-cable preimage. -/
theorem prefixEdge_onto (d : Fin D) : Function.Surjective (prefixEdge N bin perm m a d) := by
  intro z
  have hbin := (bin_selected N bin perm m z.val).trans (by rw [z.property])
  refine ⟨⟨z.val.val.1,hbin⟩,Subtype.ext (Subtype.ext (Prod.ext rfl ?_))⟩
  have h := (Finset.mem_filter.mp z.val.property).2.1
  rw [z.property] at h
  exact h.symm

variable (s : Ports ((layout N bin perm m).cutWidths ((partition N bin perm m).part a)))

/-- The physical value on a specific retained source or destination hook. -/
noncomputable def hookBit (d : Fin D) (e : Old N bin perm a d) (source : Bool) (k : Fin (W N bin perm m a d e)) : Bool :=
  let z := (prefixEdge N bin perm m a d e).val
  if source then s (.inl z) k else s (.inr z) k

variable (hooks : ∀ d, Old N bin perm a d → Bool → Port) (terminal : Fin D × Bool → Port)
private theorem hook_interval_iff (d : Fin D) (e : Old N bin perm a d) (source : Bool)
    (boxes : List (List Factor)) (bank : ℕ → Bool)
    (hread : ∀ k, bank ((hooks d e source).atBit 0 k.val) = hookBit N bin perm m a s d e source k) :
    let B := bundle N bin perm m positive a
    let r := endpointRecord N bin perm m binName siteName positive a d e source
    (directHook r.wire (hooks d e source) (terminal (d,r.side))).Valid boxes bank ↔
        ∀ k : Fin (W N bin perm m a d e), let i := B.order d ⟨prefixEdge N bin perm m a d e,k⟩
          bank ((terminal (d,r.side)).atBit 0 i.val) = B.gather s (d,r.side) i := by
  intro B r
  have hw := descriptor_width N bin perm m binName e (some (d,true))
  have hslot (k : Fin (W N bin perm m a d e)) :=
    terminalPort_atBit N bin perm m binName positive a d e (terminal (d,r.side)) 0 k
  have hvalue (k : Fin (W N bin perm m a d e)) :=
    endpointRecord_gather N bin perm m binName siteName positive a d e source s k
  constructor
  · intro h k i
    exact (congrArg bank (hslot k)).symm.trans
      ((h 0 (by decide) k.val (k.isLt.trans_eq hw)).symm.trans
        ((hread k).trans (hvalue k).symm))
  · intro h copy hcopy k hk
    have hzero : copy = 0 := by omega
    subst copy
    let i : Fin (W N bin perm m a d e) := ⟨k,hk.trans_eq hw.symm⟩
    exact (hread i).trans ((hvalue i).symm.trans
      ((h i).symm.trans (congrArg bank (hslot i)).symm))


/-- Exactly the clipped rows owned by a specified terminal fix its gathered word;
the other cells' wire assignments can be chosen independently. -/
theorem directHooksOne_iff (t : Fin D × Bool) (boxes : List (List Factor)) (bank : ℕ → Bool)
    (hread : ∀ d e src, let r := endpointRecord N bin perm m binName siteName positive a d e src
      (d,r.side) = t → ∀ k, bank ((hooks d e src).atBit 0 k.val) = hookBit N bin perm m a s d e src k) :
    (∀ d e src, let r := endpointRecord N bin perm m binName siteName positive a d e src
      (d,r.side) = t → (directHook r.wire (hooks d e src) (terminal t)).Valid boxes bank) ↔
      ∀ k, bank ((terminal t).atBit 0 k.val) = (bundle N bin perm m positive a).gather s t k := by
  let B := bundle N bin perm m positive a
  obtain ⟨d,side⟩ := t
  constructor
  · intro h k
    obtain ⟨⟨z,i⟩,rfl⟩ := (B.order d).surjective k
    obtain ⟨e,rfl⟩ := prefixEdge_onto N bin perm m a d z
    have fromSide (src : Bool) (hs : (endpointRecord N bin perm m binName siteName positive a d e src).side = side) :
        bank ((terminal (d,side)).atBit 0 (B.order d ⟨prefixEdge N bin perm m a d e,i⟩).val) =
          B.gather s (d,side) (B.order d ⟨prefixEdge N bin perm m a d e,i⟩) := by
      have hpair := congrArg (Prod.mk d) hs
      have hi := hook_interval_iff N bin perm m binName siteName positive a s hooks terminal d e src boxes bank
        (hread d e src hpair)
      dsimp only at hi
      rw [hs] at hi
      exact hi.mp (h d e src hpair) i
    by_cases hs : positive e.val = side
    · exact fromSide true hs
    · have hn : (!(positive e.val)) = side := by cases he : positive e.val <;> cases side <;> simp_all
      exact fromSide false hn
  · intro h d' e src r he
    have hi := hook_interval_iff N bin perm m binName siteName positive a s hooks terminal d' e src boxes bank
      (hread d' e src he)
    dsimp only at hi
    change (directHook r.wire (hooks d' e src) (terminal (d',r.side))).Valid boxes bank ↔ _ at hi
    rw [he] at hi
    exact hi.mpr (fun _ => h _)

/-- In the assignment bank of each terminal's owning cell, the clipped-hook rows
recover the concatenated word at every public ordinal and both orientations. -/
theorem directHooksAt_iff
    (boxesAt : Fin D × Bool → List (List Factor)) (bankAt : Fin D × Bool → ℕ → Bool)
    (hread : ∀ d e source k, let r := endpointRecord N bin perm m binName siteName positive a d e source
      bankAt (d,r.side) ((hooks d e source).atBit 0 k.val) =
      hookBit N bin perm m a s d e source k) :
    (∀ d e source,
      let r := endpointRecord N bin perm m binName siteName positive a d e source
      (directHook r.wire (hooks d e source) (terminal (d,r.side))).Valid (boxesAt (d,r.side)) (bankAt (d,r.side))) ↔
      ∀ t k, bankAt t ((terminal t).atBit 0 k.val) = (bundle N bin perm m positive a).gather s t k := by
  let B := bundle N bin perm m positive a
  have one (d : Fin D) (e : Old N bin perm a d) (source : Bool) :=
    let r := endpointRecord N bin perm m binName siteName positive a d e source
    hook_interval_iff N bin perm m binName siteName positive a s hooks terminal d e source
      (boxesAt (d,r.side)) (bankAt (d,r.side)) (fun k => hread d e source k)
  constructor
  · intro h ⟨d,side⟩ k
    obtain ⟨⟨z,t⟩,rfl⟩ := (B.order d).surjective k
    obtain ⟨e,rfl⟩ := prefixEdge_onto N bin perm m a d z
    by_cases hs : positive e.val = side
    · exact hs ▸ (one d e true).mp (h d e true) t
    · have hn : (!(positive e.val)) = side := by
        cases he : positive e.val <;> cases side <;> simp_all
      exact hn ▸ (one d e false).mp (h d e false) t
  · intro h d e source
    exact (one d e source).mpr (fun _ => h _ _)

variable (boxes : List (List Factor)) (bank : ℕ → Bool)

/-- All the physical clipped-hook rows are valid exactly when the bank's gathered
terminal words agree with the bundle's true concatenation, at every public ordinal. -/
theorem directHooks_iff
    (hread : ∀ d e source k, bank ((hooks d e source).atBit 0 k.val) =
      hookBit N bin perm m a s d e source k) :
    (∀ d e source,
      let r := endpointRecord N bin perm m binName siteName positive a d e source
      (directHook r.wire (hooks d e source) (terminal (d,r.side))).Valid boxes bank) ↔
      ∀ t k, bank ((terminal t).atBit 0 k.val) = (bundle N bin perm m positive a).gather s t k :=
  directHooksAt_iff N bin perm m binName siteName positive a s hooks terminal (fun _ => boxes) (fun _ => bank) hread

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
