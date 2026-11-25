import OAI.Computability.BorderVNP.PackedSewnRecordEmitter

/-! # The exterior sewing records at each physical site

A site-keyed scan of the immutable output visits exactly the enabled opcode of
each interval. Appending this section to the predecessor tape produces the
full directory of the retained, sewn private site.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField ParseBatchSort VPVNP.VerifierNetwork CellSparse
open scoped Classical

variable {n w : ℕ} {V : Type*}

/-- Stable interval list at one sparse physical site number. -/
def runsAt (xs : List Fragment.Parsed) (key : ℕ) :=
  xs.filterMap fun p => if p.site=key then some p.run else none

private def decode {n w : ℕ} (x : Input n w → Bool) (i : Fin n) :=
  if Fragment.active (x ∘ Sum.inl) i then some (Fragment.parse (x ∘ Sum.inl) i) else none

private theorem mem_run (x : Input n w → Bool) (key : ℕ) (i : Fin n)
    (live : Fragment.active (x ∘ Sum.inl) i = true) (same : (Fragment.parse (x ∘ Sum.inl) i).site = key) :
    (Fragment.parse (x ∘ Sum.inl) i).run ∈ runsAt (Fragment.list (x ∘ Sum.inl)) key := by
  refine List.mem_filterMap.mpr ⟨Fragment.parse (x ∘ Sum.inl) i,List.mem_filterMap.mpr ⟨i,List.mem_finRange _,?_⟩,?_⟩
  · simp [live]
  · simp [same]

private theorem atKey (x : Input n w → Bool) (key : ℕ) (s : Site)
    (correct : ∀ i, Fragment.active (x ∘ Sum.inl) i = true → (Fragment.parse (x ∘ Sum.inl) i).site=key →
      (schema n w).read ((frame n w).eval x) (i,x (.inl (i,.inl true))) = marked ((Fragment.parse (x ∘ Sum.inl) i).run.record s)) :
    (schema n w).atSite ((frame n w).eval x) key =
      (runsAt (Fragment.list (x ∘ Sum.inl)) key).map (fun p => marked (p.record s)) := by
  let get (r : Row n) := if (frame n w).eval x (.inl (r,.inl ())) ∧ owner ((frame n w).eval x) r = key
    then some ((schema n w).read ((frame n w).eval x) r) else none
  have loop (xs : List (Fin n)) : (xs.flatMap (fun i => [(i,false),(i,true)])).filterMap get =
      (runsAt (xs.filterMap (decode x)) key).map (fun p => marked (p.record s)) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      rw [List.flatMap_cons,List.filterMap_append,ih]
      by_cases live : Fragment.active (x ∘ Sum.inl) i = true
      · by_cases same : (Fragment.parse (x ∘ Sum.inl) i).site = key
        · have word := correct i live same
          cases h : x (.inl (i,.inl true)) <;>
            simp [get,flag,owner_eq,live,same,h,decode,runsAt] at word ⊢ <;> exact word
        · simp [get,flag,owner_eq,live,same,decode,runsAt]
      · simp [get,flag,owner_eq,live,decode,runsAt]
  exact loop (List.finRange n)

/-- On a genuine ordered interval frame, all scalar words, row boundaries and attained
site owners of the physical section agree with the actual maximal reconstruction runs. -/
theorem frame_section (x : Input n w → Bool) (id : V ↪ ℕ) (prior : V → Site) (size : V → ℕ)
    (source : ∀ v, Fin (prior v).incoming → Option (Fin (size v)))
    (owners : ∀ i, Fragment.active (x ∘ Sum.inl) i = true → ∃ v, (Fragment.parse (x ∘ Sum.inl) i).site = id v)
    (rows : ∀ v, runsAt (Fragment.list (x ∘ Sum.inl)) (id v) = intervals (source v))
    (bases : ∀ i v, (Fragment.parse (x ∘ Sum.inl) i).site = id v → ∀ b,
      value (fun j => x (.inr (i,b,j))) = if b then (prior v).size else (prior v).work)
    (fit : ∀ v, (prior v).size + size v < 2^w) (one : 1 < 2^w) :
    (schema n w).Section ((frame n w).eval x) id (fun v => (intervals (source v)).map (Interval.record (prior v))) := by
  constructor
  · rintro ⟨i,b⟩ _ en
    rw [owner_eq]
    exact owners i ((flag x i b).mp en).1
  · intro v
    have correct (i : Fin n) (live : Fragment.active (x ∘ Sum.inl) i = true) (same : (Fragment.parse (x ∘ Sum.inl) i).site = id v) :
        (schema n w).read ((frame n w).eval x) (i,x (.inl (i,.inl true))) =
          marked ((Fragment.parse (x ∘ Sum.inl) i).run.record (prior v)) := by
      let p := (Fragment.parse (x ∘ Sum.inl) i).run
      have hp : p ∈ intervals (source v) := rows v ▸ mem_run x (id v) i live same
      have bounds := intervals_cover (source v)
      have h₁ := bounds.oldFit p hp
      have h₂ := fit v
      apply read x i (prior v) one (bases i v same false) (bases i v same true)
      · change (prior v).work + p.oldStart < 2^w
        change (prior v).work+(prior v).incoming+size v < 2^w at h₂
        omega
      · intro j hj
        have h₃ := bounds.newFit p hp j (by simpa only [Option.mem_def] using hj)
        omega
    rw [atKey x (id v) (prior v) correct,rows,List.map_map]
    rfl

variable {R B σ : Type*} [Fintype R] [Fintype B] [Fintype σ]

/-- Appending the actual site-local interval payload gives exactly the new private
site history, including both older observations and every sewn stage descriptor. -/
theorem append_image (S : Schema R B) (hist : Frame σ (Pins R B w)) (src : Frame σ (Input n w))
    (x : σ → Bool) (id : V ↪ ℕ) (prior : V → Site) (size : V → ℕ)
    (source : ∀ v, Fin (prior v).incoming → Option (Fin (size v)))
    (old : S.Image (hist.eval x) id prior)
    (owners : ∀ i, Fragment.active (src.eval x ∘ Sum.inl) i = true → ∃ v, (Fragment.parse (src.eval x ∘ Sum.inl) i).site=id v)
    (rows : ∀ v, runsAt (Fragment.list (src.eval x ∘ Sum.inl)) (id v) = intervals (source v))
    (bases : ∀ i v, (Fragment.parse (src.eval x ∘ Sum.inl) i).site=id v → ∀ b,
      value (fun j => src.eval x (.inr (i,b,j))) = if b then (prior v).size else (prior v).work)
    (fit : ∀ v, (prior v).size + size v < 2^w) (one : 1 < 2^w) :
    (S.append (schema n w)).Image ((appendFrame hist ((frame n w).subst src)).eval x) id
      (fun v => stage (prior v) (size v) (intervals (source v))) := by
  have h := frame_section (src.eval x) id prior size source owners rows bases fit one
  have ev : ((frame n w).subst src).eval x = (frame n w).eval (src.eval x) := funext fun z => Frame.subst_eval _ _ _ _
  rw [←ev] at h
  have full := appendFrame_section S (schema n w) hist ((frame n w).subst src) x id _ _ (old.toSection S) h
  exact full.image _ _ (fun v => (stage_rows ..).symm)

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
