import OAI.Computability.VPVNP.LiveLinkedEvaluatorFrame
import OAI.Computability.VPVNP.LiveEvaluatorReindexSkeleton

/-!
# The linked runtime-skeleton sweep

The native table writes one nonblank tape symbol for every bit of the
zero-exponent runtime input. Its reports preserve both the linker tag and
the four runtime operands. The final linked call writes the scatter tag.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group

open BurstRAM LiveStageLink LiveEvaluatorInitialize LiveEvaluatorReindexSkeleton
open CompressorRecords
open scoped Fin.CommRing

variable {w t Z : ℕ}

/-- Every returned native report writes only inside the allocated runtime
interval. This also applies when replaying that report on another memory. -/
theorem skeletonReports_outside (hw : 2 ≤ w) (pub : Fin 4 → Word w)
    (width : (pub 0).val = Z) (total : (pub 1).val = t*Z)
    (length : (pub 3).val = 2*(t*Z)+6*Z+4) (fit : (pub 2).val+(pub 3).val ≤ 2^w)
    (s : Option (Word w)) (m : Memory w) (bits : List (List Bool)) (rs : List (Report w))
    (active : ∀ st, s = some st → st < pub 3)
    (run : runSegment (skeletonStage.instantiate w pub).program 28 s m bits = some rs) :
    ∀ r ∈ rs, ∀ mem a, a < (pub 2).val ∨ (pub 2).val+(pub 3).val ≤ a → after mem r.events a = mem a := by
  induction bits generalizing s m rs with
  | nil =>
    simp [runSegment] at run
    subst rs
    simp
  | cons b bs ih =>
    cases s with
    | none => contradiction
    | some st =>
      have ha := active st rfl
      have step := skeletonStage_call hw pub st m width total length ha b 0
      dsimp only at step
      rw [runSegment, step] at run
      by_cases hb : b = []
      · rw [ite_eq_left hb, Option.map_eq_some_iff] at run
        obtain ⟨rest, hr, rfl⟩ := run
        rw [List.forall_mem_cons]
        constructor
        · intro mem a h
          change after mem (events _ _) a = _
          have hav := Fin.lt_def.mp ha
          have addr := Fin.val_add_eq_of_add_lt (a := pub 2) (b := st) (by omega)
          rw [events_after, writeMemory, ite_eq_right (by omega)]
        · apply ih _ _ rest _ hr
          intro k hk
          change (if st+1 = pub 3 then none else some (st+1)) = some k at hk
          split at hk
          · contradiction
          · rename_i hn
            obtain rfl := Option.some.inj hk
            have hval : (st+1).val = st.val+1 := Fin.val_add_one_of_lt' (Nat.lt_of_le_of_lt (Fin.lt_def.mp ha) (pub 3).isLt)
            have hne : (st+1).val ≠ (pub 3).val := fun he => hn (Fin.ext he)
            have hav := Fin.lt_def.mp ha
            change (st+1).val < (pub 3).val
            omega
      · simp [hb] at run

variable (G : Group)

/-- Base word address of the runtime skeleton's four operands, thirteen words past the advice
frame base. -/
abbrev skeletonBase := Pieces.word G.g G.lit (.geometry (Layout.adviceFrames G.constants+13))

private theorem copied_tag {raw : List Bool} {base count : ℕ} {original out : Memory G.w}
    (h : Copied raw base count original out)
    (outside : G.addr.val < base ∨ base+count ≤ G.addr.val) (tag : Word G.w) :
    Copied raw base count (writeMemory original G.addr tag) (writeMemory out G.addr tag) := by
  constructor
  · intro j hj
    simp only [writeMemory, ite_eq_right (by omega : base+j ≠ G.addr.val)]
    exact h.symbols j hj
  · intro a ha
    by_cases he : a = G.addr.val
    · simp [writeMemory, he]
    · simpa only [writeMemory, ite_eq_right he] using h.outside a ha

/-- On the actual linked skeleton row, the canonical runtime word is written
to the supplied tape base. At handoff the scatter tag is the only change
beyond these writes, including on the reference memory for untouched cells. -/
theorem skeletonRun (pub : Fin 4 → Word G.w) (m : Memory G.w) (hw : 2 ≤ G.w)
    (width : (pub 0).val = Z) (total : (pub 1).val = t*Z)
    (length : (pub 3).val = 2*(t*Z)+6*Z+4) (fit : (pub 2).val+(pub 3).val ≤ 2^G.w)
    (data : Frame.data G.skeletonBase m = pub) (tag : G.tagged Stage.skeleton m)
    (tagOutside : G.addr.val < (pub 2).val ∨ (pub 2).val+(pub 3).val ≤ G.addr.val)
    (frameOutside : ∀ j : Fin 4, (G.skeletonBase+(j.val : Word G.w)).val < (pub 2).val ∨
      (pub 2).val+(pub 3).val ≤ (G.skeletonBase+(j.val : Word G.w)).val)
    (clock : 91 ≤ G.clock) :
    let raw := EvaluatorProgramRawInput.runtime (fun _ : Fin t => (0 : Word Z))
    ∃ out, Advice.Returning G.P G.clock raw.length 7 m (writeMemory out G.addr (tagWord G.w Stage.scatter)) ∧
      Copied raw (pub 2).val raw.length m out ∧
      Copied raw (pub 2).val raw.length (writeMemory m G.addr (tagWord G.w Stage.scatter))
        (writeMemory out G.addr (tagWord G.w Stage.scatter)) := by
  intro raw
  obtain ⟨rs, run, halt, hc, hlen, hprobes⟩ := skeletonStage_sweep hw pub m width total length fit
  have hlen' : raw.length = (pub 3).val := (EvaluatorProgramRawInput.runtime_length _).trans length.symm
  have protect := skeletonReports_outside hw pub width total length fit (some 0) m _ rs
    (fun st he => by
      obtain rfl := Option.some.inj he
      change 0 < (pub 3).val
      omega) run
  refine ⟨after m (eventLog rs), ?_, hc, copied_tag G hc (hlen'.symm ▸ tagOutside) _⟩
  apply framedReturning (T := skeletonStage) (s := Stage.skeleton) (dest := Stage.scatter)
    (fuel := 28) (b := 1) (base := G.skeletonBase) clock tag (by rfl) data (fun _ _ _ => rfl) run halt hlen hprobes
  intro r hr u
  refine ⟨protect r hr u G.addr.val tagOutside, ?_⟩
  funext j
  exact protect r hr u _ (frameOutside j)

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
