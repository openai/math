import OAI.Computability.BorderVNP.ShortenStaticRowCircuit
import OAI.Computability.BorderVNP.ShortenStaticTerminalCircuit

/-!
# Full old-cable row circuit after bin-directory lookup

The directory provides the seed number, old endpoint names, split width and
padding-site name. Both terminal-site addresses are computed by fixed-template
arithmetic before the row enable and orientation mux. The source gates are
charged only once across the entire table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticRows.Serializer

open Crossing SeedIntervals StaticTerminalCircuit VPVNP.VerifierNetwork ParseBatchSort

/-- Directory words needed after the sorted split widths and inverse seed IDs are available. -/
inductive DirectoryWord | oldSrc | oldDst | span | seed | pad deriving DecidableEq
instance : Fintype DirectoryWord := ⟨{.oldSrc,.oldDst,.span,.seed,.pad}, by intro f; cases f <;> simp⟩

/-- Input block before computing the terminal-site identifiers. -/
abbrev DirectoryInput (w : ℕ) := Flag ⊕ (DirectoryWord × Fin w)

/-- All candidate rows in the three old-band rectangles, independent of the histogram. -/
abbrev Row (oldEdges D : ℕ) := Fin oldEdges × Band D × Fin 3

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The six row words after computing the two signed terminal names from the inverse seed ID. -/
noncomputable def expandWords (oldSites : ℕ) (axis : Fin D) (raw : DirectoryWord → ℕ) : Word → ℕ
  | .oldSrc => raw .oldSrc | .oldDst => raw .oldDst | .span => raw .span | .pad => raw .pad
  | .terminalPos => address e oldSites axis true (raw .seed)
  | .terminalNeg => address e oldSites axis false (raw .seed)

private def expandPin {R : Type*} {w : ℕ} :
    R × Input w → (R × DirectoryInput w) ⊕ (R × Bool × Fin w)
  | (r,.inl f) => .inl (r,.inl f)
  | (r,.inr (.oldSrc,j)) => .inl (r,.inr (.oldSrc,j))
  | (r,.inr (.oldDst,j)) => .inl (r,.inr (.oldDst,j))
  | (r,.inr (.span,j)) => .inl (r,.inr (.span,j))
  | (r,.inr (.pad,j)) => .inl (r,.inr (.pad,j))
  | (r,.inr (.terminalPos,j)) => .inr (r,true,j)
  | (r,.inr (.terminalNeg,j)) => .inr (r,false,j)

/-- Boolean circuit for every reserved hook and retained cable row. The cost is linear in the
number of old descriptors at fixed dimension and paid identity, and quadratic in word bits. -/
theorem exists_oldBandFrame {σ : Type*} [Fintype σ] (oldSites oldEdges w : ℕ)
    (source : Frame σ (Row oldEdges D × DirectoryInput w)) :
    ∃ f : Frame σ (Row oldEdges D × Output w),
      f.size ≤ source.size + 1 + oldEdges * (2*D+1) * 3 *
        (2 * nodeBudget e * (100*(w+1)^2) + 64*(1+3*w)) ∧
      ∀ (x : σ → Bool) (r : Row oldEdges D),
        let flags := fun t => source.eval x (r,.inl t)
        let raw := fun t => value (fun j => source.eval x (r,.inr (t,j)))
        (enabled r.2.2 (isPrefix r.2.1) flags = true → r.2.2.val < 2 →
          ∀ side, address e oldSites (direction r.2.1) side (raw .seed) < 2^w) →
        f.eval x (r,.inl ()) = enabled r.2.2 (isPrefix r.2.1) flags ∧
        ∀ c, value (fun j => f.eval x (r,.inr (c,j))) =
          columnValue r.2.2 (isPrefix r.2.1) flags (expandWords e oldSites (direction r.2.1) raw) c := by
  let R := Row oldEdges D
  let seeds : Frame (R × DirectoryInput w) (R × Fin w) := Frame.initial fun z => (z.1,.inr (.seed,z.2))
  obtain ⟨term,hterm,termValue⟩ := exists_terminalFrame e oldSites (fun r : R => direction r.2.1) w seeds
  let complete := term.withInput.select expandPin
  let kind := fun r : R => r.2.2
  let matched := fun r : R => isPrefix r.2.1
  let localRows := frame kind matched complete
  refine ⟨localRows.subst source,?_,?_⟩
  · have hc : Fintype.card R = oldEdges*(2*D+1)*3 := by
      simp [R,Row,Band,Nat.mul_assoc,Nat.mul_comm]
    have hcpl : complete.size = term.size := by simp [complete]
    have hs := frame_size kind matched complete
    have hseed : seeds.size = 0 := Frame.initial_size _
    rw [hseed,zero_add] at hterm
    rw [hcpl] at hs
    rw [Frame.subst_size]
    change source.size + (frame kind matched complete).size ≤ _
    rw [hc] at hs hterm
    calc
      _ ≤ source.size + ((1 + oldEdges*(2*D+1)*3*(2*nodeBudget e*(100*(w+1)^2))) +
        oldEdges*(2*D+1)*3*(64*(1+3*w))) := Nat.add_le_add_left (hs.trans (Nat.add_le_add_right hterm _)) _
      _ = _ := by ring
  · intro x r flags raw hfit
    let y := source.eval x
    let z := fun i => complete.eval y (r,i)
    have hf : (z ∘ Sum.inl) = flags := by
      funext t
      simp [z,complete,expandPin,Frame.select_eval,Frame.withInput_eval_inl,flags,y]
    let actual := fun t : Word => value (fun j => z (.inr (t,j)))
    let ideal := expandWords e oldSites (direction r.2.1) raw
    have hcopy (t : Word) (hpos : t ≠ .terminalPos) (hneg : t ≠ .terminalNeg) : actual t = ideal t := by
      cases t <;> first | contradiction | (simp only [actual,ideal,z,complete,expandPin,expandWords,
        Frame.select_eval,Frame.withInput_eval_inl]; rfl)
    have he := frame_eval kind matched complete y r
    change localRows.eval y (r,.inl ()) = enabled (kind r) (matched r) (z ∘ Sum.inl) ∧
      ∀ c, value (fun j => localRows.eval y (r,.inr (c,j))) =
        columnValue (kind r) (matched r) (z ∘ Sum.inl) actual c at he
    rw [hf] at he
    simp only [Frame.subst_eval]
    refine ⟨he.1,fun c => (he.2 c).trans ?_⟩
    change columnValue r.2.2 (isPrefix r.2.1) flags actual c = columnValue r.2.2 (isPrefix r.2.1) flags ideal c
    cases hp : enabled r.2.2 (isPrefix r.2.1) flags
    · cases c <;> simp [columnValue,hp,hcopy .pad (by decide) (by decide)]
    · by_cases hk : r.2.2.val = 2
      · cases c <;> simp [columnValue,hp,activeWord,hk,hcopy .span (by decide) (by decide),
          hcopy .oldSrc (by decide) (by decide),hcopy .oldDst (by decide) (by decide)]
      · have haddr (side : Bool) : value (fun j => term.eval y (r,side,j)) =
            address e oldSites (direction r.2.1) side (raw .seed) := by
          have hs : value (fun j => seeds.eval y (r,j)) = raw .seed := by simp [seeds,raw,y]
          exact (termValue y r side (by rw [hs]; exact hfit hp (by omega) side)).trans
            (congrArg (address e oldSites (direction r.2.1) side) hs)
        have hall : actual = ideal := by
          funext t
          cases t <;> first | exact hcopy _ (by decide) (by decide) |
            (simp only [actual,ideal,z,complete,expandPin,expandWords,Frame.select_eval,Frame.withInput_eval_inr];
             exact haddr _)
        rw [hall]

end Shortening.StaticRows.Serializer

end BorderVNP
end Computability
end OAI
