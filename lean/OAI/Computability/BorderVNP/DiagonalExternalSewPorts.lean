import OAI.Computability.BorderVNP.DiagonalExternalSewPortIndex
import OAI.Computability.BorderVNP.DiagonalExternalSewPortReads

/-! # The literal, exterior and pin slots of a physical public port

A bit of an unordered exterior cable has two ends. The team at either end
reads it in the row for the same processor, at the skipped rank of the other
team. Literal and pin slots retain their individual processor addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open TeamContraction

/-- Each processor keeps two distinct fields of width `w`, for the literal
(left summand) and the additional pin input (right summand). -/
abbrev FreePort (R r w : ℕ) := Fin (R+1) × Fin r × (Fin w ⊕ Fin w)

/-- Team, processor and bit position of the physical public input. -/
abbrev PublicPort (R r w link : ℕ) := Fin (R+1) × Fin r × Fin (2*w+R*link)

private abbrev RowField (R w link : ℕ) := Fin w ⊕ ((Fin R × Fin link) ⊕ Fin w)

private def rowFieldEquiv (R w link : ℕ) : RowField R w link ≃ Fin (2*w+R*link) :=
  ((Equiv.sumCongr (Equiv.refl _)
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by omega))

private def portFields (R r w link : ℕ) :
    FreePort R r w ⊕ (Bool × Exterior R r link) ≃ Fin (R+1) × Fin r × RowField R w link where
  toFun
    | .inl (u,j,.inl a) => (u,j,.inl a)
    | .inl (u,j,.inr a) => (u,j,.inr (.inr a))
    | .inr (s,b,j,z) =>
      let ends := endpointEquiv R (s,b)
      (ends.1,j,.inr (.inl (ends.2,z)))
  invFun
    | (u,j,.inl a) => .inl (u,j,.inl a)
    | (u,j,.inr (.inr a)) => .inl (u,j,.inr a)
    | (u,j,.inr (.inl (k,z))) =>
      let ends := (endpointEquiv R).symm (u,k)
      .inr (ends.1,ends.2,j,z)
  left_inv := by
    rintro (⟨u,j,a | a⟩ | ⟨s,b,j,z⟩)
    · rfl
    · rfl
    · dsimp only
      simp
  right_inv := by
    rintro ⟨u,j,a | (⟨k,z⟩ | a)⟩
    · rfl
    · dsimp only
      simp
    · rfl

/-- Every public port is either a free literal/pin slot or one of the two
ordered ends of a bit of the original global exterior assignment. -/
def publicPortEquiv (R r w link : ℕ) :
    FreePort R r w ⊕ (Bool × Exterior R r link) ≃ PublicPort R r w link :=
  (portFields R r w link).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (rowFieldEquiv R w link)))

variable {R r w link : ℕ}

/-- Literal bits occupy the initial contiguous segment of a processor. -/
theorem publicPortEquiv_literal (u : Fin (R+1)) (j : Fin r) (a : Fin w) :
    publicPortEquiv R r w link (.inl (u,j,.inl a)) = (u,j,⟨a.val,by have := a.isLt; omega⟩) := rfl

/-- The additional pin field starts immediately after the partner fields. -/
theorem publicPortEquiv_pin (u : Fin (R+1)) (j : Fin r) (a : Fin w) :
    publicPortEquiv R r w link (.inl (u,j,.inr a)) =
      (u,j,⟨w+R*link+a.val,by have := a.isLt; omega⟩) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Fin.ext ?_))
  · rfl
  · rfl
  change w + (R*link+a.val) = w+R*link+a.val
  omega

/-- The two physical occurrences of an exterior bit share their processor
index and their offset within the partner field. -/
theorem publicPortEquiv_exterior (s : Bool) (b : Routing.Block (R+1)) (j : Fin r) (z : Fin link) :
    publicPortEquiv R r w link (.inr (s,b,j,z)) = (fieldTeam b s,j,
      ⟨w+((fieldRank b s).val*link+z.val),by
        have h := (finProdFinEquiv (fieldRank b s,z)).isLt
        change z.val + link*(fieldRank b s).val < R*link at h
        rw [Nat.mul_comm link, Nat.add_comm z.val] at h
        omega⟩) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Fin.ext ?_))
  · rfl
  · rfl
  change w + (z.val + link*(fieldRank b s).val) = w + ((fieldRank b s).val*link+z.val)
  rw [Nat.mul_comm link, Nat.add_comm z.val]

/-- Install the public bit partition in any stored presentation of the final
physical port set, preserving both the processor order and the exterior pairing. -/
def storedPortEquiv {P : Type} (physical : PublicPort R r w link ≃ P) :
    FreePort R r w ⊕ (Bool × Exterior R r link) ≃ P :=
  (publicPortEquiv R r w link).trans physical

variable {t d inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)

/-- Read the literal or the live (possibly clamped) pin input before exterior sewing. -/
def freeBits (pin : Fin d → Bool) : FreePort R r (G.program.length+t) → Bool
  | (u,j,.inl a) => (G.program ++ List.ofFn (G.literal u j))[a.val]'(by simp)
  | (u,j,.inr a) => liveBit u pin (finProdFinEquiv (j,a)).val

/-- At every named end the prewired physical table reads the original
literal, pin or common exterior bit specified by the partition. -/
theorem publicBits_at (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (x : FreePort R r (G.program.length+t) ⊕ (Bool × Exterior R r link)) :
    let p := publicPortEquiv R r (G.program.length+t) link x
    ParseBatch.Prewire.publicBits G p.1 pin ext p.2 =
      Sum.elim (freeBits G pin) (fun e => ext e.2) x := by
  rcases x with ⟨u,j,a | a⟩ | ⟨s,b,j,z⟩
  · dsimp only
    rw [publicPortEquiv_literal]
    exact publicBits_literal G u pin ext j a
  · dsimp only
    rw [publicPortEquiv_pin]
    exact publicBits_pin G u pin ext j a
  · dsimp only
    rw [publicPortEquiv_exterior]
    calc
      _ = ext (Layout.blockOf (fieldTeam b s) ((fieldTeam b s).succAbove (fieldRank b s))
        ((fieldTeam b s).ne_succAbove (fieldRank b s)),j,z) :=
        publicBits_exterior G (fieldTeam b s) pin ext j (fieldRank b s) z
      _ = ext (b,j,z) := by simp only [succAbove_fieldRank, blockOf_fieldTeam]

/-- At every position in the whole physical row the inverse partition reads
the same bit as the processor's actual prewired input. -/
theorem publicBits_equiv (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (p : PublicPort R r (G.program.length+t) link) :
    ParseBatch.Prewire.publicBits G p.1 pin ext p.2 =
      Sum.elim (freeBits G pin) (fun e => ext e.2)
        ((publicPortEquiv R r (G.program.length+t) link).symm p) := by
  simpa only [Equiv.apply_symm_apply] using
    publicBits_at G pin ext ((publicPortEquiv R r (G.program.length+t) link).symm p)

/-- Reading through any saved numbering of the physical input ports preserves
the free fields and both occurrences of every globally shared exterior bit. -/
theorem publicBits_stored {P : Type} (physical : PublicPort R r (G.program.length+t) link ≃ P)
    (pin : Fin d → Bool) (ext : Exterior R r link → Bool) (p : P) :
    ParseBatch.Prewire.publicBits G (physical.symm p).1 pin ext (physical.symm p).2 =
      Sum.elim (freeBits G pin) (fun e => ext e.2) ((storedPortEquiv physical).symm p) :=
  publicBits_equiv G pin ext (physical.symm p)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
