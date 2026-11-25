import OAI.Computability.BorderVNP.DiagonalExternalSewIntervals

/-! # Public exterior cable records at an initial site

Physical fields are named by team, processor, and skipped partner rank.
A block of at most a link width meets at most two such fields. For each
of those fields, the corresponding offsets at the partner meet at most
two of its blocks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Finset
open scoped Classical

variable {F T : Type} {r R : ℕ} (ends : Bool × F ↪ T × (Fin r × Fin R))
variable (literal stride link g : ℕ)

/-- Absolute start of the exterior field, in processor and partner-rank order. -/
def endStart (f : F) (s : Bool) : ℕ :=
  (ends (s,f)).2.1.val * stride + literal + (ends (s,f)).2.2.val * link

/-- One cable descriptor at the indicated end, including the team name of its block. -/
def endBlock (c : Pieces (endStart ends literal stride link) g link) (s : Bool) : T × ℕ :=
  ((ends (s,c.1)).1, if s then c.2.val.2 else c.2.val.1)

/-- Lexicographic processor and partner-rank ordinal. -/
def fieldOrdinal (v : Fin r × Fin R) : ℕ := v.1.val*R + v.2.val

private theorem ordinal_inj : Function.Injective (fieldOrdinal (r := r) (R := R)) := by
  intro v w h
  apply finProdFinEquiv.injective
  apply Fin.ext
  simpa [fieldOrdinal,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm] using h

private theorem proc_le {v w : Fin r × Fin R} (h : fieldOrdinal v ≤ fieldOrdinal w) : v.1.val ≤ w.1.val := by
  by_contra! hz
  have hx := Nat.mul_le_mul_right R (Nat.succ_le_of_lt hz)
  rw [Nat.succ_mul] at hx
  have := w.2.isLt
  dsimp [fieldOrdinal] at h
  omega

private theorem gap (fits : R*link ≤ stride) (a b : Bool × F) (k : ℕ)
    (h : fieldOrdinal (ends a).2 + k ≤ fieldOrdinal (ends b).2) :
    endStart ends literal stride link a.2 a.1 + k*link ≤ endStart ends literal stride link b.2 b.1 := by
  have hz (x : Bool × F) : endStart ends literal stride link x.2 x.1 =
      fieldOrdinal (ends x).2 * link + (ends x).2.1.val*(stride-R*link) + literal := by
    rcases x with ⟨s,f⟩
    unfold endStart fieldOrdinal
    rw [show stride = (stride-R*link)+R*link from (Nat.sub_add_cancel fits).symm] at ⊢
    rw [Nat.add_sub_cancel]
    ring
  have hl := Nat.mul_le_mul_right link h
  have hp := Nat.mul_le_mul_right (stride-R*link) (proc_le (show fieldOrdinal (ends a).2 ≤ fieldOrdinal (ends b).2 by omega))
  rw [Nat.add_mul] at hl
  rw [hz a,hz b]
  omega

private theorem same_block_lt {x y b : ℕ} (hb : 0 < b) (he : x/b = y/b) : x < y+b := by
  have hx := Nat.div_add_mod' x b
  have hy := Nat.div_add_mod' y b
  have hm := Nat.mod_lt x hb
  rw [he] at hx
  omega

private def sample (c : Pieces (endStart ends literal stride link) g link) : Fin link :=
  pieceOffset _ _ c ⟨0,pieceWidth_pos _ _ c⟩

private theorem sample_block (c : Pieces (endStart ends literal stride link) g link) (s : Bool) :
    (endStart ends literal stride link c.1 s + (sample ends literal stride link g c).val)/g =
      (endBlock ends literal stride link g c s).2 := by
  have h := pieceOffset_blocks _ _ c ⟨0,pieceWidth_pos _ _ c⟩
  cases s
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

variable {ends literal stride link g}

/-- One fixed-width block meets at most two successive fields in the actual
processor-major order, including the gap for literal and additional pin fields. -/
theorem field_ordinal_le_succ {a b : Bool × F} {i j : Fin link}
    (fits : R*link ≤ stride) (hg : 0 < g) (small : g ≤ link)
    (he : (endStart ends literal stride link a.2 a.1 + i.val)/g =
      (endStart ends literal stride link b.2 b.1 + j.val)/g) :
    fieldOrdinal (ends a).2 ≤ fieldOrdinal (ends b).2+1 := by
  by_contra! h
  have hh := gap ends literal stride link fits b a 2 (by omega)
  have hc := same_block_lt hg he
  have hj := j.isLt
  omega

/-- The public descriptors for positive exterior cables at one site of one
team number at most four. Empty intervals receive no descriptors. -/
theorem ends_per_block [Fintype F] [DecidableEq T] (fits : R*link ≤ stride) (hg : 0 < g) (small : g ≤ link) (u : T) (s : ℕ) :
    (univ.filter fun x : Bool × Pieces (endStart ends literal stride link) g link =>
      endBlock ends literal stride link g x.2 x.1 = (u,s)).card ≤ 4 := by
  let L := endStart ends literal stride link
  let A := {x : Bool × Pieces L g link // endBlock ends literal stride link g x.2 x.1 = (u,s)}
  let code (x : A) : Fin 2 × Fin 2 :=
    (⟨fieldOrdinal (ends (x.val.1,x.val.2.1)).2 % 2, Nat.mod_lt _ (by decide)⟩,
     ⟨(endBlock ends literal stride link g x.val.2 (!x.val.1)).2 % 2, Nat.mod_lt _ (by decide)⟩)
  have inj : Function.Injective code := by
    rintro ⟨⟨a,c⟩,ha⟩ ⟨⟨b,d⟩,hb⟩ he
    have hx := congrArg (fun y : Fin 2 × Fin 2 => y.1.val) he
    have hy := congrArg (fun y : Fin 2 × Fin 2 => y.2.val) he
    dsimp only [code] at hx hy
    let i := sample ends literal stride link g c
    let j := sample ends literal stride link g d
    have site : (L c.1 a + i.val)/g = (L d.1 b + j.val)/g :=
      (sample_block _ _ _ _ _ c a).trans ((congrArg Prod.snd (ha.trans hb.symm)).trans
        (sample_block _ _ _ _ _ d b).symm)
    have h₁ := field_ordinal_le_succ (a := (a,c.1)) (b := (b,d.1)) fits hg small site
    have h₂ := field_ordinal_le_succ (a := (b,d.1)) (b := (a,c.1)) fits hg small site.symm
    have hv : fieldOrdinal (ends (a,c.1)).2 = fieldOrdinal (ends (b,d.1)).2 := by omega
    have hteam := congrArg Prod.fst (ha.trans hb.symm)
    change (ends (a,c.1)).1 = (ends (b,d.1)).1 at hteam
    have hfield := ends.injective (Prod.ext hteam (ordinal_inj hv))
    rcases c with ⟨f,c,hc⟩
    rcases d with ⟨z,d,hd⟩
    change (a,f) = (b,z) at hfield
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hfield
    have ij := same_block_lt hg site
    have ji := same_block_lt hg site.symm
    change L f a + i.val < L f a + j.val + g at ij
    change L f a + j.val < L f a + i.val + g at ji
    have nr (v w : Fin link) (h : v.val < w.val+g) :
        (L f (!a)+v.val)/g ≤ (L f (!a)+w.val)/g + 1 := by
      rw [← Nat.add_div_right _ hg]
      exact Nat.div_le_div_right (by omega)
    have rem₁ := nr i j (by omega)
    have rem₂ := nr j i (by omega)
    have hi := sample_block ends literal stride link g (⟨f,⟨c,hc⟩⟩ : Pieces L g link) (!a)
    have hj := sample_block ends literal stride link g (⟨f,⟨d,hd⟩⟩ : Pieces L g link) (!a)
    change (L f (!a)+i.val)/g = _ at hi
    change (L f (!a)+j.val)/g = _ at hj
    rw [hi,hj] at rem₁ rem₂
    have hremote : (endBlock ends literal stride link g (⟨f,⟨c,hc⟩⟩ : Pieces L g link) (!a)).2 =
      (endBlock ends literal stride link g (⟨f,⟨d,hd⟩⟩ : Pieces L g link) (!a)).2 := by omega
    have hlocal := congrArg Prod.snd (ha.trans hb.symm)
    have hcd : c = d := by
      cases a
      · exact Prod.ext hlocal hremote
      · exact Prod.ext hremote hlocal
    subst d
    rfl
  simpa [A,Fintype.card_subtype] using Fintype.card_le_of_injective code inj

private theorem ordinal_le_of_raw {a b : Bool × F} {i j : Fin link}
    (fits : R*link ≤ stride)
    (he : endStart ends literal stride link a.2 a.1 + i.val =
      endStart ends literal stride link b.2 b.1 + j.val) :
    fieldOrdinal (ends a).2 ≤ fieldOrdinal (ends b).2 := by
  by_contra! h
  have hz := gap ends literal stride link fits b a 1 (by omega)
  have := j.isLt
  omega

/-- All bits in the incident exterior intervals at one team and block together
fit in its actual `g` raw slots. Distinct intervals cannot claim the same bit. -/
theorem width_per_block [Fintype F] [DecidableEq T] (fits : R*link ≤ stride) (hg : 0 < g) (u : T) (s : ℕ) :
    (∑ x : {x : Bool × Pieces (endStart ends literal stride link) g link //
      endBlock ends literal stride link g x.2 x.1 = (u,s)}, pieceWidth _ _ x.val.2) ≤ g := by
  let L := endStart ends literal stride link
  let A := {x : Bool × Pieces L g link // endBlock ends literal stride link g x.2 x.1 = (u,s)}
  let Bits := Σ x : A, Fin (pieceWidth L g x.val.2)
  let pos (x : Bits) := L x.1.val.2.1 x.1.val.1 + (pieceOffset L g x.1.val.2 x.2).val
  let loc (x : Bits) : Fin g := ⟨pos x % g,Nat.mod_lt _ hg⟩
  have addr (x : Bits) : pos x / g = s := by
    have h := pieceOffset_blocks L g x.1.val.2 x.2
    have he := congrArg Prod.snd x.1.property
    rcases x with ⟨⟨⟨a,c⟩,ha⟩,i⟩
    cases a
    · exact (congrArg Prod.fst h).trans he
    · exact (congrArg Prod.snd h).trans he
  have hi : Function.Injective loc := by
    intro x y h
    have hx := Nat.div_add_mod' (pos x) g
    have hy := Nat.div_add_mod' (pos y) g
    have hm := congrArg Fin.val h
    change pos x % g = pos y % g at hm
    rw [addr x,hm] at hx
    rw [addr y] at hy
    have he := hx.symm.trans hy
    rcases x with ⟨⟨⟨a,⟨f,⟨c,hc⟩⟩⟩,ha⟩,i⟩
    rcases y with ⟨⟨⟨b,⟨z,⟨d,hd⟩⟩⟩,hb⟩,j⟩
    let ci : Pieces L g link := ⟨f,⟨c,hc⟩⟩
    let cj : Pieces L g link := ⟨z,⟨d,hd⟩⟩
    change L f a + (pieceOffset L g ci i).val = L z b + (pieceOffset L g cj j).val at he
    have hv := Nat.le_antisymm (ordinal_le_of_raw (a := (a,f)) (b := (b,z)) fits he)
      (ordinal_le_of_raw (a := (b,z)) (b := (a,f)) fits he.symm)
    have ht := congrArg Prod.fst (ha.trans hb.symm)
    change (ends (a,f)).1 = (ends (b,z)).1 at ht
    have hfield := ends.injective (Prod.ext ht (ordinal_inj hv))
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hfield
    have hoff := Fin.ext (Nat.add_left_cancel he)
    have hcd := (pieceOffset_blocks L g ci i).symm.trans
      ((congrArg (blockPair L g f) hoff).trans (pieceOffset_blocks L g cj j))
    change c = d at hcd
    subst d
    have hij := (pieceOffset_strictMono L g ci).injective hoff
    subst j
    rfl
  simpa [Bits,A,Fintype.card_sigma] using Fintype.card_le_of_injective loc hi

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
