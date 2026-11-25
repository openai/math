import OAI.Hierarchy.TaggedAlignmentData
import OAI.Hierarchy.TaggedAlignmentPrefix
import OAI.Hierarchy.TaggedRealTransport

namespace OAI
/-! # The destinations of real rows and dummy rows in a sorted local block -/

namespace Hierarchy.Tagged.SortedBlock
open ThreeFlat Routing SortNetwork
open Radix.PassShape AlignRows
open scoped Classical
noncomputable section

variable {j t d w b : ℕ} (digit : Fin d → Fin w) (real : Fin w) (x : Records (j+t) w)

structure AlignedInput : Prop where
  front : AlignBlock.initial real x (prefixSize real x)
  ascending : Ordered real digit x
  fits : prefixSize real x + 2^d * 2^j ≤ 2^(j+t)

def blockKeys : Fin (prefixSize real x) → Row d := fun i =>
  AlignBlock.key digit x (Align.split (prefixSize_le real x) (.inl i))

private theorem mono_by_next {n : ℕ} {α : Type*} [Preorder α] (f : Fin n → α)
    (steps : ∀ i l, i.val+1 = l.val → f i ≤ f l) : Monotone f := by
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n => exact Fin.monotone_iff_le_succ.mpr (fun i => steps _ _ rfl)

theorem blockKeys_mono (ok : AlignedInput digit real x) : Monotone (blockKeys digit real x) := by
  apply mono_by_next
  intro i l step
  let u : Row (j+t) := Align.split (prefixSize_le real x) (.inl i)
  let v : Row (j+t) := Align.split (prefixSize_le real x) (.inl l)
  let e : Edge (j+t) := ⟨u,step.trans_lt v.isLt⟩
  have nxt : next e = v := Fin.ext step
  have ord := ok.ascending e ((ok.front u).mpr i.isLt) (nxt.symm ▸ (ok.front v).mpr l.isLt)
  change (digitValue digit x u).toNat ≤ (digitValue digit x v).toNat
  rw [nxt] at ord
  exact ord

/-- The canonical completion retains the real rows' source order; the
unoccupied destinations are filled by the unique sorted dummy permutation. -/
def placement (ok : AlignedInput digit real x) :=
  Align.embed (Nat.two_pow_pos j) (blockKeys digit real x) (blockKeys_mono digit real x ok) ok.fits

def perm (ok : AlignedInput digit real x) : Row (j+t) ≃ Row (j+t) :=
  (Align.split (prefixSize_le real x)).symm.trans (Align.complete (placement digit real x ok))

def align (x : Records (j+t) w) : Records (j+t) w :=
  if ok : AlignedInput digit real x then x ∘ (perm digit real x ok).symm else x

@[simp] theorem destination (ok : AlignedInput digit real x) (i : Fin (prefixSize real x)) :
    perm digit real x ok (Align.split (prefixSize_le real x) (.inl i)) = placement digit real x ok i := by
  simp [perm]

/-- A real row has a unique real prefix source index. -/
def liveEquiv (ok : AlignedInput digit real x) : Radix.Live (fun z : Fin w → Bool => z real = true) x ≃ Fin (prefixSize real x) where
  toFun i := ⟨i.val.val,(ok.front _).mp i.property⟩
  invFun i := ⟨Align.split (prefixSize_le real x) (.inl i), (ok.front _).mpr i.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem addr_strict {r m p : ℕ} (hp : 0 < p) (key : Fin r → Fin m) : StrictMono (Align.realAddress p key) := by
  cases r with
  | zero => exact fun i => Fin.elim0 i
  | succ r => exact Align.dest_strict hp key

private theorem addr_homogeneous {r m p : ℕ} (hp : 0 < p) (key : Fin r → Fin m) (mono : Monotone key) (i l : Fin r)
    (eq : Align.realAddress p key i / p = Align.realAddress p key l / p) : key i = key l := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact Align.homogeneous hp key mono i l eq

private theorem addr_prefix {r m p : ℕ} (hp : 0 < p) (key : Fin r → Fin m) (i : Fin r) :
    ∃ l, Align.realAddress p key l = Align.realAddress p key i / p * p ∧ key l = key i := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact Align.pack_prefix hp key i _ le_rfl (Nat.div_mul_le_self ..)

/-- The real port transport is strictly increasing before the wide sort. -/
theorem align_order (ok : AlignedInput digit real x) {u v : Row (j+t)} (ur : x u real = true)
    (vr : x v real = true) (lt : u < v) : perm digit real x ok u < perm digit real x ok v := by
  let e := liveEquiv digit real x ok
  let i := e ⟨u,ur⟩
  let l := e ⟨v,vr⟩
  have change_u : u = Align.split (prefixSize_le real x) (.inl i) := rfl
  have change_v : v = Align.split (prefixSize_le real x) (.inl l) := rfl
  rw [change_u,change_v,destination,destination]
  simpa only [Fin.lt_def,placement,Align.embed_val] using addr_strict (Nat.two_pow_pos j) (blockKeys digit real x) (show i < l from lt)

/-- Every nonempty pack starts with a real lane whose digit equals every
real digit observed anywhere later in that pack. -/
theorem align_first (ok : AlignedInput digit real x) (i : Row (j+t))
    (real_i : align digit real x i real = true) :
    ∃ v : Row (j+t), v.val = i.val/2^j*2^j ∧ align digit real x v real = true ∧
      readKey digit (align digit real x v) = readKey digit (align digit real x i) := by
  let p := perm digit real x ok
  let q : Row (j+t) := p.symm i
  have real_q : x q real = true := by simpa [align,ok,p,q] using real_i
  let src := liveEquiv digit real x ok ⟨q,real_q⟩
  have ident (l : Fin (prefixSize real x)) :
      Align.realAddress (2^j) (blockKeys digit real x) l = (p (Align.split (prefixSize_le real x) (.inl l))).val := by
    simp [p,destination,placement]
  have eq : p (Align.split (prefixSize_le real x) (.inl src)) = i := p.apply_symm_apply i
  obtain ⟨first,where_,key⟩ := addr_prefix (Nat.two_pow_pos j) (blockKeys digit real x) src
  let atFirst := Align.split (prefixSize_le real x) (.inl first)
  refine ⟨p atFirst,by simpa only [ident,eq] using where_, ?_, ?_⟩
  · rw [align,dite_eq_left ok]
    change x (p.symm (p atFirst)) real = true
    rw [p.symm_apply_apply]
    exact (ok.front atFirst).mpr first.isLt
  · have k := congrArg Fin.val key
    change readKey digit (x atFirst) = readKey digit (x q) at k
    simpa [align,ok,p,q] using k

end
end Hierarchy.Tagged.SortedBlock

end OAI
