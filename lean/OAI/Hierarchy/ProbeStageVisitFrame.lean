import OAI.Hierarchy.ProbeStageRecordContract
import OAI.Hierarchy.ProbeStagePublish

namespace OAI
/-! # Immutable operands and persistent outputs of an ordinal visit -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

/-- Each ordinal writes either its three rank cells, its private scratch
cells, or mutable masks and counters. Every such word belongs to this
level, before the permanent geometry output area. -/
theorem mayWrite_region {h d j x : ℕ} {r : Fin (2^h)} (w : MayWrite h d j r x) :
    phase h d copies j≤x ∧ x<output h d copies j ∧
      (x<bankBase h d copies j 3 ∨ bankBase h d copies j 14≤x) := by
  have gap : bankBase h d copies j 3≤output h d copies j := by
    have before := separate h d copies j 3 (stride d copies-9) (by unfold stride;omega)
    exact (Nat.le_add_right _ _).trans before
  rcases w with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,o,rfl⟩
  · have lim := r.isLt.trans_le (height_extent h d)
    have before := separate h d copies j k.val 3 k.isLt
    have earlier : rankAddr h d j k r<bankBase h d copies j 3 :=
      (Nat.add_lt_add_left lim _).trans_le before
    exact ⟨by unfold rankAddr bankBase;omega,earlier.trans_le gap,Or.inl earlier⟩
  · have upper := (scratch_separate h d j k 0).trans_le
      ((Nat.le_add_right _ _).trans (region_end h d j 0))
    exact ⟨by unfold scratch bankBase;omega,upper,Or.inr (Nat.le_add_right _ _)⟩
  · have upper := (Nat.add_lt_add_left o.isLt _).trans_le
      (region_end h d j (⟨12+k.val,by omega⟩ : Fin 16))
    exact ⟨by unfold region bankBase;omega,upper,Or.inr (by unfold region bankBase;omega)⟩

theorem mayWrite_not_rom {h d j : ℕ} (i : Fin (2^h)) (k : Fin 12) (a : Fin (regionSize h d)) :
    ¬MayWrite h d j i (region h d j ⟨k.val,by omega⟩+a.val) := by
  let tag : Fin 16 := ⟨k.val,by omega⟩
  let c : Cell h d := .area tag a
  rintro (⟨b,eq⟩|⟨b,eq⟩|⟨b,u,eq⟩)
  · have bad : c=Cell.rank b i := cell_injective h d j eq
    dsimp only [c] at bad
    cases bad
  · have bad : c=Cell.temp b := cell_injective h d j eq
    dsimp only [c] at bad
    cases bad
  · have bad : c=Cell.area ⟨12+b.val,by omega⟩ u := cell_injective h d j eq
    have tags : tag=(⟨12+b.val,by omega⟩:Fin 16) := (Cell.area.inj bad).1
    have := congrArg Fin.val tags
    change k.val=12+b.val at this
    omega

theorem mayWrite_not_earlier_rank {h d j : ℕ} {i r : Fin (2^h)} (different : r≠i) (k : Fin 3) :
    ¬MayWrite h d j i (rankAddr h d j k r) := by
  rintro (⟨b,eq⟩|⟨b,eq⟩|⟨b,u,eq⟩)
  · have e : (Cell.rank k r : Cell h d)=Cell.rank b i := cell_injective h d j eq
    exact different (Cell.rank.inj e).2
  · have e : (Cell.rank k r : Cell h d)=Cell.temp b := cell_injective h d j eq
    cases e
  · have e : (Cell.rank k r : Cell h d)=Cell.area ⟨12+b.val,by omega⟩ u := cell_injective h d j eq
    cases e

theorem mayWrite_not_argument {h d j : ℕ} (i r : Fin (2^h)) (k : Fin 3) :
    ¬MayWrite h d j i ((blockBank h d copies j k).base+r.val) := by
  intro written
  obtain ⟨_,_,early|late⟩ := mayWrite_region written
  · have lower := separate h d copies j 3 11 (by decide)
    change allocatorBase h d copies j+_*_+_<bankBase h d copies j 3 at early
    unfold allocatorBase at early
    omega
  · have final := allocator_end h d copies j
    have cell : k.val*2^h+r.val < 3*2^h :=
      (Nat.add_lt_add_left r.isLt _).trans_le (by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ k.isLt)
    change bankBase h d copies j 14≤allocatorBase h d copies j+_*_+_ at late
    omega

def EndpointWords {h d w : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (m : Memory w) : Prop :=
  let p := history h d π j.val
  ∀ (r : Fin (2^h)) (k : Fin 3),m ((blockBank h d copies j.val k).base+r.val)=
    (Endpoints.words p.tiles (radix_pos h d) p.encode r k : Word w)

end Hierarchy.ProbeStage.Native

end OAI
