import OAI.Computability.NearSquareRoot.InterchangeROMLeafMasksSingle
import OAI.Computability.NearSquareRoot.InterchangeROMLeafMasksShape
import OAI.Computability.NearSquareRoot.InterchangeROMAddressBank
import OAI.Computability.NearSquareRoot.InterchangeROMLeaf

/-! # Compiling all leaf masks in physical request order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeafMasks

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom IntegerMultiplication.Adic
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMAddress
  NearSquareRoot.InterchangeROMLeafMasksShape

/-- The radix is among the data, so the code witnesses on this domain are
uniform over exponents and scheduler configurations. -/
abbrev Instance := {z : Sigma Request // 2 ≤ z.1 ∧ Request.Admissible z.2}

namespace Instance

abbrev radix (s : Instance) := s.val.1
abbrev req (s : Instance) := s.val.2
abbrev D (s : Instance) := (line s.radix s.req.width).count
abbrev N (s : Instance) := s.req.rows.count

private theorem posParts (s : Instance) :
    0 < (layout s.req.before).count ∧ 0 < s.D ∧ 0 < (layout s.req.between).count ∧
      0 < (layout s.req.after_).count := by
  have ok := s.property.2
  refine ⟨?_,?_,?_,?_⟩
  · rw [Dims.space]; exact wide _ (fun j hj => (ok j (by simp [hj])).1)
  · rw [D,lineSize]; exact Nat.pow_pos ((by decide : 0 < 2).trans_le s.property.1)
  · rw [Dims.space]; exact wide _ (fun j hj => (ok j (by simp [hj])).1)
  · rw [Dims.space]; exact wide _ (fun j hj => (ok j (by simp [hj])).1)

theorem size_rulers (i : Instance) : size (rulers i.req) + 1 ≤ 20 * i.N := by
  obtain ⟨pp,pd,pg,pb⟩ := posParts i
  let P := (layout i.req.before).count
  let d := i.D
  let g := (layout i.req.between).count
  let b := (layout i.req.after_).count
  let tail := g*(d*b)
  have hdb : 0 < d*b := Nat.mul_pos pd pb
  have ht : 0 < tail := Nat.mul_pos pg hdb
  have le₁ : d*tail ≤ P*(d*tail) := Nat.le_mul_of_pos_left _ pp
  have le₂ : tail ≤ P*(d*tail) := (Nat.le_mul_of_pos_left _ pd).trans le₁
  have le₃ : d*b ≤ tail := Nat.le_mul_of_pos_left _ pg
  have le₄ : b ≤ P*(d*tail) := ((Nat.le_mul_of_pos_left _ pd).trans le₃).trans le₂
  have le₅ : d ≤ P*(d*tail) := ((Nat.le_mul_of_pos_right _ pb).trans le₃).trans le₂
  have le₆ : g ≤ P*(d*tail) := (Nat.le_mul_of_pos_right _ hdb).trans le₂
  have le₇ : P ≤ P*(d*tail) := Nat.le_mul_of_pos_right _ (Nat.mul_pos pd ht)
  change size (tally P,tally d,tally g,tally b,tally tail)+1 ≤ 20*i.N
  rw [show i.N = P*(d*tail) by change ((layout i.req.before).cart ((line i.radix i.req.width).cart ((layout i.req.between).cart ((line i.radix i.req.width).cart (layout i.req.after_))))).count = _; simp only [Series.count_cart]; rfl]
  simp only [size_prod,size_tally,tally_length]
  omega

abbrev Rank (s : Instance) := Fin s.D × Fin s.D

def desc (s : Instance) (p : Rank s) : Query := (rulers s.req,tally p.1.val,tally p.2.val)

noncomputable def coords (s : Instance) (p : Rank s) : List Bool :=
  s.req.rows.tab (fun z => decide ((line s.radix s.req.width).index z.2.1 = p.1 ∧
    (line s.radix s.req.width).index z.2.2.2.1 = p.2))

private theorem runOne :
    Task (fun j : Sigma Rank => j.1.N) (fun j => send (desc j.1 j.2))
      (fun j => send (coords j.1 j.2)) :=
  single (fun j : Sigma Rank => layout j.1.req.before) (fun j => line j.1.radix j.1.req.width)
    (fun j => layout j.1.req.between) (fun j => layout j.1.req.after_)
    (fun j => (posParts j.1).1) (fun j => (posParts j.1).2.1)
    (fun j => (posParts j.1).2.2.1) (fun j => (posParts j.1).2.2.2)
    (fun j => j.2.1) (fun j => j.2.2)

noncomputable def descs (i : Instance) := (InterchangeROMLeaf.ranks i.D).tab
  fun z => (i.desc z,i.desc z.swap)

private theorem sum_le {A : Type} (ls : List A) (f : A → ℕ) (k : ℕ) (h : ∀ x ∈ ls, f x ≤ k) :
    costSum f ls ≤ ls.length * k := by
  apply (costSum_le (u:=fun _ => k) h).trans
  simp [costSum]

private theorem descSize (i : Instance) (u : Rank i) : size (i.desc u) ≤ 65*i.N := by
  have h := i.size_rulers
  have du : 2*i.D ≤ size (rulers i.req) := by
    simp only [InterchangeROMLeafMasksShape.rulers,size_prod,size_tally,tally_length,D,radix]
    omega
  have hu := u.1.isLt
  have hv := u.2.isLt
  change size (rulers i.req) + (size (tally u.1.val) + size (tally u.2.val) + 1) + 1 ≤ _
  rw [size_tally,size_tally,tally_length,tally_length]
  omega

private theorem forest_tab {A B : Type} [Codec B] (s : Series A) (f : A → B) :
    Task.forest (fun x => send (f x)) s.explore = send (s.tab f) := by
  rw [← Task.forest_map,Task.forest_send]
  rfl

theorem materialize :
    Space.BoundedTask (fun i : Instance => (i.D+1)^2 * i.N) (fun i => (i.D+1)^2 * i.N)
      (fun i => send i.descs) (fun i => send ((InterchangeROMLeaf.batch i.req).colors.map
        (InterchangeROMLeaf.batch i.req).masks)) := by
  let J := Sigma Rank
  let tag (j : J) := send (desc j.1 j.2)
  let mask (j : J) := send (coords j.1 j.2)
  let t (j : J) := j.1.N
  let faces (i : Instance) (u : Rank i) : J × J := (⟨i,u⟩,⟨i,u.swap⟩)
  let list (i : Instance) := (InterchangeROMLeaf.ranks i.D).tab (faces i)
  have len i : (list i).length = i.D^2 := by simp [list,InterchangeROMLeaf.ranks,pow_two]
  have score i : costSum (pairPrice tag t) (list i) ≤ (list i).length*(67*i.N) := by
    apply sum_le
    intro x hx
    obtain ⟨u,rfl⟩ := (Series.elements ..).mp hx
    change size (i.desc u)+i.N+i.N ≤ _
    have := descSize i u
    omega
  have mem i : costSum (fun x => (pairDesc tag x).count) (list i) ≤ (list i).length*(130*i.N+1) := by
    apply sum_le
    intro x hx
    obtain ⟨u,rfl⟩ := (Series.elements ..).mp hx
    change size (i.desc u) + size (i.desc u.swap) + 1 ≤ _
    have := descSize i u
    have := descSize i u.swap
    omega
  have src i : Task.forest (pairDesc tag) (list i) = send i.descs := by
    simp only [list,Series.tab,Task.forest_map]
    exact forest_tab (InterchangeROMLeaf.ranks i.D) (fun p => (i.desc p,i.desc p.swap))
  have dst i : Task.forest (pairMasks mask) (list i) =
      send ((InterchangeROMLeaf.batch i.req).colors.map (InterchangeROMLeaf.batch i.req).masks) := by
    rw [InterchangeROMLeaf.bank_eq]
    simp only [list,Series.tab,Task.forest_map]
    exact forest_tab (InterchangeROMLeaf.ranks i.D) (InterchangeROMLeaf.masks i.req)
  have pay (i : Instance) : (197*i.N+2)*i.D^2+1 ≤ 199*((i.D+1)^2*i.N+1) := by
    have pN : 0 < i.N := by
      have := size_pos (rulers i.req)
      have := size_rulers i
      omega
    nlinarith [Nat.mul_le_mul_right (i.D^2) pN,
      Nat.mul_le_mul_right i.N (Nat.pow_le_pow_left (Nat.le_succ i.D) 2)]
  have ready := (bank_task tag mask t runOne).on list
  have run := Space.BoundedTask.of_time ready
  apply (run.conform (fun _ => rfl) (fun _ => rfl) src dst).bound 200 400
  · intro i
    have a := score i
    have d := mem i
    rw [len] at a d
    change bankPrice tag t (list i) + 1 ≤ _
    rw [bankPrice,Task.forest_count,len]
    rw [Nat.mul_comm (i.D^2)] at a d
    nlinarith [pay i]
  · intro i
    have a := score i
    have d := mem i
    rw [len] at a d
    change (Task.forest (pairDesc tag) (list i)).count + bankPrice tag t (list i) + 1 ≤ _
    rw [bankPrice,Task.forest_count,len]
    nlinarith [pay i,Nat.mul_le_mul_right (i.D^2) (show 1 ≤ i.N from by have := size_rulers i; omega)]

end Instance
end InterchangeROMLeafMasks

end NearSquareRoot
end Computability
end OAI
