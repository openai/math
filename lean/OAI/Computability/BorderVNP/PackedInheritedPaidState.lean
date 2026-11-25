import OAI.Computability.BorderVNP.PackedBankBoxMerged
import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Persistent private state of a newly inserted paid term

The auxiliary bits are guessed first; the incident word array follows them.
The strided site fragment uses zero as its intrinsic offset and a single
private factor at local ordinal zero. Only one auxiliary string is accepted
for each incident input. These facts remain true for an empty multiplicity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.PaidSite

open Crossing CellSparse PaidBox
open scoped Classical
open private bits_left bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging

variable {n : ℕ} (w : Fin n → ℕ) (c incoming : ℕ) (starts : Fin n → ℕ)

/-- Two equal-size regions, cable-major and copy-major, of the intrinsic paid-site work bank. -/
def work := c*(∑ r,w r) + c*(∑ r,w r)

/-- Addresses of the actual cable bundles in the current incoming array. -/
def source (r : Fin n) := work w c + starts r

/-- A fresh persistent site with one local box, one layer, and the certified work extent. -/
def born (f : Factor) : Site :=
  ⟨work w c,incoming,[[f]],[(PaidBinding.fragment w c 0 0 (source w c starts) [[f]]).records]⟩

/-- The initial state exposes the true paid fragment, including its whole-bundle ties. -/
theorem directory (f : Factor) :
    (born w c incoming starts f).directory = PaidBinding.fragment w c 0 0 (source w c starts) [[f]] := by
  simp [Site.directory,Site.rows,born,PaidBinding.fragment]

/-- Every canonical incoming bundle lies in the site's current incidence area. -/
def Room : Prop := ∀ r, starts r + c*w r ≤ incoming

private theorem data_fits (room : Room w c incoming starts) (i : Fin c) (k : Fin (∑ r,w r)) :
    let b := (finSigmaFinEquiv (n := w)).symm k
    source w c starts b.1 + i.val*w b.1 + b.2.val < work w c + incoming := by
  intro b
  have h := (finProdFinEquiv (i,b.2)).isLt
  have hi : i.val*w b.1+b.2.val < c*w b.1 := by simpa [Nat.mul_comm,Nat.add_comm] using h
  have hr := room b.1
  unfold source
  omega

private theorem data_congr (room : Room w c incoming starts) {a b : ℕ → Bool}
    (h : ∀ k < work w c + incoming, a k = b k) :
    PaidBinding.data w c (source w c starts) a = PaidBinding.data w c (source w c starts) b := by
  funext i k
  exact h _ (data_fits w c incoming starts room i k)

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
    (position : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site)
    (starts : Fin (Fintype.card (Bundle (e.net a) v)) → ℕ)

local notation3 "ws" => PaidBox.widths (e.net a) v
local notation3 "f₀" => tableFactor e position a v
local notation3 "source₀" => source ws c starts
local notation3 "born₀" => born ws c incoming starts f₀
local notation3 "dir₀" => PaidBinding.fragment ws c 0 0 source₀ [[f₀]]

/-- On an arbitrary bit bank, the paid site succeeds precisely when its whole
work block is canonical. Each successful copy observes its actual paid-entry address. -/
theorem observe (bank : ℕ → Bool) :
    (born₀).observe bank = if ∀ t < work ws c, bank t = PaidBinding.canonical ws c source₀ bank t then
      some (List.ofFn fun i => (false,some (position (PaidBinding.entryAt c e a v source₀ bank i)))) else none := by
  have hrows : (born₀).rows = (dir₀).records := by simp [Site.rows,born]
  have iff' : (∀ r ∈ (born₀).rows, r.Valid (born₀).boxes bank) ↔
      ∀ t < work ws c, bank t = PaidBinding.canonical ws c source₀ bank t := by
    rw [hrows]
    simpa only [work,born,PaidBinding.fragment,List.length_cons,List.length_nil,zero_lt_one,true_and,Nat.zero_add] using
      PaidBinding.valid_iff ws c 0 0 source₀ [[f₀]] bank
  unfold Site.observe
  by_cases h : ∀ t < work ws c, bank t = PaidBinding.canonical ws c source₀ bank t
  · have hv := iff'.2 h
    rw [ite_eq_left hv,ite_eq_left h,directory]
    exact PaidBinding.observations c 0 0 e position a v source₀ [[f₀]] bank (by rfl) (hrows ▸ hv)
  · rw [ite_eq_right (mt iff'.1 h),ite_eq_right h]

/-- Every recorded entry and validity test of a newly born paid site depends only
on its complete finite bank. This is the locality invariant needed for inheritance. -/
theorem local_born (room : Room ws c incoming starts) : (born₀).Local := by
  intro b₁ b₂ h
  have hd := data_congr ws c incoming starts room h
  have hc : PaidBinding.canonical ws c source₀ b₁ = PaidBinding.canonical ws c source₀ b₂ := by
    unfold PaidBinding.canonical
    rw [hd]
  have ht : (∀ k < work ws c, b₁ k = PaidBinding.canonical ws c source₀ b₁ k) ↔
      ∀ k < work ws c, b₂ k = PaidBinding.canonical ws c source₀ b₂ k := by
    rw [hc]
    apply forall_congr'; intro k
    apply imp_congr_right; intro hk
    rw [h k (hk.trans_le (Nat.le_add_right _ _))]
  rw [observe,observe]
  by_cases hvalid : ∀ k < work ws c, b₁ k = PaidBinding.canonical ws c source₀ b₁ k
  · rw [ite_eq_left hvalid,ite_eq_left (ht.mp hvalid)]
    congr 2
    funext i
    unfold PaidBinding.entryAt
    rw [hd]
  · rw [ite_eq_right hvalid,ite_eq_right (mt ht.mpr hvalid)]

/-- With a fixed incoming vector, all physical source reads are independent of
the current private work guess. -/
theorem data_fixed (room : Room ws c incoming starts) (input : Fin incoming → Bool)
    (g₁ g₂ : Fin (work ws c) → Bool) :
    PaidBinding.data ws c source₀ (bits g₁ input) = PaidBinding.data ws c source₀ (bits g₂ input) := by
  funext i k
  let b := (finSigmaFinEquiv (n := ws)).symm k
  let off := starts b.1 + i.val*ws b.1 + b.2.val
  have ht : off < incoming := by
    have h := data_fits ws c incoming starts room i k
    change work ws c + starts b.1 + i.val*ws b.1 + b.2.val < work ws c + incoming at h
    dsimp only [off]
    omega
  let l : Fin incoming := ⟨off,ht⟩
  have hpos : work ws c + starts b.1 + i.val*ws b.1 + b.2.val = work ws c + l.val := by
    dsimp only [l,off]
    omega
  change bits g₁ input (work ws c + starts b.1 + i.val*ws b.1 + b.2.val) =
    bits g₂ input (work ws c + starts b.1 + i.val*ws b.1 + b.2.val)
  rw [hpos]
  exact (bits_right g₁ input l).trans (bits_right g₂ input l).symm

/-- The unique choice of all intrinsic paid work bits at a fixed input. -/
noncomputable def canonicalWork (input : Fin incoming → Bool) (t : Fin (work ws c)) : Bool :=
  PaidBinding.canonical ws c source₀ (bits (fun _ : Fin (work ws c) => false) input) t.val

/-- At fixed input the actual accepted work is exactly the canonical work vector,
and its entire list is returned before any specialization of an entry. -/
theorem observe_work (room : Room ws c incoming starts) (input : Fin incoming → Bool)
    (g : Fin (work ws c) → Bool) :
    let b := bits (fun _ : Fin (work ws c) => false) input
    (born₀).observe (bits g input) =
      if g = canonicalWork c incoming e a v starts input then
        some (List.ofFn fun i => (false,some (position (PaidBinding.entryAt c e a v source₀ b i)))) else none := by
  intro b
  let workBits := canonicalWork c incoming e a v starts input
  have hd := data_fixed c incoming e a v starts room input g (fun _ => false)
  have hc : PaidBinding.canonical ws c source₀ (bits g input) = PaidBinding.canonical ws c source₀ b := by
    unfold PaidBinding.canonical
    exact congrArg (fun f => Crossing.CellBox.stageBank (copies := c) (inputBank ws f) (c*∑ r,ws r) (src ws c)) hd
  have hcond : (∀ k < work ws c, bits g input k = PaidBinding.canonical ws c source₀ (bits g input) k) ↔
      g = workBits := by
    rw [hc]
    constructor
    · intro h
      funext k
      exact (bits_left g input k).symm.trans (h k.val k.isLt)
    · rintro rfl k hk
      exact bits_left workBits input ⟨k,hk⟩
  rw [observe]
  by_cases hg : g = workBits
  · rw [ite_eq_left (hcond.mpr hg),ite_eq_left hg]
    congr 2
    funext i
    unfold PaidBinding.entryAt
    exact congrArg (fun f => (false,some (position (⟨a,v,(fun u k => f i ((laneOrder (e.net a) v) (.inl ⟨u,k⟩))),
      (fun u k => f i ((laneOrder (e.net a) v) (.inr ⟨u,k⟩)))⟩ : e.Entry)))) hd
  · rw [ite_eq_right (mt hcond.mp hg),ite_eq_right hg]

/-- Summation over the entire fresh work block leaves exactly one observation
sequence with one genuine position per copy, for any additive interpretation. -/
theorem value_born {R : Type*} [AddCommMonoid R] (room : Room ws c incoming starts)
    (weight : List (Bool × Option ℕ) → R) (input : Fin incoming → Bool) :
    let b := bits (fun _ : Fin (work ws c) => false) input
    (born₀).value weight input =
      weight (List.ofFn fun i => (false,some (position (PaidBinding.entryAt c e a v source₀ b i)))) := by
  intro b
  change (∑ g : Fin (work ws c) → Bool, ((born₀).observe (bits g input)).elim 0 weight) = _
  simp_rw [observe_work c incoming e position a v starts room input]
  simp [apply_ite (fun o => Option.elim o 0 weight),b]

end Packing.Inherited.PaidSite

end BorderVNP
end Computability
end OAI
