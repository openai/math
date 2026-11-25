import OAI.Hierarchy.TaggedWidePurchasedCuts

namespace OAI
/-! # The charged shorter banks selected before filling their physical input pins -/
noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget TaggedShorterPacking TaggedShorterSupergroups
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork Real Filter
open scoped Classical Topology BigOperators

/-- Only the two actual compactor networks are chosen. The common directory
and dyadic physical dimensions are fixed independently of their existence. -/
structure Purchased (F : Type*) [Field F] {κ A : ℝ} (menu : WideMenu κ A) (x : WideParent κ A)
    (i : Fin menu.types) (D S M : ℕ) (C : ℝ) where
  near : Compactor F D (2^(menu.height i x)) (menu.height i x+menu.payload i x)
  far : Compactor F S M (Width (2^(menu.height i x)) (menu.height i x+menu.payload i x))
  copies : menu.copies i x=2*M
  bill : ∀{V : Type} (read : Input S D (menu.height i x+menu.payload i x)→V),
    ((CutFormat.mk S D M (menu.height i x) (menu.payload i x) near far read).cost:ℝ)≤C*((2:ℝ)^x.h*x.w)

namespace Purchased
variable {F : Type*} [Field F] {κ A : ℝ} {menu : WideMenu κ A} {x : WideParent κ A}
    {i : Fin menu.types} {D S M : ℕ} {C : ℝ} (a : Purchased F menu x i D S M C)

def cut {V : Type} (read : Input S D (menu.height i x+menu.payload i x)→V) : CutFormat F V :=
  ⟨S,D,M,menu.height i x,menu.payload i x,a.near,a.far,read⟩

theorem bank {V : Type} (read : Input S D (menu.height i x+menu.payload i x)→V) :
    (a.cut read).bank ⌊(menu.height i x:ℝ)^A⌋₊=menu.bank x i := by
  simp only [cut,CutFormat.bank,WideMenu.bank,a.copies,Nat.mul_comm]

theorem work {V : Type} (read : Input S D (menu.height i x+menu.payload i x)→V) :
    ((a.cut read).cost:ℝ)≤C*((2:ℝ)^x.h*x.w) := a.bill read
end Purchased

variable {F : Type*} [Field F] {u : ℝ→ℝ} {s κ A ε p q Q σ Λ δ η ξ : ℝ}

def purchaseSlots (h W k attempts ell : ℕ) := 2^(superAddress W (2*copies k attempts) h)*2^ell

def purchaseModules (W : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) {κ A : ℝ} (menu : WideMenu κ A) (x : WideParent κ A)
    (i : Fin menu.types) := ⌈6*typeFraction u δ ξ (logb x.h x.w) (W,i.val)*(2:ℝ)^x.h/(2:ℝ)^(menu.height i x)⌉₊

def purchaseCandidates (h W k attempts D height M : ℕ) :=
  let roles:=copies k attempts
  let dir:=stageDir h W roles (2*roles) (show 2*roles≤2^(2*roles) from Nat.lt_two_pow_self.le)
  max M (dir.groups*batches D (2^(height-1)))

/-- The first stage of each shorter call uses two halves. Its one real
module per group is covered at the same cutoff used to buy both compactors. -/
def GroupRoom (W k attempts : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (menu : WideMenu κ A) (x : WideParent κ A) : Prop :=
  let roles:=copies k attempts
  let dir:=stageDir x.h W roles (2*roles) (show 2*roles≤2^(2*roles) from Nat.lt_two_pow_self.le)
  ∀i:Fin menu.types, let half : ℕ := 2^(menu.height i x-1)
    0<half ∧ 2*half=2^(menu.height i x) ∧ (dir.groups:ℝ)*(2*half)≤typeFraction u δ ξ (logb x.h x.w) (W,i.val)*(2:ℝ)^x.h

/-- The single shortening offset works for the physical paired input
compactors of every type at every sufficiently large parent format. -/
theorem choose_purchases (profile : TaggedWidthProfile.Admissible s u) (price : Choice u A ε p q Q σ Λ δ η ξ)
    (W m k attempts ell : ℕ) (hW : 0<W) (hk : 0≤κ) :
    ∃short:ℕ,∃C:ℝ,0≤C ∧ ∀ᶠ x in WideParent.large κ A,
      let menu:=(typeMenu κ A W m k attempts ell hW (fun _=>short+ell)).menu u δ ξ
      let D:=purchaseSlots x.h W k attempts ell
      GroupRoom W k attempts u δ ξ menu x ∧ Nonempty (∀i:Fin (m+1),let count:=purchaseModules W u δ ξ menu x i
        Purchased F menu x i D (purchaseCandidates x.h W k attempts D (menu.height i x) count) count C) := by
  obtain ⟨short,C,ready⟩:=purchased_cuts F profile price W m k attempts ell hW hk
  refine ⟨short,max C 0,le_max_right ..,?_⟩
  filter_upwards [ready] with x good
  dsimp only
  have one (i:Fin (m+1)) := good i
  let menu:=(typeMenu κ A W m k attempts ell hW (fun _=>short+ell)).menu u δ ξ
  let D:=purchaseSlots x.h W k attempts ell
  have all (i:Fin (m+1)) : let count:=purchaseModules W u δ ξ menu x i
      Nonempty (Purchased F menu x i D (purchaseCandidates x.h W k attempts D (menu.height i x) count) count (max C 0)) := by
    obtain ⟨copy,_,_,_,near,far,cost⟩:=one i
    refine ⟨⟨near,far,copy,fun read=>(cost read).trans ?_⟩⟩
    exact mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)
  refine ⟨?_,⟨fun i=>Classical.choice (all i)⟩⟩
  intro i
  obtain ⟨_,pos,twice,groups,_⟩:=one i
  exact ⟨pos,twice,groups⟩

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
