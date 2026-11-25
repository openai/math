import OAI.Hierarchy.ProbeRealization
import OAI.Hierarchy.ProbeFlatteningThreshold

namespace OAI
/-! # Local flattening for the quoted commodity and test prices on a wired ball -/

namespace Hierarchy.AdaptiveProbe
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
noncomputable section

variable {F I E A : Type*} [Field F] [Fintype I] [Fintype E] [Fintype A] [Nonempty E]
variable {S k : ℕ} [Nonempty (Fin S)]

def Joins (e : Chord S) (x y : Fin S) := e.val=(x,y) ∨ e.val=(y,x)

theorem Joins.price {e : Chord S} {x y : Fin S} (pair : Joins e x y)
    (φ : Probe.Spectrum F S) (s : ℝ) : s*Probe.distance φ e=rawWireDistance φ s x y := by
  have scale : s*Probe.distance φ e=rawWireDistance φ s e.val.1 e.val.2 := by
    simp [Probe.distance,rawWireDistance,rawLogPrice]
  rw [scale]
  rcases pair with p|p
  · rw [p]
  · rw [p]
    exact rawWireDistance_symm ..

/-- Upper price obtained along physical core wires, free identifications and their concatenation. -/
inductive WireBound (edge : E → Chord S) (p : E → ℝ) : Fin S → Fin S → ℝ → Prop
  | wire (e : E) (x y : Fin S) (pair : Joins (edge e) x y) : WireBound edge p x y (p e)
  | self (x : Fin S) : WireBound edge p x x 0
  | symm {x y v} : WireBound edge p x y v → WireBound edge p y x v
  | append {x y z b c} : WireBound edge p x y b → WireBound edge p y z c → WireBound edge p x z (b+c)
  | weaken {x y b c} : WireBound edge p x y b → b ≤ c → WireBound edge p x y c

omit [Fintype E] [Nonempty E] in
theorem WireBound.sound {edge : E → Chord S} {p : E → ℝ} {x y : Fin S} {bound : ℝ}
    (proof : WireBound edge p x y bound) (φ : Probe.Spectrum F S) (s : ℝ) (hs : 0 ≤ s)
    (ok : ∀ e,s*Probe.distance φ (edge e) ≤ p e) : rawWireDistance φ s x y ≤ bound := by
  induction proof with
  | wire e x y pair => exact (pair.price φ s).symm.trans_le (ok e)
  | self x => exact (rawWireDistance_self φ s hs x).le
  | symm prev ih => exact (rawWireDistance_symm ..).trans_le ih
  | append p q ih ih' => exact (rawWireDistance_triangle φ s hs ..).trans (add_le_add ih ih')
  | weaken p le ih => exact ih.trans le

def demanded (edge : E → Chord S) (req : A → E) (p : E → ℝ) (x y : Fin S) (v : ℝ) :=
  ∃ a, Joins (edge (req a)) x y ∧ p (req a)=v

omit [Fintype E] [Fintype A] [Nonempty E] in
theorem demanded_sound {edge : E → Chord S} {req : A → E} {p : E → ℝ} {x y : Fin S} {v : ℝ}
    (d : demanded edge req p x y v) (φ : Probe.Spectrum F S) (s : ℝ)
    (ok : ∀ a,s*Probe.distance φ (edge (req a))=p (req a)) : rawWireDistance φ s x y=v := by
  obtain ⟨a,pair,h⟩ := d
  exact (pair.price φ s).symm.trans ((ok a).trans h)

/-- A horizontal path, its tested endpoint link, or a tile's signed altimeter. -/
inductive Source (I E : Type*) (k : ℕ)
  | payload (i i' : I) (e : E)
  | probe (i i' : I)
  | altimeter (i i' : I) (j : Fin k) (s : Bool) (e : E)

namespace Source
def sign (s : Bool) : ℝ := if s then 1 else -1

def quote (R : ℝ) (q : Source I E k) (p : E → ℝ) : ℝ :=
  match q with
  | .payload _ _ e => p e
  | .probe _ _ => 0
  | .altimeter _ _ _ _ e => max (p e-R) 0

def model (q : Source I E k) (z : I → Coordinates k) : ℝ :=
  match q with
  | .payload i i' _ => dist (z i) (z i')
  | .probe i i' => max (dist (z i) (z i')-1) 0
  | .altimeter i i' j s _ => max (sign s*(z i' j-z i j)) 0

def wired (q : Source I E k) (edge : E → Chord S) (req : A → E) (p : E → ℝ)
    (cent : I → Fin S) (port : I → Fin k → Bool → Fin S) : Prop :=
  match q with
  | .payload i i' e => demanded edge req p (cent i) (cent i') (p e)
  | .probe i i' => WireBound edge p (cent i) (cent i') 1
  | .altimeter i i' j s e => demanded edge req p (cent i) (port i' j s) (p e)

end Source

/-- This is the finite-format local flattening lemma. The hypotheses reference only
the actual demand list, bounded paths of installed wires and physical quoted prices.
There is one fixed discrepancy threshold for the whole compact price box. -/
theorem local_flattening {L : Type*} [Finite L] (base : I) (no : ¬HasSpectralFlat F (k+1))
    (K : ℝ) (join : I → I → Prop) {η : ℝ} (hη : 0<η) :
    ∃ N : ℕ, ∀ R : ℝ, 0 < R → (N:ℝ) ≤ R →
    ∀ (edge : E → Chord S) (req : A → E), Probe.Connected edge →
    ∀ (cent : I → Fin S) (port : I → Fin k → Bool → Fin S) (obs : L → Source I E k)
      (box : Set (E → ℝ)), IsCompact box →
    (∀ p ∈ box,
      (∀ i j, demanded edge req p (port i j false) (port i j true) (2*R)) ∧
      (∀ i j, WireBound edge p (port i j false) (cent i) R) ∧
      (∀ i j, WireBound edge p (cent i) (port i j true) R) ∧
      (∀ i i', WireBound edge p (cent i) (cent i') K) ∧
      (∀ i i' j s, WireBound edge p (port i j s) (port i' j s) K) ∧
      (∀ i j l, j≠l → ∀ s t, WireBound edge p (port i j s) (port i l t) (Real.sqrt 2*R+1)) ∧
      (∀ i i', join i i' → WireBound edge p (cent i) (cent i') 0) ∧
      ∀ l, (obs l).wired edge req p cent port) →
    ∃ ε : ℝ, 0<ε ∧ ∀ p ∈ box, Probe.discrepancy F edge req p≤ε →
      ∃ z : I → Coordinates k, (∀ i i',join i i' → z i=z i') ∧
      ∀ l, |(obs l).quote R p-(obs l).model z|<η := by
  have half : 0<η/2 := by positivity
  obtain ⟨N,flatten⟩ := normalized_flattening (S:=S) base no K join half
  refine ⟨N,?_⟩
  intro R pos wide edge req conn cent port obs box compact setup
  refine Probe.flattening_threshold edge req conn box compact (fun l => (obs l).quote R) ?_
    (fun z : I → Coordinates k => ∀ i i',join i i' → z i=z i') (fun z l => (obs l).model z) hη ?_
  · intro l
    cases obs l with
    | payload i i' e => exact continuous_apply e
    | probe i i' => exact continuous_const
    | altimeter i i' j s e => exact ((continuous_apply e).sub continuous_const).max continuous_const
  · intro p inside passed
    obtain ⟨φ,s,hs,upper,exact'⟩ := Classical.not_not.mp passed
    obtain ⟨diam,left,right,distance,ends,cross,joined,reads⟩ := setup p inside
    have collapse (i i' : I) (h : join i i') : rawWireDistance φ s (cent i) (cent i')=0 :=
      le_antisymm ((joined i i' h).sound φ s hs upper) (rawLogPrice_nonneg φ hs _)
    obtain ⟨z,seams,hcenter,hend⟩ := flatten φ s R cent port hs pos wide
      (fun i j => demanded_sound (diam i j) φ s exact') (fun i j => (left i j).sound φ s hs upper)
      (fun i j => (right i j).sound φ s hs upper) (fun i i' => (distance i i').sound φ s hs upper)
      (fun i i' j t => (ends i i' j t).sound φ s hs upper)
      (fun i j l jl u v => (cross i j l jl u v).sound φ s hs upper) collapse
    refine ⟨z,seams,?_⟩
    intro l
    have wired := reads l
    cases h : obs l with
    | payload i i' e =>
      rw [h] at wired
      change |p e-dist (z i) (z i')| ≤ η/2
      rw [←demanded_sound wired φ s exact']
      exact (hcenter i i').le
    | altimeter i i' j b e =>
      rw [h] at wired
      change |max (p e-R) 0 - max ((if b then (1:ℝ) else -1)*(z i' j-z i j)) 0| ≤ η/2
      rw [←demanded_sound wired φ s exact']
      exact (hend i i' j b).le
    | probe i i' =>
      rw [h] at wired
      have bound := wired.sound φ s hs upper
      have lower := (abs_lt.mp (hcenter i i')).1
      change |0-max (dist (z i) (z i')-1) 0|≤η/2
      rw [zero_sub,abs_neg,abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith) half.le

end
end Hierarchy.AdaptiveProbe

end OAI
