import OAI.Hierarchy.ProbeStrip
import OAI.Hierarchy.ProbeScore

namespace OAI
/-! # The common coordinate frame of an actual purchased H-tile strip -/

namespace Hierarchy.AdaptiveProbe.ChainStrip
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped BigOperators Classical
noncomputable section

abbrev edgeCount (depth : ℕ) := 2*depth+1
abbrev Columns (depth : ℕ) := TestColumns (Strip.steps (edgeCount depth)) 0 (edgeCount depth)
abbrev Axes (depth k : ℕ) := Fin (depth+1) × (Fin k × Bool)

def inlet (depth : ℕ) (j : Fin (depth+1)) : Columns depth := Strip.column _ ⟨2*j.val,by dsimp [edgeCount]; omega⟩
def outlet (depth : ℕ) (j : Fin (depth+1)) : Columns depth := Strip.column _ ⟨2*j.val+1,by dsimp [edgeCount]; omega⟩

def length (depth : ℕ) (e : Fin (edgeCount depth)) : ℝ := if e.val % 2=0 then 1 else 0

def commodity (depth k : ℕ) (i : Axes depth k) : LocalCommodity (Columns depth) k :=
  .altimeter (inlet depth i.1) (outlet depth i.1) i.2.1 i.2.2

def probe (depth : ℕ) (_ : Unit) : DistinctPair (Columns depth) :=
  ⟨inlet depth 0,outlet depth (Fin.last depth),fun eq => by
    have ord := congrArg (fun x : Columns depth => x.val.val) eq
    change 2*0=2*depth+1 at ord
    omega⟩

abbrev wires (depth k : ℕ) [SiteNaming (ColumnSite (Columns depth) k)] := ColumnWires.wires (Strip.horizontal (edgeCount depth)) (LocalCommodity.extraEnds (commodity depth k) (probe depth))
abbrev demands (depth k : ℕ) := ColumnWires.demand (I:=Columns depth) (H:=Fin (edgeCount depth)) (k:=k) (Sum.inl (α:=Axes depth k) (β:=Unit))
abbrev prices (depth k : ℕ) (M : ℝ) (y : Axes depth k → ℝ) := ColumnWires.quote (I:=Columns depth) (k:=k) M (length depth) (LocalCommodity.extraPrice (B:=Unit) y)

instance (depth : ℕ) : Nonempty (Columns depth) := ⟨Strip.column _ 0⟩
instance (depth k : ℕ) : Nonempty (ColumnWires.Role (Columns depth) (Fin (edgeCount depth)) (Axes depth k ⊕ Unit) k) :=
  ⟨.extra (.inr ())⟩
instance (depth k : ℕ) : Nonempty (Fin (Fintype.card (ColumnSite (Columns depth) k))) :=
  Fin.pos_iff_nonempty.mp (Fintype.card_pos (α:=ColumnSite (Columns depth) k))

/-- Exact Bregman frame data for each good purchased path, using only this one
fixed finite shape for every population size, row ordering, and dynamic inventory. -/
theorem frames {F : Type*} [Field F] (depth k : ℕ) [SiteNaming (ColumnSite (Columns depth) k)] (hk : 0 < k) (no : ¬ HasSpectralFlat F (k+1))
    {η : ℝ} (tol : 0 < η) : ∃ M₀ : ℕ, ∀ M : ℝ, 0 < M → M₀≤M →
    ∃ ε : ℝ, 0<ε ∧ ∀ y ∈ Set.Icc (0:Axes depth k → ℝ) (fun _ => M+1),
    Probe.discrepancy F (wires depth k) (demands depth k) (prices depth k M y) ≤ ε →
    ∃ zi zo : Fin (depth+1) → Coordinates k,
      (∀ j : ℕ, ∀ hj : j+1<depth+1, zo ⟨j,by omega⟩=zi ⟨j+1,hj⟩) ∧
      (∀ i : Axes depth k, |rise M (y i)-max (Source.sign i.2.2*(zo i.1 i.2.1-zi i.1 i.2.1)) 0|<η) ∧
      |0-max (dist (zi 0) (zo (Fin.last depth))-1) 0|<η := by
  have cap : ∀ e, length depth e≤1 := by intro e; unfold length; split <;> norm_num
  obtain ⟨N,ok⟩ := Strip.strip_flattening hk no (length depth) cap (commodity depth k) (probe depth) tol
  refine ⟨N,?_⟩; intro M pos large
  obtain ⟨ε,he,all⟩ := ok M pos large (fun _ => M+1)
  refine ⟨ε,he,?_⟩; intro y box pass
  obtain ⟨z,joined,read⟩ := all y box pass
  refine ⟨fun i => z (inlet depth i),fun i => z (outlet depth i),?_,?_,?_⟩
  · intro j hj
    let e : Fin (edgeCount depth) := ⟨2*j+1,by dsimp [edgeCount]; omega⟩
    have le : length depth e=0 := by simp [length,e,Nat.add_mod]
    convert joined e le using 1 <;> congr 2
  · exact fun i => read (.inl i)
  · exact read (.inr ())

end
end Hierarchy.AdaptiveProbe.ChainStrip

end OAI
