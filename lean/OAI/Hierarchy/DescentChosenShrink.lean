import OAI.Hierarchy.DescentSelectedInvoice
import OAI.Hierarchy.DescentMarkedShrink
import OAI.Hierarchy.DescentMarkedLoad

namespace OAI
/-! # Sparse whole-pack coloring shrinks each actual branch -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentWalshTables
open scoped BigOperators Classical
noncomputable section

private theorem shrink_scalars (u : ℝ) (a z b slots classes tether K : ℕ)
    (scale : 0<u) (hz : 0<z) (hb : 0<b) (hs : 0<slots)
    (cutoff : 481*128*(K+1)≤2^a) :
    0<(2:ℝ)^a ∧ 0<u*((z*b:ℕ):ℝ)*slots ∧ 0≤(classes:ℝ) ∧
      0≤u*tether ∧ 0≤(K:ℝ) ∧ 481*128*((K:ℝ)+1)≤(2:ℝ)^a := by
  refine ⟨pow_pos (by norm_num) a,?_,Nat.cast_nonneg _,mul_nonneg scale.le (Nat.cast_nonneg _),
    Nat.cast_nonneg _,?_⟩
  · exact mul_pos (mul_pos scale (Nat.cast_pos.mpr (Nat.mul_pos hz hb))) (Nat.cast_pos.mpr hs)
  · exact_mod_cast cutoff

variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable {F : Type*} [Field F] (A : MarkedWorld F d P bits) (G : PoweredGadget F)
private def selectedConclusion {I C : Type} [Fintype I] (pick : I × Fin 2 ↪ A.graph.Edge)
    (pack : A.graph.Site → C) (z : ℕ) (hz : 0 < z) (u β ε : ℝ) : Prop :=
  ∃ fit : ∀ (i : I) s, A.graph.width (pick (i,s)) = z*G.b,
    let branch := A.selected G pick (fun _ => z) (fun _ => hz) fit pack
    (∀ pins, (∑ p, (branch p).value pins) = A.value pins) ∧
      ∀ p, (branch p).tetherWidth ≤ A.tetherWidth ∧
        u*(branch p).liveWidth ≤ (1-(2-G.rate)/4)*(u*A.liveWidth) +
          (2-G.rate)*(((β+1)*(u*A.tetherWidth)+ε)/4)

variable (position : A.graph.Site→V) (block : A.graph.Site→Block k) (full : A.graph.Site→ℕ)
variable (near : V→Finset V) (D a pairCap unit : ℕ)
variable (small : ∀ (v : V) (x : Block k), blockMass A.graph position block full v x ≤ unit*pairCap)
local notation "home" => occupiedHome A.graph position block full near D a (unit*pairCap) small
local notation "Col" => (occupied A.graph (unit*pairCap) near D a (blockMass A.graph position block full) small position block)

/-! The affine color supplied by the native scan determines each selected pair. -/
set_option maxHeartbeats 1800000 in
omit [Fintype V] in
theorem chosen_shrink_of_bound {Aty : Type*}
    (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (hu : 0<unit)
    (covered : ∀v,unit*live (nativeTraffic A.graph A.core home) v≤full v)
    (adj : ∀e∈A.core,position (A.graph.dst e)∈near (position (A.graph.src e)))
    (rev : ∀e∈A.core,position (A.graph.src e)∈near (position (A.graph.dst e)))
    (same : ∀e∈A.core,block (A.graph.src e)=block (A.graph.dst e))
    (z : ℕ) (hz : 0<z) (fixed : ∀e∈A.core,A.graph.width e=z*G.b) (u : ℝ) (scale : 0<u)
    (hub : A.graph.Site → Bool) (atoms : A.graph.Site → List Aty) (β atomUnit ε roots : ℝ)
    (he : 0≤ε) (hβ : 0≤β) (hcap : 0<pairCap)
    (inside : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (outside : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e))
    (retain : atomUnit*(∑v,((atoms v).length:ℝ))≤ε)
    (cutoff : 481*128*(((Δ+1)*(D+1+2*2^D):ℕ)+1)≤2^a)
    (slack : roots*((2:ℝ)^a*(u*(z*G.b:ℕ)*pairCap))≤ε)
    (count : (Fintype.card Col:ℝ)≤roots +
      240*(∑v,A.siteLoad hub atoms u β atomUnit v)/((2:ℝ)^a*(u*(z*G.b:ℕ)*pairCap))) (alpha : Bits k) (beta : ZMod 2)
    (balanced : affineBalance A.graph A.core position block full near D a pairCap unit small alpha beta) :
      let color := fun v=>decide (binaryRow alpha ((DescentColonies.address k).symm (block v))+beta=0)
      let I := NativePair A.graph A.core home color pairCap
      let pick := colorPick A.graph A.core home color pairCap
      selectedConclusion A G (I:=I) pick (coloredPack A.graph A.core home color pairCap) z hz u β ε := by
  intro color I pick
  obtain ⟨marked,fit,paired⟩ :=
    selected_invoice_of_bound A G position block full near D a pairCap unit small Δ degree hu covered
      adj rev same z fixed u scale alpha beta balanced
  obtain ⟨hc,hB,hQ,hE,hK,hcut⟩ := shrink_scalars u a z G.b pairCap (Fintype.card Col)
    A.tetherWidth ((Δ+1)*(D+1+2*2^D)) scale hz G.base_pos hcap cutoff
  have bill := A.siteLoad_bound hub atoms u β atomUnit ε inside outside retain
  unfold selectedConclusion
  refine ⟨fit,?_⟩
  exact A.shrink_paid G pick (fun _=>z) (fun _=>hz) fit
    (coloredPack A.graph A.core home color pairCap) marked u scale
    ((2:ℝ)^a) (u*(z*G.b:ℕ)*pairCap) (Fintype.card Col) roots
    (∑v,A.siteLoad hub atoms u β atomUnit v) (u*A.tetherWidth) ε β ((Δ+1)*(D+1+2*2^D):ℕ)
    hc hB hQ hE he hβ hK hcut count slack bill paired

omit [Fintype V] in
/-- The only count passed from the multiplier scan is the number of its
actual occupied classes. The affine color, matched edges, replacement,
contraction identity and branch shrinkage are produced together. -/
theorem chosen_shrink {Aty : Type*}
    (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (hu : 0<unit)
    (covered : ∀v,unit*live (nativeTraffic A.graph A.core home) v≤full v)
    (adj : ∀e∈A.core,position (A.graph.dst e)∈near (position (A.graph.src e)))
    (rev : ∀e∈A.core,position (A.graph.src e)∈near (position (A.graph.dst e)))
    (same : ∀e∈A.core,block (A.graph.src e)=block (A.graph.dst e))
    (z : ℕ) (hz : 0<z) (fixed : ∀e∈A.core,A.graph.width e=z*G.b) (u : ℝ) (scale : 0<u)
    (hub : A.graph.Site → Bool) (atoms : A.graph.Site → List Aty) (β atomUnit ε roots : ℝ)
    (he : 0≤ε) (hβ : 0≤β) (hcap : 0<pairCap)
    (inside : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (outside : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e))
    (retain : atomUnit*(∑v,((atoms v).length:ℝ))≤ε)
    (cutoff : 481*128*(((Δ+1)*(D+1+2*2^D):ℕ)+1)≤2^a)
    (slack : roots*((2:ℝ)^a*(u*(z*G.b:ℕ)*pairCap))≤ε)
    (count : (Fintype.card Col:ℝ)≤roots +
      240*(∑v,A.siteLoad hub atoms u β atomUnit v)/((2:ℝ)^a*(u*(z*G.b:ℕ)*pairCap))) :
    ∃ (alpha : Bits k) (beta : ZMod 2),
      let color := fun v=>decide (binaryRow alpha ((DescentColonies.address k).symm (block v))+beta=0)
      let I := NativePair A.graph A.core home color pairCap
      let pick := colorPick A.graph A.core home color pairCap
      selectedConclusion A G (I:=I) pick (coloredPack A.graph A.core home color pairCap) z hz u β ε := by
  obtain ⟨alpha,beta,h⟩ := exists_affineBalance A.graph A.core position block full near D a pairCap unit small hu covered
  exact ⟨alpha,beta,chosen_shrink_of_bound A G position block full near D a pairCap unit small
    Δ degree hu covered adj rev same z hz fixed u scale hub atoms β atomUnit ε roots he hβ hcap inside outside retain cutoff slack count alpha beta h⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
