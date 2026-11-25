import OAI.Hierarchy.DescentPackedMatchPortInventory

namespace OAI
/-! # Numerical order of all original source slots in the two packed matching streams -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open scoped Classical
noncomputable section
variable {r D p d : ℕ} (u : Panel r D p d)

def targetCode (z : Port r p) := ((peer u z.1 z.2).map (fun v=>bin u v z.1)).getD 0

def lex3 {I : Type*} (a b c : I→ℕ) (x y : I) := a x<a y ∨ a x=a y ∧ (b x<b y ∨ b x=b y ∧ c x<c y)

def primary (side : Bool) (z : Port r p) := if side then targetCode u z else z.1.val
def secondary (side : Bool) (z : Port r p) := if side then z.1.val else targetCode u z

def stream (n key : ℕ) (side : Bool) := if side then thickStream u n key else thinStream u n key

theorem site_sorted (key : ℕ) (side : Bool) : (sites u key side).Pairwise (·<·) :=
  (List.pairwise_ofFn.mpr (fun _ _ h=>h) : (List.finRange r).Pairwise (·<·)).filter _

theorem bin_key {x : Fin r} {b : ℕ} {i : Port r p} (mem : i∈atBin u x b) : i.1=x ∧ targetCode u i=b := by
  obtain ⟨atX,j,hit,code⟩ := (at_mem u).mp mem
  exact ⟨atX,by simp only [targetCode,atX,hit,Option.map_some,Option.getD_some,code]⟩

theorem stream_ordered (n key : ℕ) (side : Bool) : (stream u n key side).Pairwise
    (lex3 (primary u side) (secondary u side) (fun z=>z.2.val)) := by
  let t : Port r p→ℕ := targetCode u; let a : Port r p→ℕ := fun z=>z.1.val;let b : Port r p→ℕ := fun z=>z.2.val
  have range (l : ℕ) : (List.finRange l).Pairwise (·<·) := List.pairwise_ofFn.mpr (fun _ _ h=>h)
  have localSort (R : Port r p→ℕ) (Q : Port r p→ℕ) (x : Fin r) (v : ℕ)
      (tie : ∀y∈atBin u x v,∀z∈atBin u x v,R y=R z ∧ Q y=Q z) :
      (atBin u x v).Pairwise (lex3 R Q b) := by
    apply (slots_ordered u x v).imp_of_mem
    intro y z hy hz lt
    exact Or.inr ⟨(tie y hy z hz).1,Or.inr ⟨(tie y hy z hz).2,lt⟩⟩
  cases side with
  | false=>
    change ((sites u key false).flatMap (inBlock u n)).Pairwise (lex3 a t b)
    apply List.pairwise_flatMap.mpr
    refine ⟨?_,?_⟩
    · intro x _
      apply List.pairwise_flatMap.mpr
      refine ⟨fun v _=>localSort a t x v.val (fun y hy z hz=>?_),?_⟩
      · obtain ⟨a₁,t₁⟩:=bin_key u hy;obtain ⟨a₂,t₂⟩:=bin_key u hz
        exact ⟨congrArg Fin.val (a₁.trans a₂.symm),t₁.trans t₂.symm⟩
      · apply (range n).imp
        intro v w lt y hy z hz
        obtain ⟨a₁,t₁⟩:=bin_key u hy;obtain ⟨a₂,t₂⟩:=bin_key u hz
        exact Or.inr ⟨congrArg Fin.val (a₁.trans a₂.symm),Or.inl (by simpa only [t,t₁,t₂] using Fin.lt_def.mp lt)⟩
    · apply (site_sorted u key false).imp
      intro x y lt l hl v hv
      have l₁:=((in_mem u).mp hl).1;have v₁:=((in_mem u).mp hv).1
      exact Or.inl (by simpa only [a,l₁,v₁] using Fin.lt_def.mp lt)
  | true=>
    change ((List.finRange n).flatMap (fun v=>thickBins u key v.val)).Pairwise (lex3 t a b)
    apply List.pairwise_flatMap.mpr
    refine ⟨?_,?_⟩
    · intro v _
      apply List.pairwise_flatMap.mpr
      refine ⟨fun x _=>localSort t a x v.val (fun y hy z hz=>?_),?_⟩
      · obtain ⟨a₁,t₁⟩:=bin_key u hy;obtain ⟨a₂,t₂⟩:=bin_key u hz
        exact ⟨t₁.trans t₂.symm,congrArg Fin.val (a₁.trans a₂.symm)⟩
      · apply (site_sorted u key true).imp
        intro x y lt l hl z hz
        obtain ⟨a₁,t₁⟩:=bin_key u hl;obtain ⟨a₂,t₂⟩:=bin_key u hz
        exact Or.inr ⟨t₁.trans t₂.symm,Or.inl (by simpa only [a,a₁,a₂] using Fin.lt_def.mp lt)⟩
    · apply (range n).imp
      intro i j lt x hx y hy
      obtain ⟨_,v,sv,bv⟩:=(thick_mem u).mp hx
      obtain ⟨_,w,sw,bw⟩:=(thick_mem u).mp hy
      exact Or.inl (by simpa only [t,targetCode,sv,sw,Option.map_some,Option.getD_some,bv,bw] using Fin.lt_def.mp lt)

theorem stream_mem (n key : ℕ) (side : Bool) (i : Port r p) :
    i∈stream u n key side ↔ i.1∈sites u key side ∧ ∃v,peer u i.1 i.2=some v ∧ bin u v i.1<n := by
  cases side with
  | false=>simp only [stream,Bool.false_eq_true,ite_false,thinStream,List.mem_flatMap,in_mem];aesop
  | true=>
    simp only [stream,ite_true,thickStream,List.mem_flatMap,List.mem_finRange,true_and,thick_mem]
    constructor
    · rintro ⟨b,in_,v,peer_,eqn⟩;exact ⟨in_,v,peer_,by simpa only [eqn] using b.isLt⟩
    · rintro ⟨in_,v,peer_,room⟩;exact ⟨⟨_,room⟩,in_,v,peer_,rfl⟩


end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
