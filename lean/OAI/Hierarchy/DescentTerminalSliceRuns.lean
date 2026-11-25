import OAI.Hierarchy.DescentBundleScalar

namespace OAI
/-! # Recovering actual affine slices from the per-reference occurrence fields -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentBundleHistory
noncomputable section

def whole : SliceCode := ⟨0,1,1⟩
def repeatFields (codes:List SliceCode) : List SliceCode :=
  codes.flatMap fun c=>List.replicate c.count c

/-- At the first word of a slice the retained count says exactly where the
next one begins, including when both slices have the same three digits. -/
def peel : ℕ→List SliceCode→List SliceCode
  | 0,_=>[]
  | _+1,[]=>[]
  | fuel+1,c::cs=>c::peel fuel (cs.drop (c.count-1))

theorem peel_exact (codes:List SliceCode) (positive:∀c∈codes,0<c.count)
    (fuel:ℕ) (enough:codes.length≤fuel) :
    peel fuel (repeatFields codes)=codes := by
  induction codes generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons c cs ih =>
    have nz:=positive c List.mem_cons_self
    obtain ⟨h,eq⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt nz)
    cases fuel with
    | zero=>simp at enough
    | succ fuel=>
      have suffix : ((List.replicate h c)++repeatFields cs).drop h=repeatFields cs:=by
        simp
      have keep:=ih (fun d hd=>positive d (List.mem_cons_of_mem _ hd)) fuel (by simpa using enough)
      change peel (fuel+1) (List.replicate c.count c++repeatFields cs)=c::cs
      rw [eq,List.replicate_succ]
      change c::peel fuel (((List.replicate h c)++repeatFields cs).drop (c.count-1))=c::cs
      rw [eq,Nat.succ_sub_one,suffix,keep]

theorem length_le (codes:List SliceCode) (positive:∀c∈codes,0<c.count) :
    codes.length≤(repeatFields codes).length := by
  induction codes with
  | nil=>simp [repeatFields]
  | cons c cs ih=>
    have hc:=positive c List.mem_cons_self
    have hs:=ih (fun d hd=>positive d (List.mem_cons_of_mem _ hd))
    change _≤(List.replicate c.count c++repeatFields cs).length
    simp only [List.length_cons,List.length_append,List.length_replicate]
    omega

inductive Layout where
  | seed (units:ℕ)
  | ordinary (rows:List (List SliceCode))
  | relay
  | rotor

/-- The four alternatives are distinguished by the genuinely stored disjoint
primitive tag. All rotor operands have a single nonempty affine slice. -/
def Layout.correct (kind:Layout) (rows:List (List SliceCode)) : Prop :=
  match kind with
  | .seed units=>0<units ∧ ∃a,rows=List.replicate a (List.replicate units whole)
  | .ordinary chosen=>rows=chosen
  | .relay=>∃v,rows=List.replicate 2 (List.replicate v whole)
  | .rotor=>∃c:List SliceCode,rows=c.map fun z=>[z]

def Layout.restore (kind:Layout) (words:List SliceCode) : List (List SliceCode) :=
  match kind with
  | .seed units=>List.replicate (words.length/units) (List.replicate units whole)
  | .ordinary chosen=>chosen
  | .relay=>List.replicate 2 (List.replicate (words.length/2) whole)
  | .rotor=>(peel words.length words).map fun c=>[c]

private theorem length_whole (a u:ℕ) :
    (repeatFields (List.replicate a (List.replicate u whole)).flatten).length=a*u := by
  simp [repeatFields,whole,List.flatten_replicate_replicate,List.flatMap_replicate]

private theorem singletons (xs:List SliceCode) : (xs.map (fun z=>[z])).flatten=xs := by
  induction xs <;> simp_all

theorem Layout.restore_correct (kind:Layout) (rows:List (List SliceCode)) (shape:kind.correct rows)
    (live:∀c∈rows.flatten,0<c.count) :
    kind.restore (repeatFields rows.flatten)=rows := by
  cases kind with
  | seed n=>
    obtain ⟨good,a,rfl⟩:=shape
    rw [Layout.restore,length_whole,Nat.mul_div_cancel _ good]
  | ordinary sel=>exact shape.symm
  | relay=>
    obtain ⟨a,rfl⟩:=shape
    rw [Layout.restore,length_whole,Nat.mul_comm 2 a,Nat.mul_div_cancel _ (by decide : 0<2)]
  | rotor=>
    obtain ⟨cs,rfl⟩:=shape
    rw [singletons] at live
    simp only [Layout.restore,singletons,peel_exact cs live _ (length_le cs live)]

/-- Seed and relay rows depend only on their number of live words. Ordinary
gadget rows use their complete recorded primitive specification. -/
theorem Layout.restore_of_observations (kind:Layout) (rows:List (List SliceCode)) (words:List SliceCode)
    (shape:kind.correct rows) (live:∀c∈rows.flatten,0<c.count)
    (amount:words.length=(repeatFields rows.flatten).length)
    (rotor:kind=.rotor→words=repeatFields rows.flatten) :
    kind.restore words=rows := by
  have canonical:=kind.restore_correct rows shape live
  cases kind with
  | seed n=>simpa only [Layout.restore,amount] using canonical
  | ordinary chosen=>exact canonical
  | relay=>simpa only [Layout.restore,amount] using canonical
  | rotor=>rw [rotor rfl];exact canonical

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
