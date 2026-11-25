import OAI.Hierarchy.DescentResetContactFactor
import OAI.Hierarchy.DescentDatedCanonicalFront

namespace OAI
/-! # The original public capacity and old-block window pay both contact components -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentContactFieldPolynomial DescentResetLocalRoster DescentCommonHost
open DescentDenseHostOrder DescentCompiler
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
noncomputable section
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d)

def localContactFields (D Ht k cap : ℕ) : Fields :=
  let L:=2^k
  let raw:=DescentRotorWindowArchive.count D L cap
  let half:=L*(2*cap)
  ⟨raw+DescentSharedBookScan.width k (2^n) D,2*(half*3),1+((D*(2*cap))*2+D*D),
   half*2,D,DescentResetSignedHaloMatrix.termWork D,raw,2*(half*2),
   (roster board k Ht).card,2*(rootSlots k (2^n)*(2^n+2^Ht)),2*half⟩

theorem contact_fields_from_calendar (v : ResetOutput) (S : AtomSchedule) (k tail age D f g M next bits «meta» C p : ℕ)
    (calendar : List ℕ)
    (installed : v.front=CandidateFront.setupFront S board k tail age D f g M next bits «meta» C p calendar) :
    v.contactFields=localContactFields board D (GroupStage.depthBound D n f g) k ((calendar.take age).prod*256) := by
  rw [contactFields,installed];rfl

variable {ι : ℕ→Type*} {J : ℕ→ℕ} (D Ht : ℕ)
    {k cap : ∀h,ι h→ℕ}

theorem local_contact_bounds (window : SmallAt J (fun h i=>2^(k h i))) (capacity : SmallAt J cap) :
    Bounds J (fun h i=>localContactFields board D Ht (k h i) (cap h i)) := by
  let c (z : ℕ):=SmallAt.const (ι:=ι) J z
  have depth : SmallAt J k:=window.of_le (fun _ _=>Nat.lt_two_pow_self.le)
  have twice : SmallAt J (fun h i=>2^(k h i+1)):=by
    simpa only [pow_succ] using window.mul (c 2)
  have half:=window.mul ((c 2).mul capacity)
  have raw:=((window.add ((c D).mul window)).add half).add
    ((window.mul window).add ((c D).mul ((c D).mul (c 6))))
  have lines:=((depth.add (c 1)).mul window).mul (c (2^n+1))
  have book:=lines.mul ((c (D+1)).mul lines)
  have shapes : SmallAt J (fun h i=>(roster board (k h i) Ht).card) :=
    ((c (2*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(Ht+1))))).mul twice).of_le
      (fun _ _=>DescentDenseHostOrder.roster_bound ..)
  have roots:=twice.add (twice.mul (c (2^n+1)))
  exact ⟨raw.add book,(c 2).mul (half.mul (c 3)),(c 1).add
    ((((c D).mul ((c 2).mul capacity)).mul (c 2)).add (c (D*D))),half.mul (c 2),
    c D,c (DescentResetSignedHaloMatrix.termWork D),raw,(c 2).mul (half.mul (c 2)),
    shapes,(c 2).mul (roots.mul (c (2^n+2^Ht))),(c 2).mul half⟩

theorem calendar_factor_paid (v : ∀h,ι h→ResetOutput) (U : ∀h,ι h→ℕ)
    (date : ∀h i,(v h i).contactFields=localContactFields board D Ht (k h i) (cap h i))
    (window : SmallAt J (fun h i=>2^(k h i))) (capacity : SmallAt J cap) (work : SmallAt J U) :
    SmallAt J (fun h i=>(v h i).contactFactor (U h i)) := by
  simp only [factor_eq,date]
  exact paid (local_contact_bounds board D Ht window capacity) work

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
