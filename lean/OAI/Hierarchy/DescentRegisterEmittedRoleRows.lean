import OAI.Hierarchy.DescentRegisterRoleRows

namespace OAI
/-! # The previous native date provides the original role rows at each reset -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)

local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "data" i:arg => Geometry G S b k w i (cursor i)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)

variable (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces b initial (w:=w) i e)

variable (onCut : ∀i,RunTrace.Events traces i→Geometry G S b k w i (calendar (w:=w) traces b initial i)) (c : C)
local notation "t" => traces c

include fixed placed onCut in
omit [Fintype P] in
theorem role_rows_noninitial {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path) (live : 0< i) : (cursor i).ports.RoleRows:=by
  cases p with
  | here=>omega
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick=>
    let e : (t).path.Event age:=.ordinary prev tick suffix joined
    exact role_rows_next traces b initial fixed placed age ⟨c,e⟩
      (onCut age ⟨c,e⟩)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed=>
    let e : (t).path.Event age:=.reset prev closed suffix joined
    exact role_rows_next traces b initial fixed placed age ⟨c,e⟩
      (onCut age ⟨c,e⟩)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
