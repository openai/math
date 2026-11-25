import OAI.Hierarchy.DescentFallbackPeriodInputs

namespace OAI
/-! # A physical stencil scan determines fallback ticket occupancy at every old host -/
namespace Hierarchy.DescentResetHostSize
open DescentHostDirectory

theorem code_bounds {r : ℕ} (i : Code r) : i.val.1≤r ∧ i.val.2<2^i.val.1 := by
  have aux (r : ℕ) (z : ℕ×ℕ) (member : z∈codes r) : z.1≤r ∧ z.2<2^z.1 := by
    induction r with
    | zero=>have eq : z=(0,0):=by simpa [codes] using member
            subst z
            decide
    | succ r ih=>
      rcases Finset.mem_union.mp member with prev|top
      · have h:=ih prev
        exact ⟨h.1.trans (Nat.le_succ _),h.2⟩
      · obtain ⟨j,jlt,rfl⟩:=Finset.mem_image.mp top
        exact ⟨le_rfl,Finset.mem_range.mp jlt⟩
  exact aux r i.val i.property
end Hierarchy.DescentResetHostSize

namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentColonies DescentGL DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open DescentChosenRouter DescentRelativeContacts DescentContacts DescentResetHostSize DescentFallbackShapeTable
open scoped Classical
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool} (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ) (wt : V→Block k→ℕ)
    (flow : V→V→Block k→ℝ) (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "c" => T.commonDepth
local notation "Y" => (2^Z.n:ℕ)
local notation "r" => Z.k-c
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
local notation "b" => fun v=>Z.placement.b (frame.host v)
set_option quotPrecheck false in
local notation "safe" => roster.2.2.2.2.2.choose
local notation "ep" => endpoint near b frame.basis wt f (32*Nat.clog 2 (2*Δ)) B g Y safe
  (fun v j=>(frame.host v,j)∈Z.placement.keys) hub
local notation "μ" => rearrange frame.basis

include roster in
theorem measured_presence (v : V) (hi : Block c) (ticket : Code r×Option (Fin Y))
    (source : Block (k-c)→ℕ) (stencil : ∀lo,
      source lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v ((μ).symm (join fit hi lo))))) :
    (∃t : Z.Fallback,(T.code t).1=frame.host v ∧ Z.rootBlock T (.inr t)=hi ∧ Z.rootTicket T (.inr t)=.inr ticket) ↔
    ∃lo,source lo/2=DescentFallbackPeriod.rootCell r Z.n ticket := by
  rw [frame.root_presence vertex near n f B wire K Δ wt flow roster]
  apply exists_congr
  intro lo
  let x:=(μ).symm (join fit hi lo)
  obtain ⟨z,_,label⟩:=frame.each_label vertex near n f B wire K Δ wt flow roster v x
  let name:=(shortName c (T.code z)).2
  have fieldEq : fieldsRelative c (ep v x)=DescentPlainTerminal.fields name := by rw [←label,←fields_relative]
  have depth := Nat.sub_le_sub_right (T.codeLegal z).2.1 c
  have index : name.1.2<2^name.1.1:=Nat.mod_lt _ (Nat.two_pow_pos _)
  have lim:=code_bounds ticket.1
  have poweq : k-c=r:=by rw [frame.extent]
  have sourceEq : source lo/2=cell r name:=by
    rw [stencil,←show x=(μ).symm (join fit hi lo) from rfl,fieldEq,poweq,Stencil.shapeCode_fields]
  change fieldsRelative c (ep v x) = DescentPlainTerminal.fields (ticket.1.val,ticket.2) ↔ _
  rw [fieldEq,sourceEq]
  constructor
  · intro same
    exact (Stencil.shapeCode_fields r name).symm.trans
      ((congrArg (Stencil.shapeCode r Y) same).trans (Stencil.shapeCode_fields r (ticket.1.val,ticket.2)))
  · intro same
    have inj:=congrArg (decode r Y) same
    rw [decode_cell r name depth index,DescentFallbackPeriod.rootCell,decode_cell r _ lim.1 lim.2] at inj
    exact congrArg DescentPlainTerminal.fields inj

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
