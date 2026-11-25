import OAI.Hierarchy.DescentDatedMeasuredTicketRows
import OAI.Hierarchy.DescentDatedTicketResolve

namespace OAI
/-! The fragment read from the normalized source bank equals the mathematical
ticket resolver on the eight measured ticket digits and the earlier four header words. -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentOperandStateBanks DescentPackedOperand DescentSIMDLookup DescentDatedOperandCoordinates
open scoped Classical Fin.CommRing
noncomputable section
variable (l:Layout) (old:Books l) (typed:BookPointers old)
    (digits:Fin l.jobs→Fin l.hosts→Fin l.groups→Fin 8→ℕ) (grain:Cell (l.size+2))
variable (room : ∀ (j : Fin l.jobs) (h : Fin l.hosts) (g : Fin l.groups),
    11*(measuredRoles l digits j 1 h g).val + (measuredRoles l digits j 2 h g).val<2^(l.size+2))

theorem source_compiled (j:Fin l.jobs) (h:Fin l.hosts) (g:Fin l.groups) (p:Pointer)
    (read:∀f,(booksHeader old j h g f).val=p.header f)
    (flags:Ticket.Flags (digits j h g)) :
    (ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j).compiled h g=Ticket.compiled (digits j h g) grain p
      (fun f=>(read f).ge.trans_lt (booksHeader old j h g f).isLt) := by
  let y:=digits j h g
  have flag (i:Fin 8) (hi:y i≤1) : decide (y i=1)=decide (y i≠0) :=by
    by_cases zero : y i=0
    · simp [zero]
    · have one : y i=1:=by omega
      simp [one]
  have sideEq:DescentDatedPublicGrain.withGrain grain (Ticket.recordedSide l.size y)=Ticket.side y grain :=by
    simp only [DescentDatedPublicGrain.withGrain,Ticket.recordedSide,Ticket.side,flag 1 flags.first,
      flag 2 flags.second,flag 3 flags.marked]
  let cap:=2^(l.size+2)
  have count : 11*(y 6%cap)+(y 7%cap)<cap:=room j h g
  have scalar : DescentPackedRawTicket.payload (measuredRoles l digits j 1) (measuredRoles l digits j 2) (room j) h g=
      ((11*y 6+y 7:ℕ):Cell (l.size+2)) := by
    apply Fin.ext
    change 11*(y 6%cap)+(y 7%cap)=(11*y 6+y 7)%cap
    exact (Nat.mod_eq_of_lt count).symm.trans
      (((Nat.mod_modEq (y 6) cap).mul_left 11).add (Nat.mod_modEq (y 7) cap))
  let src:=ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j
  have ptr : src.pointer h g=p:=decode_of_pointer read
  cases ptr
  exact congrArg₂ (fun (s : DescentPriorOperandColumns.Side l.size) (n : Cell (l.size+2))=>
    DescentOrdinaryLocalFragment.route (s.withHeader (src.pointer h g) (src.size h g))
      (y 5:Cell (l.size+2)) n) sideEq scalar

/-- The actual normalized dictionary entry of a retained original pin
uses both earlier numerical fields even when its index is zero. -/
theorem source_pin (j:Fin l.jobs) (h:Fin l.hosts) (g:Fin l.groups) (port piece:ℕ)
    (read:∀f,(booksHeader old j h g f).val=(Pointer.pin port piece).header f) :
    resolve ((ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j).compiled h g)=.pin port piece := by
  have ptr : (ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j).pointer h g=.pin port piece:=decode_of_pointer read
  have bounded (f:Fin 4) : (Pointer.pin port piece).header f<2^(l.size+2):=
    (read f).ge.trans_lt (booksHeader old j h g f).isLt
  have portRoom:port<2^(l.size+2):=bounded 2
  have pieceRoom:piece<2^(l.size+2):=bounded 3
  let src:=ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j
  have routed (p:Pointer) (size:∀f,p.header f<2^(l.size+2)) (eqn:p=.pin port piece) :
      resolve (DescentOrdinaryLocalFragment.route ((src.side h g).withHeader p size)
        (src.routed 0 h g) (DescentPackedRawTicket.payload (src.routed 1) (src.routed 2) src.noCarry h g))=
        .pin port piece :=by
    subst p
    simp [DescentOrdinaryLocalFragment.route,DescentPriorOperandColumns.Side.withHeader,
      resolve,Pointer.header]
  exact routed _ _ ptr

theorem source_carried (j:Fin l.jobs) (h:Fin l.hosts) (g:Fin l.groups) («alias» donor:ℕ)
    (read:∀f,(booksHeader old j h g f).val=(Pointer.privateWord «alias»).header f)
    (measured:digits j h g 0=donor) (roomDonor:donor<2^(l.size+2)) :
    resolve ((ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j).compiled h g)=.carried donor «alias» := by
  let src:=ofBooks old typed (measuredSides l digits grain) (measuredRoles l digits) room j
  have ptr : src.pointer h g=.privateWord «alias»:=decode_of_pointer read
  have aliasRoom:«alias»<2^(l.size+2):=(read 2).ge.trans_lt (booksHeader old j h g 2).isLt
  have sourceDonor:(src.side h g).donor.val=donor:=by
    change (digits j h g 0)%2^(l.size+2)=donor
    rw [measured,Nat.mod_eq_of_lt roomDonor]
  have routed (p:Pointer) (size:∀f,p.header f<2^(l.size+2)) (eqn:p=.privateWord «alias») :
      resolve (DescentOrdinaryLocalFragment.route ((src.side h g).withHeader p size)
        (src.routed 0 h g) (DescentPackedRawTicket.payload (src.routed 1) (src.routed 2) src.noCarry h g))=
        .carried donor «alias» :=by
    subst p
    simp [DescentOrdinaryLocalFragment.route,DescentPriorOperandColumns.Side.withHeader,
      resolve,Pointer.header,sourceDonor]
  exact routed _ _ ptr

end
end Hierarchy.DescentDatedPriorOperand

end OAI
