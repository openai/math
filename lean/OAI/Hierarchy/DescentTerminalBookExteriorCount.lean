import OAI.Hierarchy.DescentTerminalBookPeerCounts
import OAI.Hierarchy.DescentTerminalPointerArity
import OAI.Hierarchy.DescentTerminalExteriorHeaders

namespace OAI
/-! # Counting public grains at one physical home from its genuine population and arity words -/
namespace Hierarchy.DescentTerminalLocalPortBook.Board
open DescentSixParty DescentKernelHistory DescentCompiler DescentSharedCableNames DescentColonies
open DescentChosenRouter DescentTerminalGraphRows DescentTerminalPointerDigits Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {F P V : Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k H i p:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (hosts:V↪Fin H) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪ℕ) (names:Stage.Host (Fin groups) V k↪ℕ)
    (coords:Function.Injective (fun s=>(A.pos s,A.block s)))

/-- Those raw fields are already present before the six constant decode tables run. -/
structure Resident (h:Fin H) (board:Board A.degree groups (2^k) A.cap) : Prop where
  active : ∀v:W.graph.Site,hosts (A.pos v).2=h→board.venue (A.pos v).1 (A.block v)=some (arity W.graph p v)
  vacant : ∀g b,(¬∃v:W.graph.Site,hosts (A.pos v).2=h ∧ (A.pos v).1=g ∧ A.block v=b)→board.venue g b=none
  signed : ∀v:W.graph.Site,hosts (A.pos v).2=h→board.ports (A.pos v).1 (A.block v)=Stage.signedPanel A native S ready names (Stage.home A v)

variable (scale «public»:ℕ) (hp:0<p) (whole:A.z*G.b=scale*p) (size:∀z,bits z=«public»*p)
local notation "siteHome" => fun v:W.graph.Site=>hosts (A.pos v).2

include hp size in
omit [Field F] [Fintype P] in
private theorem complete_pins (v:W.graph.Site) (z:Attached W.graph v) : poolBatchCount (bits z.val) p=«public» := by
  have one:=DescentTerminalGraphVolume.exact_pieces p (bits z.val) hp
    (show p∣bits z.val by rw [size];exact dvd_mul_left ..)
  rw [size z.val] at one ⊢
  exact Nat.eq_of_mul_eq_mul_right hp one

include coords hp whole size in
theorem cell_public (h:Fin H) (board:Board A.degree groups (2^k) A.cap)
    (r:Resident (p:=p) A hosts S ready native names h board) (g:Fin groups) (b:Block k) :
    board.exterior scale g b=∑v:W.graph.Site,
      if siteHome v=h ∧ (A.pos v).1=g ∧ A.block v=b then Fintype.card (Attached W.graph v)*«public» else 0 := by
  by_cases exists_:∃v:W.graph.Site,siteHome v=h ∧ (A.pos v).1=g ∧ A.block v=b
  · obtain ⟨v,hv,rfl,rfl⟩:=exists_
    have count:=boundary_count A native S ready names v coords hp scale «public» whole (complete_pins «public» hp size v)
    rw [Finset.sum_eq_single v]
    · simp [exterior,internal,r.active v hv,r.signed v hv,hv,←count]
    · intro u _ nu
      split <;> try rfl
      rename_i eqn
      exact (nu (coords (Prod.ext (Prod.ext eqn.2.1 (hosts.injective (eqn.1.trans hv.symm))) eqn.2.2))).elim
    · simp
  · rw [exterior,r.vacant _ _ exists_]
    simp only [Option.getD_none,Nat.zero_sub]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro v _
    exact ite_eq_right (fun eqn=>exists_ ⟨v,eqn⟩)

include coords hp whole size in
theorem public_count (h:Fin H) (board:Board A.degree groups (2^k) A.cap)
    (r:Resident (p:=p) A hosts S ready native names h board) :
    (∑g,∑b,board.exterior scale g b)=DescentTerminalExteriorHeaders.siteMass W.graph siteHome h/p := by
  let f (g:Fin groups) (b:Block k) (v:W.graph.Site) :=
    if siteHome v=h ∧ (A.pos v).1=g ∧ A.block v=b then Fintype.card (Attached W.graph v)*«public» else 0
  have total : (∑g,∑b,board.exterior scale g b)=∑v:W.graph.Site,if siteHome v=h then Fintype.card (Attached W.graph v)*«public» else 0 := by
    calc
      _=∑g,∑b,∑v,f g b v:=by simp_rw [cell_public A hosts S ready native names coords scale «public» hp whole size h board r];rfl
      _=∑g,∑v,∑b,f g b v:=Finset.sum_congr rfl (fun g _=>Finset.sum_comm)
      _=∑v,∑g,∑b,f g b v:=Finset.sum_comm
      _=_:=by
        apply Finset.sum_congr rfl
        intro v _
        by_cases yes : siteHome v = h
        · have perGroup (g : Fin groups) : (∑ b, f g b v) =
              if (A.pos v).1 = g then Fintype.card (Attached W.graph v)*«public» else 0 := by
            by_cases hg : (A.pos v).1 = g <;> simp [f,yes,hg]
          simp [perGroup,yes]
        · simp [f,yes]
  rw [total]
  have dec : (∑z:P,if siteHome (W.graph.attach z)=h then «public» else 0)=
      ∑v:W.graph.Site,if siteHome v=h then Fintype.card (Attached W.graph v)*«public» else 0 := by
    rw [←Fintype.sum_fiberwise W.graph.attach (fun z=>if siteHome (W.graph.attach z)=h then «public» else 0)]
    apply Finset.sum_congr rfl
    intro v _
    have attached (z : Attached W.graph v) : W.graph.attach z.val = v := z.property
    change (∑ z : Attached W.graph v, if siteHome (W.graph.attach z.val) = h then «public» else 0) = _
    simp only [attached,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    by_cases yes : siteHome v = h <;> simp [yes]
  rw [←dec,DescentTerminalExteriorHeaders.siteMass]
  have factor (z:P):(if siteHome (W.graph.attach z)=h then bits z else 0)=
      (if siteHome (W.graph.attach z)=h then «public» else 0)*p := by split <;> simp_all
  simp only [factor,←Finset.sum_mul,Nat.mul_div_cancel _ hp]

end
end Hierarchy.DescentTerminalLocalPortBook.Board

end OAI
