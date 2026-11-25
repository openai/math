import OAI.Hierarchy.DescentRawFieldOps
import OAI.Hierarchy.DescentOrdinaryTarget
import OAI.Hierarchy.DescentRecordedBranch

namespace OAI
/-! # Every original cable, new demand arm and new supply cable before contraction -/

namespace Hierarchy.DescentOrdinaryRawRows
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentSixParty GadgetNetwork Computability.BorderVNP.Crossing DescentOrdinaryDestRAM
open scoped Fin.CommRing Classical
noncomputable section
def Born.edge {I P : Type} {d : ℕ} {bits : P→ℕ} (N : Network d P bits) (i : I) : Born→GadgetNetwork.Edge (I:=I) N
  | .arm s=>.inr (.inl (i,s))
  | .supply s=>.inr (.inr (i,s))

variable {F P : Type} [Field F] {I : Type} [Fintype I] [DecidableEq I] {d w n : ℕ} {bits : P→ℕ}
variable (N : Network d P bits) (G : PoweredGadget F) (S : Sources)
variable (pick : I×Fin 2↪N.Edge) (z : ℕ) (profile : I→Profile G.C)
variable (owner : GadgetNetwork.Site (I:=I) N→ℕ)
variable (edge : N.Edge≃Fin (Fintype.card N.Edge)) (site : N.Site↪ℕ) (active : Finset N.Edge)

def marked : GadgetNetwork.Edge (I:=I) N→Bool
  | .inl e=>decide (e∈active)
  | .inr _=>true

def repeats : GadgetNetwork.Edge (I:=I) N→ℕ
  | .inl e=>if e∈active then G.b else 1
  | .inr (.inl _)=>G.b
  | .inr (.inr (i,s))=>((profile i).1 s).val+G.k

def truth (f : Column) (e : GadgetNetwork.Edge (I:=I) N) : ℕ := match f with
  | .src=>owner (GadgetNetwork.source N e)
  | .dst=>owner (GadgetNetwork.target N pick e)
  | .width=>GadgetNetwork.width N pick (branchWidth G (fun _=>z) profile) e
  | .core=>(marked N active e).toNat
  | .repeats=>repeats N G profile active e

/-- These immutable input words are shared with the authentic pair and venue publishers.
The window reports every real field, raw or selected, including a deleted inner wire. -/
structure Inputs (pair : I≃Fin n) (code : I→ℕ) (m : Memory w) : Prop where
  oldSrc : ∀e,S.oldSrc.read m (edge e).val=site (N.src e)
  oldOwner : ∀u,S.oldOwner.read m (site u)=(owner (.inl u):Word w)
  target : ∀e,S.resolvedTarget.read m (edge e).val=(owner (GadgetNetwork.target N pick (.inl e)):Word w)
  oldWidth : ∀e,S.oldWidth.read m (edge e).val=N.width e
  oldMark : ∀e,S.oldMark.read m (edge e).val=(decide (e∈active)).toNat
  births : ∀i j,S.birthOwner.read m (6*(pair i).val+j.val:ℕ)=(owner (.inr (i,j)):Word w)
  picked : ∀i s,S.pair.read m (9*(pair i).val+(1+s.val):ℕ)=(edge (pick (i,s))).val
  endSite : ∀i s,S.pair.read m (9*(pair i).val+(4+2*s.val):ℕ)=site (N.dst (pick (i,s)))
  profile : ∀i,S.pair.read m (9*(pair i).val+8:ℕ)=code i
  widthROM : ∀i s,(S.widthROM s).read m (code i)=
    (branchWidth G (fun _=>z) ‹I → Profile G.C› i s:Word w)
  repeatsROM : ∀i s,(S.multiplicityROM s).read m (code i)=((‹I → Profile G.C› i).1 s).val+G.k

private theorem record_eval (b : Bank) (stride off : ℕ) (m : Memory w) (i : ℕ) :
    (readRecord b stride off .row).eval m i=b.read m (stride*i+off:ℕ) := by
  change b.read m ((times stride .row).eval m i+(off:Word w))=_
  rw [times_eval]
  push_cast
  rfl

variable (pair : I≃Fin n) (code : I→ℕ) (m : Memory w) (data : Inputs N G S pick z profile owner edge site active pair code m)

include data in
omit [DecidableEq I] in
theorem born_values (f : Column) (name : Born) (i : I) :
    (S.born G.b name f).eval m (pair i).val=(truth N G pick z profile owner active f (name.edge N i):Word w) := by
  cases name with
  | arm s=>
    cases f <;> simp [born,bornRead,pairRead,record_eval,Born.edge,truth,source,target,width,
      marked,repeats,Expr.eval]
    · simpa using data.births i (demandDst s)
    · simpa using ((congrArg (S.oldOwner.read m) (data.endSite i s)).trans
        (data.oldOwner (N.dst (pick (i,s)))))
    · simpa using ((congrArg (S.oldWidth.read m) (data.picked i s)).trans
        (data.oldWidth (pick (i,s))))
  | supply s=>
    cases f <;> simp [born,bornRead,pairRead,record_eval,Born.edge,truth,source,target,width,
      marked,repeats,Expr.eval]
    · simpa using data.births i (supplySrc s)
    · simpa using data.births i (supplyDst s)
    · simpa using ((congrArg ((S.widthROM s).read m) (data.profile i)).trans (data.widthROM i s))
    · simpa using ((congrArg ((S.multiplicityROM s).read m) (data.profile i)).trans (data.repeatsROM i s))

include data in
omit [DecidableEq I] in
theorem old_values (bitsRoom : 1<2^w) (f : Column) (e : N.Edge) :
    (S.old G.b f).eval m (edge e).val=(truth N G pick z profile owner active f (.inl e):Word w) := by
  have nz : (1:Word w)≠0 := by
    intro h
    have hn := congrArg Fin.val h
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt bitsRoom] at hn
    exact Nat.one_ne_zero hn
  cases f <;> by_cases yes : e∈active <;> simp [old,truth,marked,repeats,Expr.eval,data.oldSrc,data.oldOwner,
    data.target,data.oldWidth,data.oldMark,yes,DescriptorExpr.Comparison.test,nz,source,width]

omit [Fintype I] [DecidableEq I] in
/-- Every marked surviving cable really has the indicated number of z-wide output pieces. -/
theorem marked_count (uniform : ∀e∈active,N.width e=z*G.b) (fit : ∀i j,N.width (pick (i,j))=z*G.b)
    (e : GadgetNetwork.Edge (I:=I) N) (yes : marked N active e=true) : GadgetNetwork.width N pick (branchWidth G (fun _=>z) profile) e=repeats N G profile active e*z := by
  rcases e with e|⟨i,s⟩|⟨i,j⟩
  · have h : e∈active := by simpa [marked] using yes
    simpa [physical,width,repeats,h,Nat.mul_comm] using uniform e h
  · simpa [physical,width,repeats,Nat.mul_comm] using fit i s
  · simp [width,repeats,branchWidth,Nat.mul_comm]

end
end Hierarchy.DescentOrdinaryRawRows

end OAI
