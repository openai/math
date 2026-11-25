import OAI.Hierarchy.DescentParallelIncidentPosition
import OAI.Hierarchy.DescentPackedOperandPublic

namespace OAI
/-! # A complete bijection from signed normalized-parent offsets to real local ports -/
namespace Hierarchy.DescentParallelBase.GrainPorts
open DescentSixParty DescentSharedCableNames DescentColonies DescentHostDirectory
open scoped Classical
noncomputable section
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype E]
  {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
local notation "B" => Stage.source A native
local notation "stream" => Stage.stream A native
variable (C : Blocks (Stage.source A native) E) (h : Stage.Host J V k)

/-- Two roles are present for a loop and one role at each end for an
ordinary nonloop. No sign duplicates a normalized child offset. -/
abbrev Unit := {t : (Σe,Fin (C.count e))×Bool // (if t.2 then C.dst t.1.1 else C.src t.1.1)=h}

local notation "ports" => GroupStage.CellPorts A (Prod.fst (Prod.fst h)) (Prod.snd (Prod.fst h)) (Prod.snd h)

def grain (t : GrainPorts.Unit A native C h) :=(stream).symm (C.order t.val.1)

omit [Fintype E] in
theorem source (t : GrainPorts.Unit A native C h) (left:t.val.2=false) : Stage.home A (W.graph.src (grain A native C h t).1)=h:=by
  have end_:=C.atSource t.val.1.1 t.val.1.2
  have here:=t.property;rw [left] at here;exact end_.trans here

omit [Fintype E] in
theorem target (t : GrainPorts.Unit A native C h) (right:t.val.2=true) : Stage.home A (W.graph.dst (grain A native C h t).1)=h:=by
  have end_:=C.atTarget t.val.1.1 t.val.1.2
  have here:=t.property;rw [right] at here;exact end_.trans here

def port (t : GrainPorts.Unit A native C h) : ports :=
  let a:=grain A native C h t
  if yes:t.val.2=true then
    let ht:=target A native C h t yes
    .inr ⟨⟨a.1,congrArg Prod.fst ht,congrArg Prod.snd ht⟩,a.2⟩
  else
    let hs:=source A native C h t (Bool.eq_false_iff.mpr yes)
    .inl ⟨⟨a.1,congrArg Prod.fst hs,congrArg Prod.snd hs⟩,a.2⟩

def sign : ports→Bool :=Sum.elim (fun _=>false) (fun _=>true)

omit [Fintype E] in
theorem value (t : GrainPorts.Unit A native C h) : Stage.recover A h (port A native C h t)=grain A native C h t ∧ sign A h (port A native C h t)=t.val.2:=by
  cases s:t.val.2 <;> simp [port,s,Stage.recover,sign]

theorem sign_injective (a b : ports) (same : Stage.recover A h a=Stage.recover A h b) (signed : sign A h a=sign A h b) : a=b:=by
  rcases a with ⟨a,i⟩|⟨a,i⟩ <;> rcases b with ⟨b,j⟩|⟨b,j⟩ <;> simp [sign] at signed ⊢
  all_goals
    obtain ⟨a,ha⟩:=a;obtain ⟨b,hb⟩:=b
    have edge:=congrArg Sigma.fst same;change a=b at edge;subst b
    have eqn:i=j:=eq_of_heq (Sigma.ext_iff.mp same).2
    subst j
    exact ⟨rfl, HEq.rfl⟩

def unit (b : ports) : GrainPorts.Unit A native C h :=
  let raw:=Stage.recover A h b
  let i:=C.order.symm (stream raw)
  ⟨(i,sign A h b),by
    cases b with
    | inl b=>
      obtain ⟨⟨u,site_⟩,j⟩:=b
      have ends:=C.atSource i.1 i.2
      rw [show C.order ⟨i.1,i.2⟩=stream raw from C.order.apply_symm_apply _] at ends
      change C.src i.1=h;rw [←ends];change Stage.home A (W.graph.src (((stream).symm (stream raw)).1))=h
      rw [Equiv.symm_apply_apply];exact Prod.ext site_.1 site_.2
    | inr b=>
      obtain ⟨⟨u,site_⟩,j⟩:=b
      have ends:=C.atTarget i.1 i.2
      rw [show C.order ⟨i.1,i.2⟩=stream raw from C.order.apply_symm_apply _] at ends
      change C.dst i.1=h;rw [←ends];change Stage.home A (W.graph.dst (((stream).symm (stream raw)).1))=h
      rw [Equiv.symm_apply_apply];exact Prod.ext site_.1 site_.2⟩

def equiv : GrainPorts.Unit A native C h≃ports where
  toFun:=port A native C h
  invFun:=unit A native C h
  left_inv t:=by
    apply Subtype.ext;apply Prod.ext
    · change C.order.symm (stream (Stage.recover A h (port A native C h t)))=t.val.1
      rw [(value A native C h t).1];simp [grain]
    · exact (value A native C h t).2
  right_inv p:=by
    apply sign_injective A h
    · rw [(value A native C h _).1];simp [grain,unit]
    · exact (value A native C h _).2

variable {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ)

private theorem same_read (h₁ h₂ : Stage.Host J V k) (same:h₁=h₂)
    (p : A.CellPorts h₁.1.1 h₁.1.2 h₁.2) (q : A.CellPorts h₂.1.1 h₂.1.2 h₂.2)
    (one:Stage.recover A h₁ p=Stage.recover A h₂ q) (sg:sign A h₁ p=sign A h₂ q) :
    Stage.live A native S ready names h₁ p=Stage.live A native S ready names h₂ q:=by
  subst h₂;rw [sign_injective A h₁ p q one sg]

omit [Fintype E] in
/-- Read the actual physical port at its source or target, including both
possible observations when its source and target coordinates coincide. -/
theorem at_end (t:GrainPorts.Unit A native C h) :
    Stage.live A native S ready names h (port A native C h t)=
      DescentPackedOperand.Public.endpoint A native S ready names t.val.2 (grain A native C h t):=by
  cases test:t.val.2 with
  | false=>
    change _=Stage.live A native S ready names _ (Exchange.sourcePort A _)
    apply same_read A native S ready names _ _ (source A native C h t test).symm
    · exact (value A native C h t).1
    · exact (value A native C h t).2.trans test
  | true=>
    change _=Stage.live A native S ready names _ (Exchange.targetPort A _)
    apply same_read A native S ready names _ _ (target A native C h t test).symm
    · exact (value A native C h t).1
    · exact (value A native C h t).2.trans test

omit [Fintype E] in
theorem address (t:GrainPorts.Unit A native C h) :
    let f:Local C h:=⟨t.val.1.1,Nat.zero_lt_of_lt t.val.1.2.isLt,by
      have ht:=t.property;cases test:t.val.2 <;> simp [test] at ht <;> tauto⟩
    (Stage.signed A native S ready h.1 h.2 (port A native C h t)).val=
    t.val.2.toNat*A.cap+((B).position (Stage.measured A native S ready) h (Incidence.candidate C h f ⟨0,f.property.1⟩)).val+t.val.1.2.val:=by
  intro f
  have edgeEq : Stage.ofPort A native h (port A native C h t)=Incidence.candidate C h f t.val.1.2:=by
    have index (p : ports) : (Stage.ofPort A native h p).val = stream (Stage.recover A h p) := by
      cases p <;> rfl
    apply Subtype.ext
    rw [index]
    change stream (Stage.recover A h (port A native C h t))=C.order t.val.1
    rw [(value A native C h t).1];simp [grain]
  have signEq : (Stage.signedBit A h (port A native C h t)).val=t.val.2.toNat:=by
    cases e:t.val.2 <;> simp [port,e,Stage.signedBit]
  change (finProdFinEquiv (Stage.signedBit A h (port A native C h t),(B).position _ h _)).val=_
  rw [finProdFinEquiv_apply_val,edgeEq,Incidence.child C h _ f _,signEq];ring

end
end Hierarchy.DescentParallelBase.GrainPorts

end OAI
