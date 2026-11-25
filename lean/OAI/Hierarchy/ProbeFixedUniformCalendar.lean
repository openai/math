import OAI.Hierarchy.ProbeFixedUniformMarket
import OAI.Hierarchy.ProbeFixedUniformPost
import OAI.Hierarchy.ProbeFixedUniformCommit
import OAI.Hierarchy.ProtocolRAMCalendarUniformControl

namespace OAI
/-! # Uniform bytecode and running time of the paid wide calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseStage
open scoped Classical

private theorem sum_bound {I : Type*} (es : List I) (f : I→ℕ) (K : ℕ) (cap : ∀e∈es,f e≤K) :
    (es.map f).sum≤es.length*K := by
  induction es with
  | nil => simp
  | cons x xs ih =>
    exact (Nat.add_le_add (cap x (.head _)) (ih (fun a ha=>cap a (.tail _ ha)))).trans_eq (by
      simp [Nat.succ_mul,Nat.add_comm])

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_checked_resources :
    ∃K : ℕ, ∀h width flag : ℕ,
    let P:=v.widePlacement h width
    let C:=v.wideSignedChart h width (v.fixedTerminalStock P h width)
    checkedCost C≤K*2^h ∧ text (checked C flag)≤K := by
  obtain ⟨M,markets⟩:=v.wide_uniform_market
  obtain ⟨P₀,posts⟩:=v.wide_uniform_post
  obtain ⟨S,commits⟩:=v.wide_uniform_commit
  let dates:=(events v.mesh).length
  let bands:=FeedLayout.lanes (publicStages v.W) k
  let G:=11+4*guardWork v.mesh
  let E:=G+M+P₀+S+(15+2*bands*411)+(4+2*bands*208)
  let H:=100+100*dates
  let K:=dates*E+H
  refine ⟨K,?_⟩
  intro h width flag
  let P:=v.widePlacement h width
  let stock:=v.fixedTerminalStock P h width
  let C:=v.wideSignedChart h width stock
  let A:=v.privateArena P h width
  let fmt:=v.nativeFormats P h width
  have pos : 1≤2^h := Nat.one_le_two_pow
  have scale (n : ℕ) : n≤n*2^h := Nat.le_mul_of_pos_right _ pos
  have both (e : Event) (atDate : e∈events v.mesh) : ticks C e≤E*2^h ∧ eventText C e≤E := by
    cases e with
    | attempt a =>
      have g:=guard_resources C a atDate
      have m : (C.frozen a).ticks ≤ M*2^h ∧ text (C.frozen a).native ≤ M :=
        markets h width a atDate
      have s : (C.commit a).ticks ≤ S*2^h ∧ text (C.commit a).native ≤ S :=
        commits h width a atDate
      have p' : postTicks (C.layout a) (repair C a)≤P₀*2^h ∧
          postText (C.layout a) (repair C a)≤P₀ := posts h width _ _ _ _ _ _ a
      have bounds : (guard C a).clock≤G ∧ rowText (guard C a).term≤G := by
        change (guard C a).clock≤11+4*guardWork C.mesh ∧ rowText (guard C a).term≤11+4*guardWork C.mesh
        omega
      have full : G+M+P₀+S≤E := by unfold E; omega
      refine ⟨?_,by change rowText (guard C a).term+_+_+_≤E; omega⟩
      apply le_trans _ (Nat.mul_le_mul_right (2^h) full)
      change (guard C a).clock+((C.frozen a).ticks+(_+(C.commit a).ticks))≤_
      simp only [Nat.add_mul]
      have pre:=bounds.1.trans (scale G)
      omega
    | feed b =>
      let L:=FeedLayout.atEvent (N:=Stages h (2^v.W)) v.mesh A fmt P.joint.initial width v.keepLimit b
      obtain ⟨t,size⟩:=L.resources C b rfl
      have lanes : FeedLayout.lanes (Stages h (2^v.W)) k = bands :=
        congrArg (fun n => FeedLayout.lanes n k) (fixed_stage_count h v.W)
      rw [lanes] at t size
      have tlim : 4+2*bands*208≤E := by unfold E; omega
      have slim : 15+2*bands*411≤E := by unfold E; omega
      exact ⟨t.trans (Nat.mul_le_mul_right _ tlim),size.trans slim⟩
  have tb:=sum_bound (events C.mesh) (ticks C) (E*2^h) (fun e he=>(both e he).1)
  have sb:=sum_bound (events C.mesh) (eventText C) E (fun e he=>(both e he).2)
  have ht:=history_work C (events C.mesh)
  change (historyFlag C (events C.mesh)).work≤1+9*dates at ht
  change _≤dates*(E*2^h) at tb
  change _≤dates*E at sb
  have endCost : 4+(4+1*(2*(historyFlag C (events C.mesh)).work+4))≤H := by unfold H; omega
  have endSize : 15+rowText (historyFlag C (events C.mesh))≤H := by unfold H rowText; omega
  change checkedCost C ≤ K*2^h ∧ text (checked C flag) ≤ K
  constructor
  · change (((events C.mesh).map (ticks C)).sum+4)+(4+1*(2*(historyFlag C (events C.mesh)).work+4))≤K*2^h
    have suffix:=endCost.trans (scale H)
    dsimp only [K]
    rw [show (dates*E+H)*2^h=dates*(E*2^h)+H*2^h by ring]
    omega
  · rw [text_checked]
    change 15+((events C.mesh).map (eventText C)).sum+rowText (historyFlag C (events C.mesh))≤dates*E+H
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
