import OAI.Hierarchy.DescentBundleCombine
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.DescentPackedPrivateAliases

namespace OAI
/-! # Relabeling every occupied private word through a genuine bundle contraction -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentLocalPrivateNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {J H A Tag : Type} {B : J→Type} [Fintype J] [Fintype H]
variable {p : ℕ} (hp : 0<p) {w : A→ℕ} {bw : (i:J)→B i→ℕ} (r : ∀i,BitRecipe Tag (B i) (bw i))
variable (hw : H→ℕ) (route : ∀i,BitRef (bw i)→BitRef w⊕BitRef hw)
variable (s : ∀i,Shape p (r i)) (multiple : ∀h,p∣hw h) (f : ∀i,PrivateMap p (bw i) w hw (route i))
local notation "C" => combined r hw route s multiple f
local notation "oldRecipe" i => (s i).recipe hp
local notation "newRecipe" => (C).recipe hp

/-- Each original node retains exactly the same ordered list of operand slots. -/
theorem combined_keys (i : J) (u : (r i).Node) :
    (C).keys ⟨i,u⟩=((s i).keys u).map (destination r hw route f i) := by
  simp [Shape.keys,Shape.rows,combined,Slice.names,Slice.map,List.map_flatMap,List.map_ofFn,Function.comp_def]
  simp only [List.flatMap_def, List.map_ofFn, Slice.names, Function.comp_def]
  rfl

private theorem combined_arity (i : J) (u : (r i).Node) :
    (newRecipe).arity ⟨i,u⟩ = (oldRecipe i).arity u :=
  (congrArg List.length (combined_keys r hw route s multiple f i u)).trans
    (List.length_map (as := (s i).keys u) (destination r hw route f i))

/-- A public operand can become private. An inherited private operand remains
attached to its unique donor and original word index. -/
def wordTransfer (i : J) : BlockRef p (bw i)⊕Private (r i) p →
    BlockRef p w ⊕ Private (BitRecipe.combineBits r hw route) p
  | .inr ⟨h,j⟩=>.inr ⟨.inr ⟨i,h⟩,j⟩
  | .inl b=>((f i).map b).map id (fun t=>⟨.inl t.port,⟨t.block,(Nat.le_div_iff_mul_le hp).mpr t.fits⟩⟩)

theorem wordTransfer_read (i : J) (u : (r i).Node) (j : Fin ((oldRecipe i).arity u)) :
    let arity : (newRecipe).arity ⟨i,u⟩=(oldRecipe i).arity u:=by
      exact combined_arity hp r hw route s multiple f i u
    (newRecipe).operand ⟨i,u⟩ (Fin.cast arity.symm j)=wordTransfer hp r hw route f i ((oldRecipe i).operand u j) := by
  intro arity
  have original : j.val < ((s i).keys u).length := j.isLt
  have moved : j.val < ((C).keys ⟨i,u⟩).length := (Fin.cast arity.symm j).isLt
  have cell : ((C).keys ⟨i,u⟩)[j.val]'moved =
      destination r hw route f i (((s i).keys u)[j.val]'original) :=
    (getElem_congr (combined_keys r hw route s multiple f i u) (rfl : j.val = j.val) moved).trans
      (List.getElem_map (destination r hw route f i))
  refine (congrArg (Sum.map id (privateIndex hp)) cell).trans ?_
  change (destination r hw route f i ((s i).keys u)[j.val]).map id (privateIndex hp)=
    wordTransfer hp r hw route f i (((s i).keys u)[j.val].map id (privateIndex hp))
  cases ((s i).keys u)[j.val] with
  | inr h=>rfl
  | inl b=>cases h : (f i).map b <;> simp [destination,wordTransfer,h,liftNew] <;> rfl

def oldWord (i : J) (t : Private (r i) p) : Private (BitRecipe.combineBits r hw route) p :=
  ⟨.inr ⟨i,t.1⟩,t.2⟩

/-- A private word used after transfer in the inherited band had a real
operand occurrence already at its unique previous site. -/
theorem inherited_used (i : J) (t : Private (r i) p) :
    (newRecipe).Used (oldWord r hw route i t) ↔ (oldRecipe i).Used t := by
  constructor
  · rintro ⟨⟨i',u⟩,j,h⟩
    have len : (newRecipe).arity ⟨i',u⟩=(oldRecipe i').arity u :=by
      exact combined_arity hp r hw route s multiple f i' u
    let k:=Fin.cast len j
    have transfer : Sum.inr (oldWord r hw route i t) =
        wordTransfer hp r hw route f i' ((oldRecipe i').operand u k) :=
      h.symm.trans (wordTransfer_read hp r hw route s multiple f i' u k)
    cases ref : (oldRecipe i').operand u k with
    | inl b=>
      cases place : (f i').map b with
      | inl a=>simp [ref,wordTransfer,place] at transfer
      | inr q=>
        simp [ref,wordTransfer,place,oldWord] at transfer
        have clash := congrArg Sigma.fst transfer
        cases clash
    | inr a=>
      rcases a with ⟨h',t'⟩
      have same : oldWord r hw route i t = oldWord r hw route i' ⟨h',t'⟩ :=
        Sum.inr.inj (transfer.trans (congrArg (wordTransfer hp r hw route f i') ref))
      rcases t with ⟨h,t⟩
      cases same
      exact ⟨u,k,ref⟩
  · rintro ⟨u,k,h⟩
    rcases t with ⟨old,index⟩
    refine ⟨⟨i,u⟩, Fin.cast (combined_arity hp r hw route s multiple f i u).symm k, ?_⟩
    calc
      _ = wordTransfer hp r hw route f i ((oldRecipe i).operand u k) :=
        wordTransfer_read hp r hw route s multiple f i u k
      _ = _ := congrArg (wordTransfer hp r hw route f i) h

abbrev BornWord := Σh : H,Fin (hw h/p)

/-- Semantic inverse of the two printed private-name bands. Only old words
actually used have to carry an old local alias. -/
def liveSource (v : (newRecipe).UsedWord) :
    BornWord (p:=p) hw ⊕ (Σi,(oldRecipe i).UsedWord) := by
  rcases v with ⟨⟨h|⟨i,h⟩,j⟩,appears⟩
  · exact .inl ⟨h,j⟩
  · exact .inr ⟨i,⟨⟨h,j⟩,(inherited_used hp r hw route s multiple f i ⟨h,j⟩).mp appears⟩⟩

def forgetSource : BornWord (p:=p) hw ⊕ (Σi,(oldRecipe i).UsedWord) →
    Private (BitRecipe.combineBits r hw route) p
  | .inl ⟨h,j⟩=>⟨.inl h,j⟩
  | .inr ⟨i,t⟩=>oldWord r hw route i t.val

theorem liveSource_injective : Function.Injective (liveSource hp r hw route s multiple f) := by
  have inverse (t : (newRecipe).UsedWord) :
      forgetSource hp r hw route s (liveSource hp r hw route s multiple f t)=t.val := by
    rcases t with ⟨⟨h|⟨i,h⟩,j⟩,appears⟩ <;> rfl
  intro a b eqn
  exact Subtype.ext ((inverse a).symm.trans ((congrArg _ eqn).trans (inverse b)))

/-- The first band is a locally identified captured cable and chunk. The
second band contains a donor position and its earliest previous operand.
Both codes use only current local fields. -/
def liveTag {n D K : ℕ} (name : BornWord (p:=p) hw↪Fin n) (donor : J↪Fin D)
    (slot : ∀i,Slot (oldRecipe i)↪Fin K) : (newRecipe).UsedWord ↪ Fin (n+D*K) where
  toFun x:=finSumFinEquiv ((liveSource hp r hw route s multiple f x).elim
    (Sum.inl ∘ name) (fun u=>Sum.inr (finProdFinEquiv (donor u.1,firstAlias _ (slot u.1) u.2))))
  inj' := by
    intro a b eqn
    apply liveSource_injective hp r hw route s multiple f
    have h:=finSumFinEquiv.injective eqn
    cases ha : liveSource hp r hw route s multiple f a with
    | inl x=>
      cases hb : liveSource hp r hw route s multiple f b with
      | inl y=>exact congrArg Sum.inl (name.injective (by simpa [ha,hb] using h))
      | inr y=>simp [ha,hb] at h
    | inr x=>
      cases hb : liveSource hp r hw route s multiple f b with
      | inl y=>simp [ha,hb] at h
      | inr y=>
        have eqn:=finProdFinEquiv.injective (Sum.inr.inj (by simpa only [ha,hb,Sum.elim_inr] using h))
        obtain ⟨i,x⟩:=x
        obtain ⟨j,y⟩:=y
        obtain rfl:=donor.injective (congrArg Prod.fst eqn)
        exact congrArg (fun a=>(Sum.inr ⟨i,a⟩ : BornWord (p:=p) hw ⊕ (Σi,(oldRecipe i).UsedWord)))
          ((firstAlias _ (slot i)).injective (congrArg Prod.snd eqn))

end
end Hierarchy.DescentBundleHistory

end OAI
