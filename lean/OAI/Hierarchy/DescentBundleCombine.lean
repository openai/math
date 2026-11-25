import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentBitHistoryCombine

namespace OAI
/-! # Whole-word operands through contraction into a private local label -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {J H A Tag : Type} {B : J→Type} [Fintype J] [Fintype H]
variable {p : ℕ} {w : A→ℕ} {bw : (i:J)→B i→ℕ} (r : ∀i,BitRecipe Tag (B i) (bw i)) (hw : H→ℕ)
variable (route : ∀ i, BitRef (bw i)→BitRef w⊕BitRef hw)

structure PrivateMap (p : ℕ) (w : A→ℕ) {B : Type} (v : B→ℕ) (hw : H→ℕ)
    (route : BitRef w→BitRef v⊕BitRef hw) where
  map : BlockRef p w→BlockRef p v⊕BlockRef p hw
  read : ∀b d,(map b).map (fun t=>t.atBit d) (fun t=>t.atBit d)=route (b.atBit d)

def liftOld (i : J) (b : BlockRef p (r i).hiddenWidth) :
    BlockRef p (BitRecipe.privateWidth r hw) := ⟨.inr ⟨i,b.port⟩,b.block,b.fits⟩

def liftNew (b : BlockRef p hw) : BlockRef p (BitRecipe.privateWidth r hw) :=
  ⟨.inl b.port,b.block,b.fits⟩

def destination (f : ∀i,PrivateMap p (bw i) w hw (route i)) (i : J) :
    BlockRef p (bw i)⊕BlockRef p (r i).hiddenWidth → BlockRef p w⊕BlockRef p (BitRecipe.privateWidth r hw)
  | .inr h=>.inr (liftOld r hw i h)
  | .inl a=>(f i).map a |>.map id (liftNew r hw)

private def bitDestination (i : J) : BitRef (bw i)⊕BitRef (r i).hiddenWidth→
    BitRef w⊕BitRef (BitRecipe.privateWidth r hw)
  | .inr ⟨x,d⟩=>.inr ⟨.inr ⟨i,x⟩,d⟩
  | .inl a=>(route i a).map id (fun b=>⟨.inl b.1,b.2⟩)

omit [Fintype J] [Fintype H] in
private theorem lift_reads (f : ∀i,PrivateMap p (bw i) w hw (route i)) (i : J)
    (a : BlockRef p (bw i)⊕BlockRef p (r i).hiddenWidth) (d : Fin p) :
    (destination r hw route f i a).map (fun b=>b.atBit d) (fun b=>b.atBit d)=
      bitDestination r hw route i (a.map (fun b=>b.atBit d) (fun b=>b.atBit d)) := by
  rcases a with b|h
  · simp only [destination,Sum.map_inl,bitDestination]
    rw [←(f i).read b d]
    cases (f i).map b <;> rfl
  · rfl

private theorem bitDestination_arg (u : Σi,(r i).Node) (j : Fin ((r u.1).arity u.2)) (d : Fin ((r u.1).size u.2 j)) :
    bitDestination r hw route u.1 ((r u.1).arg u.2 j d)=(BitRecipe.combineBits r hw route).arg u j d := by
  rcases u with ⟨i,u⟩
  cases h : (r i).arg u j d with
  | inl a=> cases hh : route i a <;> simp [BitRecipe.combineBits,bitDestination,h,hh]
  | inr a=> rcases a with ⟨q,s⟩;simp [BitRecipe.combineBits,bitDestination,h]

def combined (shape : ∀i,Shape p (r i)) (multiple : ∀h,p∣hw h)
    (f : ∀i,PrivateMap p (bw i) w hw (route i)) : Shape p (BitRecipe.combineBits r hw route) where
  hiddenMultiple h := match h with | .inl v=>multiple v | .inr ⟨i,v⟩=>(shape i).hiddenMultiple v
  groups u := (shape u.1).groups u.2
  size_eq u := (shape u.1).size_eq u.2
  chunk u j g := ((shape u.1).chunk u.2 j g).map (destination r hw route f u.1)
  read u j g d := by
    rcases u with ⟨i,x⟩
    let digit:=Fin.cast ((shape i).size_eq x j).symm (finProdFinEquiv (g,d))
    let part:=(shape i).chunk x j g
    have pass:=lift_reads r hw route f i (part.get (part.index d)) (part.offset d)
    have point:=congrArg (bitDestination r hw route i) ((shape i).read x j g d)
    exact pass.trans (point.trans (bitDestination_arg r hw route ⟨i,x⟩ j digit))

@[simp] theorem combined_stride (shape : ∀i,Shape p (r i)) (multiple : ∀h,p∣hw h)
    (f : ∀i,PrivateMap p (bw i) w hw (route i)) (i : J) (u j g) :
    ((combined r hw route shape multiple f).chunk ⟨i,u⟩ j g).stride=((shape i).chunk u j g).stride := rfl

def BlockMap.publicOnly {B : Type} {next : B→ℕ} {f : BitRef w→BitRef next} (b : BlockMap p w next f) :
    PrivateMap p w next (fun t : Empty=>t.elim) (fun x=>.inl (f x)) where
  map q := .inl (b.map q)
  read q d := congrArg Sum.inl (b.read q d)

end
end Hierarchy.DescentBundleHistory

end OAI
