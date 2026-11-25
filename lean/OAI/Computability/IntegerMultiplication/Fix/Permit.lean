import OAI.Computability.IntegerMultiplication.Fix.Recover
import OAI.Computability.IntegerMultiplication.Strip.Halo

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Fix
open Code Strip
variable {A : Type} [Codec A]
variable {I : Type} {T U : I→Type}
variable (s : (i:I)→Series (T i)) (t : (i:I)→Series (U i))
-- marker includes key even on untouched entries (ignored).
abbrev Info := Bool × Key
variable (m : (i:I)→T i→Info) (z : (i:I)→U i→Info)
variable (x : (i:I)→T i→A) (y : (i:I)→U i→A)
def stamps {T} (m : T → Info) (x : T→A) (list : Series T) : List (Bool × (Key × A)) :=
  list.tab (fun i => ((m i).1,(m i).2,x i))
def batch {T} (b : Bool) (m : T → Info) (x : T→A) (list : Series T) := Ribbon.read b (stamps m x list)
def hot i := batch true (m i) (x i) (s i)

omit [Codec A] in
theorem smaller {B : Type} (l : List (Bool × (Key × A))) (f : Key×A→B) (b : Bool) :
    List.map f (Ribbon.read b l) = Ribbon.read b (l.map fun x => (x.1,f x.2)) := by
  unfold Ribbon.read
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases e:x.1=b <;> simp [Ribbon.keep,ih,e,-List.map_map] at *

def name {T} (m : T→Info) (s : Series T) := s.tab m
omit [Codec A] in
theorem binLabel {T} (m:T→Info) (s : Series T) (x:T→A) (b) :
    blot (batch b m x s) = Ribbon.read b (name m s) := by
  rw [blot,batch,smaller,stamps,name,Series.map_tab]
  simp [Function.comp_def]
omit [Codec A] in
theorem binValue {T} (m:T→Info) (s : Series T) (x:T→A) (b) :
    parcel (batch b m x s) = Ribbon.read b (s.tab (fun i => ((m i).1,x i))) := by
  rw [parcel,batch,smaller,stamps,Series.map_tab]; rfl
omit [Codec A] in
theorem reunite {T} (m:T→Info) (s : Series T) (x:T→A) :
    joinbins (s.tab (fun i => (m i).1),parcel (batch false m x s), parcel (batch true m x s)) =
      s.tab x := by
  rw [binValue,binValue]
  have h := join_plates (s.tab fun i => ((m i).1,x i))
  simp_rw [Series.map_tab] at h
  exact h

-- linear preprocessing
variable {r : Regime I} {n l : I→ℕ} {q : I→Tree}
private theorem binWord (b : Bool)
    (a : Rip r n l q (stackRun s (fun i j => send (x i j))))
    (h : Rip r n l q (stackRun s (fun i j => send (m i j)))) :
    Rip r n l q (fun i => send (batch b (m i) (x i) (s i))) := by
  have z := Rip.coalesce _ _ h a
  unfold stackRun together at z
  change Rip r n l q (fun i => stripe (s i) (fun t => send (m i t, x i t))) at z
  simp_rw [stripe_eq'] at z
  let f := fun p : Info × A => (p.1.1,p.1.2,p.2)
  have u : Easy f := by unfold f; fun_prop
  have y := Loom.Fatigue.act (x:=fun i => (s i).tab (fun t => (m i t,x i t))) z _ (Ribbon.easyRead b u.mapping)
  unfold batch stamps
  simpa only [Series.map_tab,Function.comp_def,f] using y
theorem repack (h : Rip r n l q (stackRun s fun i j => send (m i j)))
    (wv w : (i:I)→List A)
    (a : ∀ i,wv i=parcel (batch false (m i) (x i) (s i)) ∧ w i=parcel (batch true (m i) (x i) (s i)))
    (pV : Rip r n l q (send ∘ wv)) (pv : Rip r n l q (send ∘ w)) :
    Rip r n l q (stackRun s (fun i j => send (x i j))) := by
  unfold stackRun at *
  simp only [stripe_eq'] at *
  have e := Loom.Fatigue.act (x:=fun i => (s i).tab (m i)) h _ (Easy.fst (X:=Bool) (Y:=Key)).mapping
  simp only [Series.map_tab,Function.comp_def] at e
  have y := Loom.Fatigue.act (x:=fun i => ((s i).tab (fun p => (m i p).1),wv i,w i)) (e.twice (pV.twice pv)) _ easy_join_bins
  simpa only [(a _).1,(a _).2,reunite] using y

/-- Sparse relabel, with sorting temporary measure expressed per actual
exceptional key count and record size. No complete-key assumption.
Untouched stream may retain ordered content without any key checks. -/
structure Rule (d : I→ℕ) : Prop where
  snag i : ∀ r∈hot s m x i,r.1.length=d i
  tagEnd i : ∀ r∈hot t z y i,r.1.length=d i
  same i k : draw k (hot s m x i)=draw k (hot t z y i)
  stationary i : parcel (batch false (m i) (x i) (s i))=parcel (batch false (z i) (y i) (t i))

theorem Rule.patch {d : I→ℕ}
    (g : Rule s t m z x y d)
    (a : Rip r n l q (stackRun s fun i j => send (x i j)))
    (v : Rip r n l q (stackRun s fun i j => send (m i j)))
    (v' : Rip r n l q (stackRun t fun i j => send (z i j)))
    (ok : ∃ u C : ℕ, ∀ i, ((3*(d i+1)*(Schedule.total (hot s m x i)+
      Schedule.total (hot t z y i))+1:ℕ):ℝ) ≤ (C:ℝ)*mass r n l u i) :
    Rip r n l q (stackRun t fun i j => send (y i j)) := by
  let G (i:I) : Schedule A :=
    ⟨d i,hot s m x i,hot t z y i,g.snag _,g.tagEnd _,g.same _⟩
  have h := Schedule.resolve.along G
  have sta := binWord s m x false a v
  have go0 := binWord s m x true a v
  have sta' := Loom.Fatigue.act (x:=fun i=>batch false (m i) (x i) (s i)) sta _ (Easy.snd (X:=Key) (Y:=A)).mapping
  have f : Rip r n l q (send ∘ fun i => (t i).tab (z i)) := by
    unfold stackRun at v'
    simpa only [stripe_eq',Function.comp_def] using v'
  have zd := Loom.Fatigue.act f _ (Ribbon.easyRead true easy_id)
  have hi : Rip r n l q (input ∘ G) := by
    unfold input question G
    simp only [Function.comp_def,hot,binLabel,name]
    exact Rip.twice go0 zd
  have y0 :
      Rip r n l q (output ∘ G) := by
    obtain ⟨u,CV,x⟩ := ok
    obtain ⟨k,hq⟩ := hi
    let cost := mass r n l (k+u)
    have ik := hq.larger (mass_le (by omega : k≤k+u))
    exact ⟨k+u,ik.sequence (h.adapts ik.budget CV fun i => (x i).trans (by gcongr; exact mass_le (by omega) i))⟩
  apply repack t z y v' _ _ (fun i => ⟨g.stationary i,rfl⟩)
  · exact sta'
  exact y0
end Fix

end IntegerMultiplication
end Computability
end OAI
