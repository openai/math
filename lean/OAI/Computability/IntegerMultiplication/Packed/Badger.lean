import OAI.Computability.IntegerMultiplication.Packed.Rank
import OAI.Computability.IntegerMultiplication.Short

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Packed
open Code Strip Dims Loom Port Adic
-- Beam shell gate on Q holders with implementing header
variable (P G R S : Tape) {H L i : ℕ}
abbrev domeQ (H L i) := layouts P G R S (lineQ H L i)
def capslot (H L i) :
    Slot (lineQ H L i) [] (line 2 (cap i H L)) [] :=
  (Slot.sole _).arrive (package H L i)
@[simp] theorem readcap (x : Queue H L i) :
    (capslot H L i).read x = (package H L i).cast x := rfl
@[simp] theorem altercap (x : Queue H L i) (y) :
    (capslot H L i).alter x y=(package H L i).cast.symm y := rfl
def capseal (H L i) : Seal (lineQ H L i) (field 2 (cap i H L)) :=
  package H L i
private def conc {A B : Type} {s : Series A} {b : Series B}
    {P S : Tape} (t : Seal s P) (v : Seal b S) :
    Seal (s.cart b) (P++S) := (t.split v).thenDo (Loom.unite _ _)

open Pos
def broad (H L i : ℕ) (a : Pos) :=
  if a = sun then P++([]:Tape) else P ++ (field 2 (cap i H L) ++ (G ++ []))
def cross (H L i : ℕ) (a : Pos) :=
  if a = noon then ([]:Tape) ++ (R ++ [])
  else ([]:Tape) ++ (G ++ (field 2 (cap i H L) ++ (R ++ [])))

-- only swaps involving last (others via up to three applications)
def barrier (H L i : ℕ) (a : Pos) (q : a ≠ moon) :
    Axis (domeQ P G R S H L i) (broad P G H L i a) (line 2 (cap i H L))
      (cross G R H L i a) (line 2 (cap i H L)) ([]++S) :=
  let t := capslot H L i
  let z := t.exit (Adopt.same (layout S))
  match a with
  | sun =>
    let g := Adopt.same (layout R)
    let x := Adopt.same (layout G)
    (Axis.both t (((z.enter g).enter (capseal H L i)).enter x)).enter (Adopt.same _)
  | noon =>
    ((((Axis.both t (z.enter (Adopt.same (layout R)))).enter (Adopt.same (layout G))).enter
      (capseal H L i)).enter (Adopt.same _))
  | moon => False.elim (q rfl)

theorem barrier_main (x : Dome P G R S (Queue H L i)) (a : Pos) (q : a≠moon) :
    let e := barrier P G R S H L i a q
    (e.tune (Equiv.prodComm _ _)).symm x =
      wipe x (arrange (Equiv.swap a moon) (peek x)) := by
  let k := capslot H L i
  let z := k.exit (Adopt.same (layout S))
  let Q := capseal H L i
  obtain ⟨c,u,f,v,g,w,b⟩ := x
  obtain _|_|_ := a
  all_goals first | contradiction | skip
  · let e := (Axis.both k (((z.enter (Adopt.same (layout R))).enter Q).enter (Adopt.same (layout G)))).enter (Adopt.same (layout P))
    change e.bridge (c,u,f,v,g,w,b) ((e.pair _).2,(e.pair _).1)=_
    simp only [e,z,Axis.enter_pair,Axis.both_pair,Slot.enter_read,Slot.exit_read,
      Axis.enter_bridge,Axis.both_bridge,Slot.enter_alter,Slot.exit_alter,k,
      readcap,altercap,Equiv.symm_apply_apply]
    simp [wipe,peek,mark,note,arrange,Equiv.swap_apply_def]
  let e := (((Axis.both k (z.enter (Adopt.same (layout R)))).enter (Adopt.same (layout G))).enter Q).enter (Adopt.same (layout P))
  change e.bridge (c,u,f,v,g,w,b) ((e.pair _).2,(e.pair _).1)=_
  simp only [e,z,Axis.enter_pair,Axis.both_pair,Slot.enter_read,Slot.exit_read,
    Axis.enter_bridge,Axis.both_bridge,Slot.enter_alter,Slot.exit_alter,k,
    readcap,altercap,Equiv.symm_apply_apply]
  simp [wipe,peek,mark,note,arrange,Equiv.swap_apply_def]

variable {X : Type} (P G R S : X→Tape) (H L i : X→ℕ) {r : Regime X}
variable (hP : Told r P) (hG : Told r G) (hR : Told r R) (hS : Told r S)
variable (guard : ∀ x a,a∈P x ++ G x ++ R x ++ S x → a≤Net.Shuttle.base)
variable (h : r.Has fun x => tally (cap (i x) (H x) (L x)))
abbrev Series0 := fun x:X => domeQ (P x) (G x) (R x) (S x) (H x) (L x) (i x)
abbrev Addr := fun x:X => Dome (P x) (G x) (R x) (S x) (Queue (H x) (L x) (i x))
abbrev rate := fun x:X => (Series0 P G R S H L i x).count
noncomputable abbrev modes := Spindle.modes (τ:=Net.Motif.sigma) fun x:X => cap (i x) (H x) (L x)
variable {l : X→ℕ}
abbrev Sail (from_ to_ : X→ Code.Tree) :=
  Breeze (modes H L i) r (rate P G R S H L i) l (together r.header from_) to_

include hP hG hR hS h
theorem port : Station r (Series0 P G R S H L i) := by
  have z := terminal (p:=2) (by decide) (fun x:X=>cap (i x) (H x) (L x)) h
  let Q := fun x:X => lineQ (H x) (L x) (i x)
  have e : Station r Q := by
    have hp x : (Q x).count=(line 2 (cap (i x) (H x) (L x))).count := (package (H x) (L x) (i x)).cost -- fail
    unfold Station; simp_rw [hp]; exact z
  exact hP.station.product (e.product (hG.station.product (e.product (hR.station.product (e.product hS.station)))))

variable {U:X→Type} (d : (x:X)→Series (U x)) (z : ∀ x,(d x).count≤l x)
variable (f : (x:X)→Addr P G R S H L i x→U x→Bead)
include z guard
noncomputable section
open Strip.Optic
theorem exchange (s : Pos) (t : s≠moon) :
    Sail P G R S H L i (r:=r) (l:=l) (cloth (Series0 P G R S H L i) d f)
      (cloth (Series0 P G R S H L i) d (fun x => travel
        (invoke (arrange (Equiv.swap s moon)) _ _ _ _) (f x))) := by
  let a := Series0 P G R S H L i
  let N (x:X) := cap (i x) (H x) (L x)
  let P' := fun x=> broad (P x) (G x) (H x) (L x) (i x) s
  let G' := fun x=> cross (G x) (R x) (H x) (L x) (i x) s
  let B' x := ([]:Tape) ++ S x
  let v (x:X) := (barrier (P x) (G x) (R x) (S x) (H x) (L x) (i x) s t)
  have hv := Told.carrier (q:=2) (by decide) N h
  have w := Spindle.rectBead (v := fun (x:X) b => f x ((v x).view.cast.symm b)) P' G' B' N
    h (show Told r P' from ?_) (show Told r G' from ?_) ((Told.nil).append hS) (fun x n e => ?_) l d z
  · have eq (x) : rate P G R S H L i x =
        (stock 2 (P' x) (G' x) (B' x) (N x)).count := (v x).view.cost
    unfold Sail
    rw [funext eq]
    have p : cloth (fun x => stock 2 (P' x) (G' x) (B' x) (N x)) d
        (fun x b => f x ((v x).view.cast.symm b)) = cloth a d f := by
      unfold cloth stackRun; funext x
      erw [(v x).view.packet]
      apply congrArg (stripe (a x)); funext b
      change strip (d x) (f x ((v x).view.cast.symm ((v x).view.cast b)))=_
      rw [Equiv.symm_apply_apply]
    dsimp only at w
    rw [p] at w
    unfold cloth stackRun at *
    have q : (fun x => stripe (stock 2 (P' x) (G' x) (B' x) (N x))
        fun b => strip (d x) (f x ((v x).view.cast.symm (swapper _ _ _ b))))
        =
        (fun x => stripe (a x) (fun b =>
          strip (d x) (travel (invoke (arrange (Equiv.swap s moon)) _ _ _ _) (f x) b))) := by
      funext x
      erw [(v x).view.packet]
      apply congrArg (stripe _); funext b
      change strip (d x) (f x _) = strip (d x) (f x _)
      rw [gone,arrange_symm,show ((Equiv.swap s moon).symm) = Equiv.swap s moon from rfl]
      rw [← barrier_main (P x) (G x) (R x) (S x) b s t]
      rfl
    exact (q ▸ (show Breeze _ _ _ _ (fun x => _) (fun x => stripe (stock 2 (P' x) (G' x) (B' x) (N x))
        fun b => strip (d x) (f x ((v x).view.cast.symm (swapper _ _ _ b)))) from w))
  · cases s with
    | sun => exact hP.append Told.nil
    | _ => exact hP.append (hv.append (hG.append Told.nil))
  · cases s with
    | noon => exact (Told.nil).append (hR.append Told.nil)
    | _ => exact (Told.nil).append (hG.append (hv.append (hR.append Told.nil)))
  have ve := ivory (p:=2) (by decide) (j:=N x)
  by_contra g
  have hl (d : n∈P x ∨ n∈G x ∨ n∈R x ∨ n∈S x) := g (guard x n (by simp; tauto))
  have hd (q : n∈field 2 (N x)) := (g ((ve n q).2.trans Net.Shuttle.base_large.le))
  cases s <;> simp [P',G',B',broad,cross] at e
  all_goals tauto
end
end Packed

end IntegerMultiplication
end Computability
end OAI
