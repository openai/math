import OAI.Hierarchy.ProtocolRAMPurchaseSuccessor
import OAI.Hierarchy.ProtocolRAMPurchaseDFS
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Immutable endpoint sockets of a purchased sampler path

The destination socket reserves a forward digit and one inverse-sampler
digit per hop. The inverse table is static and consists of one extra word
per outgoing sampler cell. Repeated occurrences of the same sampler neighbor
still have their distinct forward digits.
-/

noncomputable section
namespace Hierarchy.TaggedShorterPathPorts
open ProbeStage ProtocolRAMPurchaseOwners ProtocolRAM.PurchaseDFS
open scoped Classical

variable {n m D groups h : ℕ} {G : Type*}

abbrev Digits (D h : ℕ) := Fin h → Fin D
abbrev ReverseDigits (D h : ℕ) := Fin h → Fin D × Fin D

def incoming (next : Fin m → List (Fin m)) (v : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => v ∈ next i)

def backCode (next : Fin m → List (Fin m)) (col : ∀ i,(incoming next i).card≤D)
    (o : Fin m) (d : Fin D) : Fin D :=
  match (next o)[d.val]? with
  | none => d
  | some v => if member : o ∈ incoming next v then
    (((incoming next v).orderIsoOfFin rfl).symm ⟨o,member⟩).castLE (col v) else d

theorem backCode_inj (next : Fin m → List (Fin m)) (col : ∀ i,(incoming next i).card≤D)
    {o p v : Fin m} {d e : Fin D} (lhs : (next o)[d.val]?=some v) (rhs : (next p)[e.val]?=some v)
    (same : backCode next col o d=backCode next col p e) : o=p := by
  let iso := ((incoming next v).orderIsoOfFin rfl).symm
  have ox : o∈incoming next v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.mem_of_getElem? lhs⟩
  have px : p∈incoming next v := Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.mem_of_getElem? rhs⟩
  have eq : iso ⟨o,ox⟩=iso ⟨p,px⟩ := by
    apply Fin.ext
    simpa [iso,backCode,lhs,rhs,ox,px] using congrArg Fin.val same
  exact congrArg Subtype.val (iso.injective eq)

inductive Trail (choice : Fin n → Fin D → Option (Fin n)) (back : Fin n → Fin D → Fin D) :
    (h : ℕ) → Fin n → Digits D h → Fin n → ReverseDigits D h → Prop
  | endAt (start : Fin n) (z : Digits D 0) : Trail choice back 0 start z start Fin.elim0
  | step {h : ℕ} {s v e : Fin n} (z : Digits D (h+1)) (c : ReverseDigits D h)
      (live : choice s (z 0)=some v) (tail : Trail choice back h v (Fin.tail z) e c) :
      Trail choice back (h+1) s z e (Fin.cons (back s (z 0),z 0) c)

/-- All named digits and the terminal socket come from this exact native
row-by-row DFS. The last row is retained even when the path has length zero. -/
theorem trail_of_walk (choice : Fin n → Fin D → Option (Fin n)) (back : Fin n → Fin D → Fin D)
    (s : Fin n) (z : Digits D h) {path : List (Fin n)} (live : walk choice s z=some path) :
    ∃ e c, Trail choice back h s z e c ∧ path.getLast?=some e := by
  induction h generalizing s path with
  | zero =>
    have eq : [s]=path := Option.some.inj live
    exact ⟨s,Fin.elim0,.endAt s z,by simp [←eq]⟩
  | succ h ih =>
    cases hv : choice s (z 0) with
    | none => simp [walk,hv] at live
    | some v =>
      cases ht : walk choice v (Fin.tail z) with
      | none => simp [walk,hv,show (fun i => z i.succ)=Fin.tail z from rfl,ht] at live
      | some rest =>
        have run : (s::rest)=path := by simpa [walk,hv,show (fun i => z i.succ)=Fin.tail z from rfl,ht]
          using live
        obtain ⟨e,c,t,last⟩ := ih v (Fin.tail z) ht
        refine ⟨e,_,.step z c hv t,?_⟩
        subst path
        cases rest with
        | nil => simp at last
        | cons a l => simpa using last

/-- Fixed terminal socket and reversed sampler information determine the
entire starting occurrence and original digit word. -/
theorem reconstruct {choice : Fin n → Fin D → Option (Fin n)} {back : Fin n → Fin D → Fin D}
    (previous : ∀ s t v d e, choice s d=some v → choice t e=some v → back s d=back t e → s=t)
    {s t e : Fin n} {z y : Digits D h} {c b : ReverseDigits D h}
    (left : Trail choice back h s z e c) (right : Trail choice back h t y e b) (agree : c=b) :
    s=t ∧ z=y := by
  induction left generalizing t with
  | endAt s z =>
    cases right
    exact ⟨rfl,funext fun i=>i.elim0⟩
  | @step h s v e z c atS tail ih =>
    cases right with
    | @step _ _ u _ y b atT other =>
      have cc : c=b := funext fun j => by simpa using congrFun agree j.succ
      have first : (back s (z 0),z 0)=(back t (y 0),y 0) := by simpa using congrFun agree 0
      obtain ⟨vu,zy⟩ := ih other cc
      subst u
      refine ⟨previous s t v _ _ atS atT (congrArg Prod.fst first),?_⟩
      funext j
      induction j using Fin.cases with
      | zero => exact congrArg Prod.snd first
      | succ j => exact congrFun zy j

theorem deterministic {choice : Fin n → Fin D → Option (Fin n)} {back : Fin n → Fin D → Fin D}
    {s e f : Fin n} {z : Digits D h} {c b : ReverseDigits D h}
    (left : Trail choice back h s z e c) (right : Trail choice back h s z f b) : e=f ∧ c=b := by
  induction left generalizing f with
  | endAt => cases right; exact ⟨rfl,rfl⟩
  | step z c atS tail ih =>
    cases right with
    | step _ b atT other =>
      have eq := Option.some.inj (atS.symm.trans atT)
      subst_vars
      obtain ⟨last,codes⟩ := ih other
      exact ⟨last,congrArg (Fin.cons _) codes⟩

def socketSource (p : Tiles (Fin n) G m) : (Fin n × Digits D h) ↪ G × Fin m × Digits D h where
  toFun z := (p.group z.1,p.input z.1,z.2)
  inj' := by
    rintro ⟨s,z⟩ ⟨t,y⟩ eq
    have sockets : (p.group s,p.input s)=(p.group t,p.input t) :=
      congrArg (fun a : G × Fin m × Digits D h => (a.1,a.2.1)) eq
    exact Prod.ext (p.input_inj sockets) (congrArg (fun a : G × Fin m × Digits D h => a.2.2) eq)

def sample (next : Fin m → List (Fin m)) (o : Fin m) (d : Fin D) := (next o)[d.val]?

theorem previous_tile (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (col : ∀ i,(incoming next i).card≤D) {s t v : Fin n} {d e : Fin D}
    (a : successor p enc (sample next) s d=some v) (b : successor p enc (sample next) t e=some v)
    (code : backCode next col (p.output s) d=backCode next col (p.output t) e) : s=t := by
  obtain ⟨gs,os⟩ := (successor_eq_some_iff ..).mp a
  obtain ⟨gt,ot⟩ := (successor_eq_some_iff ..).mp b
  exact p.output_inj (Prod.ext (gs.symm.trans gt) (backCode_inj next col os ot code))

def Live (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) :=
  {z : Fin n × Digits D h // ∃ path,walk choice z.1 z.2=some path}

private theorem annotate (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (col : ∀ i,(incoming next i).card≤D) (z : Live (successor p enc (sample (D:=D) next)) h) :
    ∃ e c, Trail (successor p enc (sample next)) (fun s d=>backCode next col (p.output s) d)
      h z.val.1 z.val.2 e c := by
  obtain ⟨l,hl⟩ := z.property
  obtain ⟨e,c,t,_⟩ := trail_of_walk _ (fun s d => backCode next col (p.output s) d) _ _ hl
  exact ⟨e,c,t⟩

def socketTarget (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (col : ∀ i,(incoming next i).card≤D) :
    Live (successor p enc (sample (D:=D) next)) h ↪ G × Fin m × ReverseDigits D h where
  toFun z := let e := (annotate p enc next col z).choose
             (p.group e,p.output e,(annotate p enc next col z).choose_spec.choose)
  inj' := by
    intro x y eq
    let e := (annotate p enc next col x).choose
    let f := (annotate p enc next col y).choose
    have sockets : (p.group e,p.output e)=(p.group f,p.output f) :=
      congrArg (fun q : G × Fin m × ReverseDigits D h => (q.1,q.2.1)) eq
    have ef : e=f := p.output_inj sockets
    have a := (annotate p enc next col x).choose_spec.choose_spec
    have b := (annotate p enc next col y).choose_spec.choose_spec
    change Trail _ _ _ _ _ e _ at a
    change Trail _ _ _ _ _ f _ at b
    rw [←ef] at b
    have old:=reconstruct (fun s t v d e=>previous_tile p enc next col) a b (congrArg (fun q=>q.2.2) eq)
    exact Subtype.ext (Prod.ext old.1 old.2)

theorem socketTarget_trail (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (col : ∀ i,(incoming next i).card≤D) (z : Live (successor p enc (sample (D:=D) next)) h)
    (e : Fin n) (c : ReverseDigits D h)
    (trail : Trail (successor p enc (sample next)) (fun s d=>backCode next col (p.output s) d)
      h z.val.1 z.val.2 e c) : socketTarget p enc next col z=(p.group e,p.output e,c) := by
  obtain ⟨last,codes⟩ := deterministic (annotate p enc next col z).choose_spec.choose_spec trail
  exact Prod.ext (congrArg p.group last) (Prod.ext (congrArg p.output last) codes)

/-- Source and destination lie in the same original group even when the
published terminal socket is reached after several sampler hops. -/
theorem group_of_trail (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    {back : Fin n → Fin D → Fin D} {s e : Fin n} {z : Digits D h} {c : ReverseDigits D h}
    (t : Trail (successor p enc (sample next)) back h s z e c) : p.group e=p.group s := by
  induction t with
  | endAt => rfl
  | step _ _ atS _ ih => exact ih.trans ((successor_eq_some_iff ..).mp atS).1

theorem socketTarget_group (p : Tiles (Fin n) G m) (enc : G ↪ Fin groups) (next : Fin m → List (Fin m))
    (col : ∀ i,(incoming next i).card≤D) (z : Live (successor p enc (sample (D:=D) next)) h) :
    ((socketTarget p enc next col) z).1=p.group z.val.1 :=
  group_of_trail p enc next (annotate p enc next col z).choose_spec.choose_spec

theorem source_port_count : Fintype.card (Fin m × Digits D h)=m*D^h := by simp [Digits]
theorem target_port_count : Fintype.card (Fin m × ReverseDigits D h)=m*D^(2*h) := by
  simp [ReverseDigits,pow_mul,pow_two]

end Hierarchy.TaggedShorterPathPorts

end
end OAI
