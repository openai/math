import OAI.Computability.IntegerMultiplication.Code.Recurse

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code
variable {I : Type}
namespace Tunnel
variable {f s : I→ℝ} {p q t : I→Tree}
variable (nest : I→ Option (I × I))

def wing (p q t : I→Tree) (i:I) : Tree :=
  match nest i with
  | .none => q i
  | .some (x,y) => .fork (p x) (.fork (p y) (t i))
def crest (p q t : I→Tree) (i:I) :=
  Tree.fork (Tree.atom (nest i).isSome) (wing nest p q t i)
structure Twins (nest : I→ Option (I×I)) where
  main : I
  x : I
  y : I
  agree : nest main=some (x,y)

def issue (b : Twins nest) (p t : I→Tree) :=
  Tree.fork (p b.x) (.fork (p b.y) (t b.main))
variable (start : Carries f p (crest nest p q t))
variable (finish : Carries (fun x:Twins nest => f x.main) (fun x => issue nest x q t) (fun x => q x.main))

theorem twin (u : ∀ i,1 ≤ s i)
    (paid : ∀ i,(f i + ((nest i).map (fun (a,b) => s a+s b)).getD 0) ≤ s i)
    (k : I→ℕ) (v : ∀ x:Twins nest,k x.x<k x.main ∧ k x.y<k x.main)
    (start : Carries f p (crest nest p q t))
    (finish : Carries (fun x:Twins nest => f x.main) (fun x => issue nest x q t) (fun x => q x.main)) :
    Sized s p q := by
  classical
  let o : Oracle I := ⟨s,p,q⟩
  let get i := wing nest p q t i
  let K i := (nest i).isSome
  let need i := ((nest i).map (fun (a,b) => [a,b])).getD []
  apply drift (w:=f) (a:=need) o (join (walkway start.runs) (fork (o:=o) (p:=get) K ?_ ?_))
    (fun i => ?_) k (fun i y d => ?_) u
  · let X := {i // K i=false}
    have eq (x:X) : nest x.val=Option.none := by
      have := x.property
      cases e:nest x.val <;> simp [K,e] at *
    have hv : (fun i:X => need i.val)=fun _ => [] := funext (by simp [need,eq])
    have e : (fun i:X => get i.val)=fun i => q i.val := funext (by simp [get,wing,eq])
    change Tunnel o _ (fun i:X => need i.val) (fun i => get i.val) _
    rw [hv,e]
    apply walkway
    exact (Sized.natural (Task.self (b:=fun _ => 0))).mono (by simpa using fun x:X => start.budget x.val)
  · let X := {i // K i=true}
    let b (x : X) : Twins nest :=
      { main := x.val
        x := ((nest x.val).get x.property).1
        y := ((nest x.val).get x.property).2
        agree := by
          rw [Prod.mk.eta,Option.some_get] }
    let y := fun x:X => f x.val
    have vl := fun x:X => start.budget x.val
    have hx := (summon (o:=o) (fun x:X => (b x).x) (w:=y) vl).surround (fun x=>Tree.fork (p (b x).y) (t x.val))
    have hd := ((summon (o:=o) (fun x:X => (b x).y) (w:=y) vl).surround (fun x=>t x.val)).surround
      (fun x=>q (b x).x)
    have bv : Carries y (fun x => crest nest p q t x.val) (fun x => crest nest p q t x.val) :=
      (Carries.idles (start.budget) start.out).slide (fun x:X => x.val)
    have hm := bv.out.right (p:=fun x => Tree.atom (K x.val)) (q:=fun x:X => wing nest p q t x.val) -- args?
    have eq (x:X) : nest x.val=some ((b x).x,(b x).y) := (b x).agree
    simp only [wing,eq] at hm
    have fy := finish.slide b
    have vh := fy.small.left (q:=fun x => Tree.fork (q (b x).y) (t x.val))
    have e1 := Carries.swap vl vh (Volume.right hm)
    let v2 := fy.small.right (p:=fun x => q (b x).x)
    have e2 := Carries.swap vl v2 vh
    have mv := (((hx.join (walkway (o:=o) e1.runs)).join hd).join
      (walkway (o:=o) (e2.runs.chain fy.runs)))
    simpa only [get,wing,need,eq,Option.map_some,Option.getD_some,List.append_nil,List.singleton_append,
      o,Function.comp_def] using mv
  · specialize paid i; cases e:nest i with
    | none => simpa [need,Oracle.reserve,e] using paid
    | some j =>
      obtain ⟨a,b⟩ := j
      simpa [need,Oracle.reserve,e,o] using paid
  · cases e:nest i with
    | none => simp [need,e] at d
    | some j =>
      obtain ⟨a,b⟩ := j
      have hs := v (⟨i,a,b,e⟩)
      simp [need,e] at d
      rcases d with rfl|rfl
      exacts [hs.1,hs.2]

end Tunnel
end Code

end IntegerMultiplication
end Computability
end OAI
