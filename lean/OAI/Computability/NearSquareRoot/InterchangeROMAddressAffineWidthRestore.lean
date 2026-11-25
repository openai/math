import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorCompile

/-! # Restoring a compact header across an affine pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress.Affine

open IntegerMultiplication IntegerMultiplication.Code Space GeneratorSyntax CommonRegisters

/-- Clone just the leading header into register one. The running command
receives the original header and stream while its saved deck carries the copy. -/
def parkHeader : Cmd := splitRoot 0 (fun _ => .pass) ((clone 0 1 2).join (pack 0))

def returnHeader : Cmd := (move 1 0 2).join (pack 0)

def restoring (c : Cmd) : Cmd := parkHeader.join (c.join returnHeader)

structure Usage where
  time : ℕ
  space : ℕ
  depth : ℕ

def restoreUsage (h x y : Tree) (u : Usage) : Usage :=
  let before := 45*h.count+7
  let after_ := 42*h.count+3
  ⟨before + (u.time + after_ + 2) + 2,
    max ((Tree.fork h x).count + before) (max (h.count+u.space) (h.count+y.count+after_)),
    max (before+1) (max (u.depth+1) after_)⟩

theorem restoring_bounded (c : Cmd) (h x y : Tree) (u : Usage)
    (env : Env) (child : ∀ d b, DeckCap b d →
      BoundedFits env c (pile 0 (.fork h x) d) (pile 0 y d)
        u.time (b+u.space) u.depth)
    (d : Deck) (base : ℕ) (ok : DeckCap base d) :
    let v := restoreUsage h x y u
    BoundedFits env (restoring c) (pile 0 (.fork h x) d) (pile 0 (.fork h y) d)
      v.time (base+v.space) v.depth := by
  let v := restoreUsage h x y u
  have run := child (pile 1 h d) _ (ok.pile 1 h)
  have park : Fits env parkHeader (pile 0 (.fork h x) d) (pile 0 (.fork h x) (pile 1 h d))
      (45*h.count+7) := by
    have cl := fits_clone (i:=0) (j:=1) (u:=2) (by decide) (by decide) (by decide) h env (pile 0 x d)
    rw [← pile_comm 0 x d 1 h (by decide)] at cl
    exact fits_pair (cl.join (fits_pack h x _ 0 env))
  have release : Fits env returnHeader (pile 0 y (pile 1 h d)) (pile 0 (.fork h y) d)
      (42*h.count+3) := by
    rw [pile_comm 0 y d 1 h (by decide)]
    exact (fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) h env _).join (fits_pack ..)
  have p := BoundedFits.of_fits park (cap:=base+v.space) (depth:=45*h.count+7)
    (fun j => by
      have sz := ok.pile 0 (.fork h x) j
      have lo : (Tree.fork h x).count + (45*h.count+7) ≤ v.space := le_max_left ..
      omega) le_rfl
  have r := BoundedFits.of_fits release (cap:=base+v.space) (depth:=v.depth)
    (fun j => by
      have sz := ((ok.pile 1 h).pile 0 y) j
      have lo : h.count+y.count+(42*h.count+3) ≤ v.space := (le_max_right ..).trans (le_max_right ..)
      omega) ((le_max_right ..).trans (le_max_right ..))
  have enough : base + h.count + u.space ≤ base + v.space := by
    have a : h.count + u.space ≤ v.space := (le_max_left ..).trans (le_max_right ..)
    omega
  exact p.join ((run.mono le_rfl enough le_rfl).join r ((le_max_left ..).trans (le_max_right ..)))
    (le_max_left ..)

theorem effective_restoring {X : Type} [Primcodable X] {p : X → Cmd} (h : Effective ltr p) :
    Effective ltr fun x => restoring (p x) :=
  (effective_const ltr parkHeader).join (h.join (effective_const ltr returnHeader))

end InterchangeROMAddress.Affine

end NearSquareRoot
end Computability
end OAI
