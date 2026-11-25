import OAI.Computability.IntegerMultiplication.Scale.Newsroom

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Scale
open Param Code Carry Brief Staff Strip Loom Hook Dusk Grid IntegerMultiplication.Star
open IntegerMultiplication.Fourier
variable {I:Type} (n:I→ℕ)

abbrev Vect i :=
  (a : Direction (n i)) → Spot (side (n i) a) → Spot (moduli (n i) a) → Grain (W (n i))
abbrev Vest i :=
  (a : Direction (n i)) → Spot (moduli (n i) a) → Spot (moduli (n i) a) → Grain (W (n i))

def ArrayScript (z:(i:I)→Vect n i) (i:I) :=
  List.ofFn fun a:Direction (n i)=>
    List.ofFn fun j : Spot (side (n i) a)=> List.ofFn fun k:Spot (moduli (n i) a)=> Dusk.mark (z i a j k)
def RestoreScript (z:(i:I)→Vest n i) (i:I) :=
  List.ofFn fun a:Direction (n i)=>
    List.ofFn fun j : Spot (moduli (n i) a)=> List.ofFn fun k:Spot (moduli (n i) a)=> Dusk.mark (z i a j k)

variable {r:Regime I} (q:Calendar r n)
abbrev hub := lanes ∘ n
abbrev parameters := q.royalty n
abbrev beam := signal (hub n) (parameters n q)
abbrev pos_ (i:Across (hub n)) := i.1
include q
private theorem space :
    RoomLine (beam n q) (n ∘ pos_ n) (fun i:Across (hub n)=>i.2) :=
  ⟨q.levels n (hub n) (parameters n q),floor_ _ _⟩

theorem sounds :
    ∃ z:(i:I)→ Vect n i,
      r.Has (ArrayScript n z) ∧
      ∀ (i:I) a j k,
        ‖meaning (F (n i)) (W (n i)) (z i a j k)-win (D (n i) a) j k‖ ≤ err (n i) := by
  obtain ⟨b,h,e⟩:= catalog _ (space n q)
  let Z (i:I) a j k := b ⟨i,a⟩ j k
  refine ⟨Z,?_,fun i a j k=>e ⟨i,a⟩ j k⟩
  exact harvest _ (q.royalty n)
    (fun i a=> List.ofFn fun j:Spot (side (n i) a)=> List.ofFn fun k:Spot (moduli (n i) a)=> Dusk.mark (Z i a j k)) h

theorem shrines (u:Bool) :
    ∃ z:(i:I)→Vest n i,r.Has (RestoreScript n z) ∧
    ∀ (i:I) a j k,
      ‖meaning (F (n i)) (W (n i)) (z i a j k)-Garden.climate u
      (mixTable (side (n i) a) (D (n i) a) (nhood (Scale.J (n i))) (Scale.K (n i)) j k)
      (moduli (n i) a)‖ ≤ err (n i) := by
  obtain ⟨b,h,e⟩:= library _ (space n q) u
  let Z (i:I) a j k := b ⟨i,a⟩ j k
  refine ⟨Z,?_,fun i a j k=>e ⟨i,a⟩ j k⟩
  exact harvest _ (q.royalty n) (fun i a=>List.ofFn fun j:Spot (moduli (n i) a)=>
    List.ofFn fun k:Spot (moduli (n i) a)=> mark (Z i a j k)) h

structure Faculty (n:I→ℕ) where
  widen : (i:I) → Vect n i
  narrow : Bool → (i:I) → Vest n i
  bank : (i:I)→ℕ→Grain (W (n i))

namespace Faculty
variable (v : Faculty n)
structure quality : Prop where
  A i : ∀ a j k,‖meaning (F (n i)) (W (n i)) (v.widen i a j k) - win (D (n i) a) j k‖≤err (n i)
  B i : ∀ (u:Bool) a j k, ‖meaning (F (n i)) (W (n i)) (v.narrow u i a j k) -
    Garden.climate u (mixTable (side (n i) a) (D (n i) a) (nhood (Scale.J (n i))) (Scale.K (n i)) j k)
    (moduli (n i) a)‖ ≤ err (n i)
  C i : ∀ t:Fin (wall (n i)),‖meaning (F (n i)) (W (n i)) (v.bank i t)-
    Axon.R (ell (n i)) (t.val:ℕ)‖≤err (n i)
structure release (r: Regime I) : Prop where
  A : r.Has (ArrayScript n v.widen)
  B u : r.Has (RestoreScript n (v.narrow u))
  C : r.Has (fun i=>telex (F (n i)) (ell (n i)) (v.bank i))
-- possible short width local telex: use same bank request but generate queries poly, usable globally

theorem obtain_ :
    ∃ v:Faculty n,v.quality n ∧ v.release n r := by
  obtain ⟨z,H,E⟩:= sounds n q
  choose b a t using shrines n q
  obtain ⟨k,V,Y⟩:= Scale.desk n q
  exact ⟨⟨z,b,k⟩,⟨E,fun i u j x y=>t u i j _ _,Y⟩,⟨H,a,V⟩⟩
end Faculty
end Scale

end IntegerMultiplication
end Computability
end OAI
