import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBounded
import OAI.Computability.NearSquareRoot.InterchangeROMProgramEffective

/-! # Compiling the action of a spectral pass on every check lane

The numeric source positions are traversed once in the bank's physical order.
The row operation reads the shared header, and the compiler restores the
header and every lane position even when the bank is empty.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.SweepBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space LoomRegisters InterchangeROM GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)

def selection (n : ℕ) : List (ℕ × Unit) := (List.range n).map fun j => (j,())

def bank (n : ℕ) (oneRow : Cmd) : Cmd := routeCommand (fun _ : Unit => oneRow) (selection n)

theorem bank_within {R : ℕ} (hr : 3 ≤ R) {oneRow : Cmd} (h : Within R oneRow) (n : ℕ) :
    Within R (bank n oneRow) := route_within hr _ (fun _ => h) _

theorem effective_bank {X : Type} [Primcodable X] {n : X → ℕ} {oneRow : X → Cmd}
    (hn : Computable n) (hr : Effective ltr oneRow) :
    Effective ltr (fun x => bank (n x) (oneRow x)) := by
  apply effective_route (op := fun x (_ : Unit) => oneRow x)
    (entries := fun x => selection (n x))
  · exact (Primrec.list_map Primrec.id
      (Primrec.snd.pair (Primrec.const ())).to₂).to_comp.comp (Primrec.list_range.to_comp.comp hn)
  · exact Computable.comp (f:=fun x => file ltr (oneRow x)) (g:=Prod.fst) hr Computable.fst

def packetCost (h : Tree) (xs ys : List Tree) (charges : List Allowance) : Allowance :=
  let v := packet h xs
  let w := packet h ys
  ⟨(xs.length+2)*(160*(v.count+1)) + (charges.map Allowance.time).sum,
    170*(v.count+1) + w.count + (charges.map Allowance.cap).foldr max 0,
    170*(v.count+1) + (charges.map Allowance.depth).foldr max 0⟩

private theorem le_peak {A : Type} (f : A → ℕ) (a : A) (l : List A) (h : a ∈ l) :
    f a ≤ (l.map f).foldr max 0 := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hs
    · exact le_max_left ..
    · exact (ih hs).trans (le_max_right ..)

abbrev Run (env : Env) (c : Cmd) (x y : Tree) (p : Allowance) :=
  ∀ r base, DeckCap base r → BoundedFits env c (pile 0 x r) (pile 0 y r)
    p.time (base+p.cap) p.depth

theorem bank_bounded {A : Type} (s : Series A) (h : Tree) (x y : A → Tree)
    (oneRow : Cmd) (charge : A → Allowance) (env : Env)
    (hc : ∀ a, Run env oneRow (.fork h (x a)) (y a) (charge a)) :
    Run env (bank s.count oneRow) (packet h (s.tab x)) (packet h (s.tab y))
      (packetCost h (s.tab x) (s.tab y) (s.tab charge)) := by
  let sel (a : A) : ℕ × Unit := ((s.index a).val,())
  have eqsel : s.explore.map sel = selection s.count := by
    apply List.ext_getElem (by simp [selection,Series.count])
    intro j hj hk
    have hj' : j < s.count := by simpa [selection] using hk
    simp only [selection,List.getElem_map,List.getElem_range]
    change ((s.index (s.follow ⟨j,hj'⟩)).val,()) = (j,())
    rw [s.index_follow]
  have src (a : A) : source (s.tab x) (sel a).1 = x a := by
    have hit : (s.index a).val < (s.tab x).length := by simp
    rw [source, List.getElem?_eq_getElem hit, Option.getD_some,s.get x (s.index a) hit]
    simp
  let S := (s.tab (fun a => (charge a).cap)).foldr max 0
  let D := (s.tab (fun a => (charge a).depth)).foldr max 0
  have bounded (a : A) (r : Deck) (b : ℕ) (hr : DeckCap b r) :
      BoundedFits env oneRow (pile 0 (.fork h (source (s.tab x) (sel a).1)) r)
        (pile 0 (y a) r) (charge a).time (b+S) D := by
    rw [src]
    exact (hc a r b hr).mono le_rfl
      (Nat.add_le_add_left (le_peak (fun k => (charge k).cap) a s.explore (s.complete a)) b)
      (le_peak (fun k => (charge k).depth) a s.explore (s.complete a))
  intro r b hr
  have z := route_bounded h (s.tab x) s.explore sel (fun _ : Unit => oneRow) y (fun a => (charge a).time)
    S D env (fun a => by simp [sel]) bounded r b hr
  rw [eqsel] at z
  simpa only [bank,packetCost,Series.tab,List.length_map,List.map_map,Function.comp_def,costSum,
    packet,Task.forest_map,id_eq,S,D, Nat.add_assoc] using z

end InterchangeROMRepair.SweepBank

end NearSquareRoot
end Computability
end OAI
