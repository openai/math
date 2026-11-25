import OAI.ThreeFlat.Diagonal.LaneBucketAddresses
import OAI.ThreeFlat.Diagonal.LaneCursorPorts
import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Equality rows at a lane cursor relay vertex -/

namespace ThreeFlat.Diagonal.LaneCursor.RelayNetwork

open TraceCircuit
open scoped BigOperators Classical

variable {F O D : Type*} [CommSemiring F] {r k t : ℕ}

private abbrev arcs (r : ℕ) := (r+1)*2

variable (ord : Fin t ≃ O × D) (mask : O → Lane (k+1)) (i : Fin (k+1))

def pins (send recv : PortFields r O D) : Fin (arcs r*t+arcs r*t) → Bool :=
  Fin.append (blocks _ _ (fun s a => send s (ord a))) (blocks _ _ (fun s a => recv s (ord a)))

private def outPin (s : Fin (arcs r)) (a : Fin t) : BitSource 0 (arcs r*t+arcs r*t) :=
  .pin ((finProdFinEquiv (s,a)).castAdd _)

private def inPin (s : Fin (arcs r)) (a : Fin t) : BitSource 0 (arcs r*t+arcs r*t) :=
  .pin (Fin.natAdd _ (finProdFinEquiv (s,a)))

@[simp] private theorem read_out (send recv : PortFields r O D) (g : Fin 0 → Bool)
    (s : Fin (arcs r)) (a : Fin t) :
    (outPin s a).read g (pins ord send recv)=send s (ord a) := by
  simp only [outPin,BitSource.read,pins,Fin.append_left,blocks_at]

@[simp] private theorem read_in (send recv : PortFields r O D) (g : Fin 0 → Bool)
    (s : Fin (arcs r)) (a : Fin t) :
    (inPin s a).read g (pins ord send recv)=recv s (ord a) := by
  simp only [inPin,BitSource.read,pins,Fin.append_right,blocks_at]

private def prev (i : Fin (k+1)) : Fin (k+1) := ⟨i.val-1,by omega⟩

private def holes (z : Fin (arcs r*t)) : Fin 3 → BitSource 0 (arcs r*t+arcs r*t) :=
  let a : Fin (arcs r) × Fin t := finProdFinEquiv.symm z
  let s := outPin a.1 a.2
  ![s,if a.1 = selected mask (ord a.2).1 i then s else .constant false,.constant false]

private def forwards (a : Fin t) : Fin 3 → BitSource 0 (arcs r*t+arcs r*t) :=
  let out := outPin (selected mask (ord a).1 i) a
  ![out,if i = 0 then out else inPin (selected mask (ord a).1 (prev i)) a,.constant false]

def network : BitNetwork F (arcs r*t+arcs r*t) where
  internal := 0
  cells := arcs r*t+t
  source := Fin.append (holes ord mask i) (forwards ord mask i)
  table := fun _ z => if z 0 = z 1 then 1 else 0

private theorem ok_iff (send recv : PortFields r O D) :
    PortChecks mask i send recv ↔
      (∀ s a, s ≠ selected mask (ord a).1 i → send s (ord a) = false) ∧
      (∀ a, i ≠ 0 → send (selected mask (ord a).1 i) (ord a) = recv (selected mask (ord a).1 (prev i)) (ord a)) := by
  constructor
  · rintro ⟨unused,pass⟩
    refine ⟨fun s a => unused s _,fun a nz => pass _ ?_ _⟩
    have : i.val ≠ 0 := fun e => nz (Fin.ext e)
    change i.val = i.val-1+1
    omega
  · rintro ⟨unused,pass⟩
    constructor
    · intro s a
      obtain ⟨x,rfl⟩ := ord.surjective a
      exact unused s x
    · intro j eq a
      obtain ⟨x,rfl⟩ := ord.surjective a
      have hp : prev i = j := Fin.ext (by change i.val-1=j.val; omega)
      have nz : i ≠ 0 := by intro hz; rw [hz] at eq; simp at eq
      simpa [hp] using pass x nz

private theorem factor_all (send recv : PortFields r O D) (g : Fin 0 → Bool) :
    (∀ c : Fin ((arcs r)*t+t), let args := fun j => ((network (F:=F) ord mask i).source c j).read g (pins ord send recv)
      args 0 = args 1) ↔ PortChecks mask i send recv := by
  rw [ok_iff ord mask i]
  simp only [network,Fin.forall_fin_add,Fin.append_left,Fin.append_right]
  constructor
  · rintro ⟨a,b⟩
    constructor
    · intro s j neq
      simpa [holes,neq,outPin,BitSource.read,pins,Fin.append_left,blocks_at] using a (finProdFinEquiv (s,j))
    · intro j nz
      simpa [forwards,nz] using b j
  · rintro ⟨a,b⟩
    constructor
    · intro z
      obtain ⟨⟨s,j⟩,rfl⟩ := finProdFinEquiv.surjective z
      by_cases eq : s = selected mask (ord j).1 i
      · simp [holes,eq]
      · simpa [holes,eq,outPin,BitSource.read,pins,Fin.append_left,blocks_at] using a s j eq
    · intro j
      by_cases eq : i = 0
      · simp [forwards,eq]
      · simpa [forwards,eq] using b j eq

/-- All unused outgoing bits are forced to zero. A noninitial layer equates
exactly its selected pair. The row count and addressing are rectangular. -/
theorem eval (send recv : PortFields r O D) :
    (network (F:=F) ord mask i).eval (pins ord send recv) = if PortChecks mask i send recv then 1 else 0 := by
  let args (g : Fin 0 → Bool) (c : Fin ((arcs r)*t+t)) (j : Fin 3) :=
    (Fin.append (holes ord mask i) (forwards ord mask i) c j).read g (pins ord send recv)
  change (∑ g : Fin 0 → Bool, ∏ c, if args g c 0=args g c 1 then (1:F) else 0)=_
  have product (g : Fin 0 → Bool) :
      (∏ c, if args g c 0=args g c 1 then (1:F) else 0) = if PortChecks mask i send recv then 1 else 0 := by
    by_cases ok : PortChecks mask i send recv
    · have a := (factor_all (F:=F) ord mask i send recv g).2 ok
      simp [ok,show ∀ c, args g c 0 = args g c 1 from a]
    · obtain ⟨c,hc⟩ := not_forall.mp (fun h => ok ((factor_all (F:=F) ord mask i send recv g).1 h))
      rw [ite_eq_right ok]
      exact Finset.prod_eq_zero (Finset.mem_univ c) (ite_eq_right hc)
  rw [Fintype.sum_unique]
  exact product _

end ThreeFlat.Diagonal.LaneCursor.RelayNetwork

end OAI
