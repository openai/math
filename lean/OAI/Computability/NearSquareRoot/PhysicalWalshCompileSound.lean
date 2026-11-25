import OAI.Computability.NearSquareRoot.PhysicalWalshCompile
import OAI.Computability.NearSquareRoot.KernelPassComputableEncode
import OAI.Computability.NearSquareRoot.KernelPassComputableRelation

/-! # Correctness of the exact command emitted by the prefix compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space PhysicalWalsh KernelPass KernelPass.ComputableSyntax

variable {X U H R : Type} {m : Meter U} [Codec H] [Codec R] {l : Layout U H R} {u : X → U}

private theorem Scans.atInput {S T : Type} [Codec S] [Codec T] {c : Cmd} {f : S → T}
    (h : Scans c f) (a : X → S) (D : ℕ) (hd : ∀ x, size (a x) ≤ D*(m.arena (u x)+1)) :
    Runs c m 0 u (fun x => send (a x)) (fun x => send (f (a x))) := by
  obtain ⟨C,h⟩ := h
  refine ⟨C*(D+1),fun x env t s _ p b hp => ?_⟩
  have hr : size (a x)+1 ≤ (D+1)*(m.arena (u x)+1) := by rw [Nat.succ_mul]; have := hd x; omega
  have hw := Nat.mul_le_mul_left C hr
  rw [← Nat.mul_assoc] at hw
  have ht := hw.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (m.arena_le _)))
  exact (h (a x) env p b hp).mono (by simpa using ht) (by omega) (by omega)

private theorem runParallel {b : BankCode} (ok : BankOK b H R) (fit : FitsLayout m l)
    {i j o v n n' : ℕ} {c d : Cmd} (x : ∀ k, Rows l (u k) (i+j))
    (y : ∀ k, Rows l (u k) o) (z : ∀ k, Rows l (u k) v)
    (hl : Runs c m n u (fun k => send (packet l (u k) fun a => x k (a.castAdd j)))
      (fun k => send (packet l (u k) (y k))))
    (hr : Runs d m n' u (fun k => send (packet l (u k) fun a => x k (a.natAdd i)))
      (fun k => send (packet l (u k) (z k)))) :
    Runs (b.parallel i c d) m (n+n') u (fun k => send (packet l (u k) (x k)))
      (fun k => send (packet l (u k) (Fin.append (y k) (z k)))) := by
  let rightInput (t : X) : Rows l (u t) j := fun a => x t (a.natAdd i)
  have split := (ok.split i).atInput (fun k => packet l (u k) (x k)) _ (fun k => fit.packet _ _)
  simp only [split_packet,send_prod] at split
  have leftRun := hl.left (fun k => send (packet l (u k) (rightInput k))) _ (fun k => fit.packet _ _)
  have swap := ok.swap.atInput (fun k => (packet l (u k) (y k),packet l (u k) (rightInput k))) _
    (fun k => fit.both _ _ _)
  have rightRun := hr.left (fun k => send (packet l (u k) (y k))) _ (fun k => fit.packet _ _)
  have finish := ok.finish.atInput (fun k => (packet l (u k) (z k),packet l (u k) (y k))) _
    (fun k => fit.both _ _ _)
  simp only [Prod.swap_prod_mk,combine_packet,send_prod] at swap finish
  simpa only [Nat.zero_add,Nat.add_zero,send_prod,BankCode.parallel,left] using
    (((split.seq leftRun).seq swap).seq (rightRun.seq finish))

/-- Correctness for the actual reached inputs of a decoded plan, including its
range guard and its exact coefficient of the child execution time. -/
def Implements {A : ℕ} (f : Ops A l) (G : Guards A l) (m : Meter U) (u : X → U)
    (p : Packed A) (cmd : Cmd) : Prop := ∀ x : ∀ t, Rows l (u t) p.i,
    (∀ t, Ready f G p.plan (u t) (x t)) →
    Runs cmd m p.plan.calls u (fun t => send (packet l (u t) (x t)))
      (fun t => send (packet l (u t) (f.applyPlan p.plan (u t) (x t))))

/-- Empty and malformed serial plans operate on an empty bank. -/
theorem empty_sound {A : ℕ} (f : Ops A l) (G : Guards A l) (u : X → U) (fit : FitsLayout m l) :
    Implements f G m u (Packed.empty A) .pass := by
  intro x _
  refine ⟨3,fun t env c s _ parked base hp => ?_⟩
  have he : f.applyPlan (Packed.empty A).plan (u t) (x t) = x t := by
    funext k
    exact Fin.elim0 k
  dsimp only
  rw [he]
  have bound := fit.packet (u t) (x t)
  change (send (packet l (u t) (x t))).count ≤ 3*(m.arena (u t)+1) at bound
  apply (BoundedFits.pass (env := env) ((hp.pile 0 (send (packet l (u t) (x t)))).mono
    (by omega : base + _ ≤ base + (3*(m.arena (u t)+1)+s)))).mono _ le_rfl le_rfl
  change 1 ≤ 3*(m.scan (u t)+1)+0*c
  omega

/-- The very command returned by `command` realizes the certified typed
decoding for every raw input, including programs with invalid widths. -/
theorem command_sound {A : ℕ} (f : Ops A l) (G : Guards A l) (u : X → U) (fit : FitsLayout m l)
    (b : BankCode) (ok : BankOK b H R) (zero : Cmd) (leaf : ℕ → Op → Cmd)
    (emptyOK : Implements f G m u (Packed.empty A) zero)
    (leafOK : ∀ op, Implements f G m u (Packed.leaf A op) (leaf A op)) (ops : List Op) :
    Implements f G m u (Packed.decode A ops) (command b zero leaf A ops) := by
  let Rel (p : Packed A) (v : Shape × Cmd) := p.shape = v.1 ∧ Implements f G m u p v.2
  apply (Algebra.parse_rel (a := Packed.algebra A) (b := algebra A zero (leaf A) Prog.join b.parallel) Rel
    ⟨rfl,emptyOK⟩ (fun op => ⟨Packed.leaf_shape A op,leafOK op⟩) ?_ ?_ ops).2
  · rintro ⟨i,o,p⟩ ⟨k,j,q⟩ ⟨sp,cp⟩ ⟨sq,cq⟩ ⟨rfl,hp⟩ ⟨rfl,hq⟩
    constructor
    · exact Packed.seq_shape _ _
    · by_cases h : j = i
      · subst i
        simp [algebra,Packed.algebra,Packed.seq,Packed.shape]
        intro x ready
        have first := hq x fun t => (ready t).1
        have second := hp (fun t => f.applyPlan q _ (x t)) fun t => (ready t).2
        simpa only [Plan.calls,Ops.applyPlan,Nat.add_comm p.calls q.calls] using first.seq second
      · simpa [algebra,Packed.algebra,Packed.seq,Packed.shape,h] using emptyOK
  · rintro ⟨i,o,p⟩ ⟨j,v,q⟩ ⟨sp,cp⟩ ⟨sq,cq⟩ ⟨rfl,hp⟩ ⟨rfl,hq⟩
    refine ⟨rfl,?_⟩
    intro x ready
    exact runParallel ok fit x _ _ (hp _ (fun t => (ready t).1)) (hq _ (fun t => (ready t).2))

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
