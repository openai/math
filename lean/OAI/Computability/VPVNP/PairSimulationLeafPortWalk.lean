import OAI.Computability.VPVNP.PairSimulationLeafPortLoad

/-!
# Filling the validator's fixed scalar-port list in a single private call

The scalar pass visits each port exactly once. The caller can reuse its
private arena at the next leaf. The incident port remains available for
the separate copy from the four half-wire buffers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRegisterBank

open BurstRAM PrivateRAM RAMTape LeafStartup StackMachine PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {K : Type} [DecidableEq K] {d e w k p r pubs N : ℕ}
  (tag : K → Field k) (x : VirtualSite.Input d e w) (args : Fin k → Word w)

/-- The completed scalar stack contents of each port, obtained by encoding its field for the
given site and operands. -/
def scalarBank : Stacks K := fun a => fieldBits x args (scalarField (tag a))

/-- The intermediate scalar bank with the unvisited ports empty and the visited ports holding
their completed fields. -/
def pending (todo : List K) : Stacks K := fun a => if a ∈ todo then [] else scalarBank tag x args a

/-- The instruction count to stage one port's scalar field and run the six-row fill loop for
its bits. -/
def ticks (a : K) := (Staging.code (scalarField (tag a))).length + (6*(scalarBank tag x args a).length+1)

/-- Program labels for each port's field-specific staging sequence, including the index used
for its continuation. -/
abbrev StageLabels (tag : K → Field k) (p : ℕ) :=
  (a : K) → Fin ((Staging.code (scalarField (tag a))).length+1) → Fin p

/-- The first staging label of the next port to fill, or the exit label once the traversal list
is empty. -/
def first (label : StageLabels tag p) (done : Fin p) (todo : List K) :=
  todo.head?.elim done fun a => label a 0

variable (M : Machine w p r pubs) (reg : Reg K k ↪ Fin r) (L : Layout K w)
  (stages : StageLabels tag p) (fills : K → Fin 6 → Fin p) (done : Fin p)

/-- The host machine implements each port's field-specific staging and fill rows, with
continuations that visit the list in order. -/
def ScalarRows : List K → Prop
  | [] => True
  | a::rest =>
    let f := scalarField (tag a)
    stages a (Fin.last (Staging.code f).length) = fills a 0 ∧
      (∀ i : Fin (Staging.code f).length, M.code (stages a i.castSucc) =
        Staging.instruction (stage reg) (stages a i.succ) (Staging.code f)[i]) ∧
      LeafScalarLoad.Linked M (mode f) (fills a) (LeafFill.fieldRegisters (load reg) a) (first tag stages done rest) ∧
      ScalarRows rest

theorem scalar_walk (todo : List K) (hn : todo.Nodup) (link : ScalarRows tag M reg stages fills done todo)
    (c : Config w p r) (hc : c.pc = first tag stages done todo)
    (rep : Represents L (stack reg) c (pending tag x args todo))
    (ready : Staging.Sources x args (c.reg ∘ stage reg)) (room : ∀ a, (scalarBank tag x args a).length ≤ L.capacity) :
    ∃ out, Prefix M c (List.replicate (todo.map (ticks tag x args)).sum .tick) out ∧ out.pc = done ∧
      Represents L (stack reg) out (scalarBank tag x args) ∧ Staging.Sources x args (out.reg ∘ stage reg) ∧
      out.persistent = c.persistent ∧ (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      ∀ u, (∀ a ∈ todo, u.val < L.base a ∨ L.base a+(scalarBank tag x args a).length ≤ u.val) →
        out.privateMem u = c.privateMem u := by
  induction todo generalizing c with
  | nil =>
    have hbank : pending tag x args [] = scalarBank tag x args := by funext i; simp [pending]
    exact ⟨c,.nil _,hc,hbank ▸ rep,ready,rfl,fun _ _ => rfl,fun _ _ => rfl⟩
  | cons a rest ih =>
    have nodup := List.nodup_cons.mp hn
    obtain ⟨hj,hs,hf,hrest⟩ := link
    have fit (j : K) : ((pending tag x args (a::rest)) j).length ≤ L.capacity := by
      by_cases h : j ∈ a::rest <;> simp [pending, h, room]
    obtain ⟨mid,head,atPC,rep',ready',state,regs,mem⟩ := scalar_run x args (scalarField (tag a))
      (scalarField_ne _) M reg L a (stages a) (fills a) _ hj hs hf c hc (pending tag x args (a::rest))
      rep ready (by simp [pending]) fit (room a)
    have eq : Function.update (pending tag x args (a::rest)) a (scalarBank tag x args a) =
        pending tag x args rest := by
      funext i
      by_cases hi : i = a
      · subst i; simp [pending,nodup.1]
      · simp [pending,hi]
    change Represents L (stack reg) mid (Function.update _ a (scalarBank tag x args a)) at rep'
    obtain ⟨out,tail,hd,rep'',rdy'',pst,fr,unchanged⟩ := ih nodup.2 hrest mid atPC (eq ▸ rep') ready'
    have run := head.append tail
    rw [← List.replicate_add] at run
    exact ⟨out,run,hd,rep'',rdy'',pst.trans state,fun i hi => (fr i hi).trans (regs i hi),
      fun u hu => (unchanged u (fun j hj => hu j (List.mem_cons_of_mem _ hj))).trans (mem u (hu a (List.mem_cons_self ..)))⟩

/-- Scalar input registers furnished by the enclosing private call. -/
def sourceWord (x : VirtualSite.Input d e w) (args : Fin k → Word w) : Source k → Word w
  | .d => (d : Word w)
  | .width => (w : Word w)
  | .bucket => ((2^e : ℕ) : Word w)
  | .fuel => (x.fuel : Word w)
  | .address => x.addrWord
  | .initial => x.initialWord
  | .header => x.headerWord
  | .operand i => args i

/-- The deterministic pointer and scalar tables are consecutive subprograms
of the same native RAM. No pre-initialized stack bank is required. -/
theorem scalar_startup (order : Fin N ≃ K) (base : ℕ) (hlayout : ∀ i, L.base (order i) = base+i.val*L.capacity)
    (allocPC : K → Fin 3 → Fin p) (endPC : Fin 2 → Fin p)
    (allocation : LeafPointers.Rows M (LeafFill.pointers (load reg)) allocPC (endPC 0) (List.ofFn order))
    (finish : ∀ i, M.code (endPC i) = LeafPointers.finish endPC (LeafFill.pointers (load reg))
      (first tag stages done (List.ofFn order)) i)
    (rows : ScalarRows tag M reg stages fills done (List.ofFn order)) (c : Config w p r)
    (hc : c.pc = LeafPointers.next (List.ofFn order) allocPC (endPC 0))
    (hbase : c.reg (LeafFill.pointers (load reg) .cursor) = (base : Word w))
    (hstride : c.reg (LeafFill.pointers (load reg) .stride) = (L.capacity : Word w))
    (inputs : ∀ j, c.reg (reg (.inr j)) = sourceWord x args j) (room : ∀ a, (scalarBank tag x args a).length ≤ L.capacity) :
    ∃ out, Prefix M c (List.replicate (3*N+2+((List.ofFn order).map (ticks tag x args)).sum) .tick) out ∧
      out.pc = done ∧ Represents L (stack reg) out (scalarBank tag x args) ∧
      Staging.Sources x args (out.reg ∘ stage reg) ∧ out.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      ∀ u, (∀ a, u.val < L.base a ∨ L.base a+(scalarBank tag x args a).length ≤ u.val) →
        out.privateMem u = c.privateMem u := by
  obtain ⟨mid,allocated,atPC,empty,memory,state,frame⟩ := LeafPointers.initialize_pointers M
    (LeafFill.pointers (load reg)) L order base hlayout allocPC endPC _ allocation finish c hc hbase hstride
  have loaded (j : Source k) : mid.reg (reg (.inr j)) = sourceWord x args j :=
    (frame _ (by rintro ⟨i,he⟩; simp at he)).trans (inputs j)
  have rdy : Staging.Sources x args (mid.reg ∘ stage reg) :=
    ⟨empty.zero,empty.unit,loaded .d,loaded .width,loaded .bucket,loaded .fuel,loaded .address,
      loaded .initial,loaded .header,fun i => loaded (.operand i)⟩
  have bank0 : pending tag x args (List.ofFn order) = fun _ => [] := by
    funext a
    simp [pending, List.mem_ofFn, order.surjective a]
  obtain ⟨out,filled,hd,rep,rdy',pst,regs,mem⟩ := scalar_walk tag x args M reg L stages fills done
    _ (List.nodup_ofFn.mpr order.injective) rows mid atPC (bank0 ▸ empty) rdy room
  have run := allocated.append filled
  rw [← List.replicate_add] at run
  refine ⟨out,run,hd,rep,rdy',pst.trans state,?_,?_⟩
  · intro i hi
    exact (regs i hi).trans (frame i (fun ⟨j,hj⟩ => hi ⟨_,hj⟩))
  · intro u hu
    exact (mem u (fun a _ => hu a)).trans (congrFun memory u)

end PairSimulation.LeafRegisterBank

end VPVNP
end Computability
end OAI
