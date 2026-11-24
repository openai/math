import OAI.Computability.VPVNP.RAMTapeAddressLogControl

/-!
# Prepending a private RAM write

The forward pass transfers the address and value to two scratch stacks. The
return pass restores the input words and pushes a copy of each bit onto the
corresponding log stream, low bit first in the completed log. A final marker
records the entry, including when both words have width zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.AddressLog

open BurstRAM BurstRAM.PrivateRAM

/-- States for saving the new address and value, restoring their input stacks, and prepending
the write to the log. -/
inductive StoreState where
  | readKey | readValue (k : Bool) | saveKey (k v : Bool) | saveValue (v : Bool)
  | restore | popValue (k : Bool) | restoreKey (k v : Bool) | restoreValue (k v : Bool)
  | pushKey (k v : Bool) | pushValue (v : Bool) | mark | done | reject
  deriving DecidableEq, Fintype

/-- Stack instructions that prepend the address and value to the log and push an occupancy
mark, including for zero-width words. -/
def storeCode : StackCode Port StoreState
  | .readKey => .pop .query fun | none => .restore | some k => .readValue k
  | .readValue k => .pop .out fun | none => .reject | some v => .saveKey k v
  | .saveKey k v => .push .keySave k (.saveValue v)
  | .saveValue v => .push .valueSave v .readKey
  | .restore => .pop .keySave fun | none => .mark | some k => .popValue k
  | .popValue k => .pop .valueSave fun | none => .reject | some v => .restoreKey k v
  | .restoreKey k v => .push .query k (.restoreValue k v)
  | .restoreValue k v => .push .out v (.pushKey k v)
  | .pushKey k v => .push .keys k (.pushValue v)
  | .pushValue v => .push .values v .restore
  | .mark => .push .occupied true .done
  | .done => .halt true
  | .reject => .halt false

private abbrev StoreRun (n : ℕ) (q : StoreState) (s : Bank) (q' : StoreState) (t : Bank) :=
  StackRuns storeCode n q s.stacks q' t.stacks

local macro "store_step" : tactic => `(tactic|
  first | refine StackRuns.cons (stepPop _ rfl) ?_ | refine StackRuns.cons (stepPush _ rfl) ?_)

private theorem save_run (s : Bank) (q o sk sv : List Bool) (hlen : o.length = q.length) :
    StoreRun (4 * q.length + 1) .readKey {s with q, o, sk, sv}
      .restore {s with q := [], o := [], sk := q.reverse ++ sk, sv := o.reverse ++ sv} := by
  induction q generalizing o sk sv with
  | nil =>
    obtain rfl : o = [] := List.length_eq_zero_iff.mp hlen
    store_step
    exact .nil ..
  | cons k q ih =>
    cases o with
    | nil => simp at hlen
    | cons v o =>
      simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
      store_step
      store_step
      store_step
      store_step
      exact ih o (k :: sk) (v :: sv) (Nat.succ.inj hlen)

private theorem restore_run (s : Bank) (sk sv q o ks vs : List Bool) (hlen : sv.length = sk.length) :
    StoreRun (6 * sk.length + 2) .restore {s with q, o, sk, sv, ks, vs}
      .done {s with
        q := sk.reverse ++ q, o := sv.reverse ++ o, ks := sk.reverse ++ ks,
        vs := sv.reverse ++ vs, marks := true :: s.marks, sk := [], sv := []} := by
  induction sk generalizing sv q o ks vs with
  | nil =>
    obtain rfl : sv = [] := List.length_eq_zero_iff.mp hlen
    store_step
    store_step
    exact .nil ..
  | cons k sk ih =>
    cases sv with
    | nil => simp at hlen
    | cons v sv =>
      simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
      store_step
      store_step
      store_step
      store_step
      store_step
      store_step
      exact ih sv (k :: q) (v :: o) (k :: ks) (v :: vs) (Nat.succ.inj hlen)

/-- A private store preserves the source words and realizes exactly one cons
of the native newest-first `WriteLog`, in a number of steps independent of
its previous length and of the numerical address. -/
theorem store_run {w : ℕ} (a v : Word w) (log : WriteLog w) :
    StackRuns storeCode (10 * w + 3) .readKey (bank a (wordBits v) log).stacks
      .done (bank a (wordBits v) ((a, v) :: log)).stacks := by
  let s := bank a (wordBits v) log
  have hf := save_run s (wordBits a) (wordBits v) [] [] (by simp)
  have hr := restore_run s (wordBits a).reverse (wordBits v).reverse [] [] (keys log) (values log) (by simp)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, length_wordBits] at hf hr
  have run := hf.trans hr
  rw [show (4 * w + 1) + (6 * w + 2) = 10 * w + 3 by omega] at run
  simpa only [s, bank, keys, values, List.flatMap_cons, List.length_cons, List.replicate_succ] using run

end RAMTape.AddressLog

end VPVNP
end Computability
end OAI
