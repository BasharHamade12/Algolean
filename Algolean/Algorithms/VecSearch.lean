/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Algolean.Models.ReadOnlyVec
public import Batteries.Data.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.Set

@[expose] public section

/-!
# Linear search and Binary Search in Fin vectors

In this file we state and prove the correctness and complexity of linear search in lists under
the `ReadOnlyVec` model.
--

## Main Definitions

- `vecLinearSearch` : Linear search algorithm in the `ReadOnlyVec` query model
- `vecBinarySearch` : Binary search algorithm in the `ReadOnlyVec` query model

## Main results

- `vecLinearSearch_eval`: `vecLinearSearch` evaluates identically to `List.contains`.
- `listLinearSearchM_time_complexity_upper_bound` : `linearSearch` takes at most `n`
  comparison operations
- `listLinearSearchM_time_complexity_lower_bound` : There exist lists on which `linearSearch` needs
  `n` comparisons
-/
namespace Algolean

namespace Algorithms

open Cslib Prog

section LinearSearch

open ReadOnlyVec in
/-- Linear Search in Lists on top of the `ListSearch` query model. -/
@[simp, grind]
def vecLinearSearch [BEq α] (v : Vector α n) (x : α) : Prog (ReadOnlyVec α) Bool := do
  match n with
  | 0 => return false
  | _ + 1 =>
    let topElem : α ← read v 0
    if topElem == x then
      return true
    else
      vecLinearSearch (v.tail) x

lemma Vector.extract_mem (v : Vector α n) (start stop : Nat)
  (x : α) (h : x ∈ v.extract start stop) : x ∈ v := by
  exact (Vector.mem_toList_iff).1 <|
    List.mem_of_mem_drop <|
      List.mem_of_mem_take <|
        by simpa [Vector.toList_extract] using (Vector.mem_toList_iff).2 h

lemma Vector.extract_begin (v : Vector α n) (hn_pos : n > 0)
    (x : α) (h : x ∈ v) (hnorfirst : v[0] ≠ x) : x ∈ v.extract 1 := by
  have hcons : v.toList = v[0] :: v.toList.tail := by
    simpa using (List.drop_eq_getElem_cons (l := v.toList) (i := 0) (by simpa using hn_pos))
  have htake : (v.toList.tail).take (n - 1) = v.toList.tail := by
    apply List.take_of_length_le
    simp
  exact (Vector.mem_toList_iff).1 <|
    by
      simpa [Vector.toList_extract, htake] using
        (List.mem_of_ne_of_mem
          (by simpa [eq_comm] using hnorfirst)
          (hcons ▸ (Vector.mem_toList_iff).2 h))
@[simp, grind .]
lemma vecLinearSearch_eval [BEq α] [LawfulBEq α] (v : Vector α n) (x : α) :
    ((vecLinearSearch v x).eval ReadOnlyVec.natCost) = (x ∈ v) := by
  fun_induction vecLinearSearch with
  | case1 v =>
      simp_all [Vector.eq_empty (xs := v)]
  | case2 n v ih =>
    simp_all only [Vector.tail_eq_cast_extract, Nat.add_one_sub_one, Vector.mem_cast, eq_iff_iff,
      FreeM.lift_def, FreeM.pure_eq_pure, Cslib.FreeM.bind_eq_bind, FreeM.liftBind_bind,
      FreeM.pure_bind, eval_liftBind, ReadOnlyVec.natCost_evalQuery, Fin.getElem_fin,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, beq_iff_eq, Nat.succ_eq_add_one]
    split_ifs with h₀
    · grind
    · simp_all only [beq_iff_eq]
      constructor
      · intro hx
        exact Vector.extract_mem (v := v) (start := 1) (stop := n + 1) x (by simpa using hx)
      · intro hx
        exact Vector.extract_begin v (by simp) x hx (by simpa [eq_comm] using h₀)

lemma listLinearSearchM_correct_true [BEq α] [LawfulBEq α] (v : Vector α n)
    {x : α} (x_mem_l : x ∈ v) : (vecLinearSearch v x).eval ReadOnlyVec.natCost = true := by
  rwa [vecLinearSearch_eval]

lemma listLinearSearchM_correct_false [BEq α] [LawfulBEq α] (v : Vector α n)
    {x : α} (x_mem_l : x ∉ v) : (vecLinearSearch v x).eval ReadOnlyVec.natCost = false := by
  apply Bool.eq_false_iff.mpr
  intro hx
  exact x_mem_l (by simpa [vecLinearSearch_eval v x] using hx)

lemma listLinearSearchM_time_complexity_upper_bound [BEq α] (v : Vector α n) (x : α) :
    (vecLinearSearch v x).time ReadOnlyVec.natCost ≤ n := by
  fun_induction vecLinearSearch
  · simp
  · simp
    split_ifs
    · simp
    · simp_all
      linarith

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [Nontrivial α] (n : ℕ) :
    ∃ (v : Vector α n) (x : α), (vecLinearSearch v x).time ReadOnlyVec.natCost = n := by
  obtain ⟨x, y, hneq⟩ := exists_pair_ne α
  use Vector.replicate n y, x
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [vecLinearSearch, FreeM.lift_def, FreeM.pure_eq_pure, Nat.add_one_sub_one,
        Vector.tail_eq_cast_extract, Vector.extract_replicate, Cslib.FreeM.bind_eq_bind,
        FreeM.liftBind_bind, FreeM.pure_bind, time_liftBind, ReadOnlyVec.natCost_cost,
        ReadOnlyVec.natCost_evalQuery, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Vector.getElem_replicate, beq_iff_eq]
      split_ifs with heq
      · exfalso
        exact hneq heq.symm
      · simp_all
        have s₁ : min (n + 1) (n + 1) - 1 = n := by grind
        have hsucc :
            (vecLinearSearch (Vector.replicate n y) x).time ReadOnlyVec.natCost + 1 = n + 1 := by
          exact congrArg (fun t => t + 1) ih
        simpa [s₁, Vector.cast, Nat.add_comm] using hsucc

end LinearSearch

section BinarySearch

open ReadOnlyVec in
/-- Linear Search in Lists on top of the `ListSearch` query model. -/
@[grind]
def vecBinarySearch [BEq α] [LawfulBEq α] (le : α → α → Bool) (v : Vector α n) (x : α)
    : Prog (ReadOnlyVec α) Bool := do
  if h : n = 0 then return false
  else
    let mut mid : Fin n := ⟨n / 2, by grind⟩
    let midval : α ← read v mid
    if midval == x then
      return true
    else if le midval x then
      vecBinarySearch le (v.extract (mid + 1) n) x
    else
      vecBinarySearch le (v.extract 0 mid) x

@[simp, grind .]
private lemma list_mem_take_or_mem_drop {l : List α} {i : Nat} {x : α} (hx : x ∈ l) :
    x ∈ l.take i ∨ x ∈ l.drop i := by
  have hx' : x ∈ l.take i ++ l.drop i := by
    rw [List.take_append_drop]
    exact hx
  exact List.mem_append.mp hx'

@[simp, grind .]
private lemma list_mem_take_succ_cases {l : List α} {i : Nat} (hi : i < l.length) {x : α}
    (hx : x ∈ l.take (i + 1)) : x ∈ l.take i ∨ x = l[i] := by
  rw [List.take_succ_eq_append_getElem hi] at hx
  rcases (List.mem_append.mp hx) with hx | hx
  · exact Or.inl hx
  · exact Or.inr (List.mem_singleton.mp hx)

@[simp, grind .]
private lemma list_mem_drop_cases {l : List α} {i : Nat} (hi : i < l.length) {x : α}
    (hx : x ∈ l.drop i) : x = l[i] ∨ x ∈ l.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons hi] at hx
  exact List.mem_cons.mp hx

@[simp, grind .]
private lemma list_getElem_mem_drop {l : List α} {i : Nat} (hi : i < l.length) :
    l[i] ∈ l.drop i := by
  rw [List.drop_eq_getElem_cons hi]
  exact List.mem_cons.mpr (Or.inl rfl)

@[simp, grind .]
private lemma list_getElem_mem_take_succ {l : List α} {i : Nat} (hi : i < l.length) :
    l[i] ∈ l.take (i + 1) := by
  rw [List.take_succ_eq_append_getElem hi]
  exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

@[simp, grind .]
private lemma vector_mem_extract_from_drop {v : Vector α n} {i : Nat} {x : α}
    (hx : x ∈ v.toList.drop i) : x ∈ v.extract i := by
  have htake : (v.toList.drop i).take (n - i) = v.toList.drop i := by
    apply List.take_of_length_le
    simp
  exact (Vector.mem_toList_iff).1 <| by
    rw [Vector.toList_extract, htake]
    exact hx

@[simp, grind .]
private lemma vector_mem_extract_zero_of_take {v : Vector α n} {i : Nat} {x : α}
    (hx : x ∈ v.toList.take i) : x ∈ v.extract 0 i := by
  exact (Vector.mem_toList_iff).1 <| by
    simpa [Vector.toList_extract] using hx

@[simp, grind .]
private lemma vector_pairwise_extract (r : α → α → Prop) {v : Vector α n}
    (h : v.toList.Pairwise r) (start stop : Nat) : (v.extract start stop).toList.Pairwise r := by
  simpa [Vector.toList_extract] using
    (List.Pairwise.take (i := stop - start) (List.Pairwise.drop (i := start) h))

@[simp, grind .]
lemma vecBinarySearch_eval [BEq α] [LawfulBEq α] (le : α → α → Bool)
    [Std.Total (fun x y => le x y)] [IsTrans _ (fun x y => le x y)]
    [Std.Antisymm (fun x y => le x y)] (v : Vector α n)
    (hSorted : v.toList.Pairwise (fun x y => le x y))
    (x : α) :
    ((vecBinarySearch le v x).eval ReadOnlyVec.natCost) = (x ∈ v) := by
  fun_induction vecBinarySearch with
  | case1 v₀ =>
      simp_all [Vector.eq_empty (xs := v₀)]
  | case2 n v hneq0 mid ih2 ih1 =>
      have hmid_lt : (mid : Nat) < v.toList.length := by simp [mid.isLt]
      simp only [FreeM.bind_eq_bind, FreeM.lift_def, FreeM.liftBind_bind, FreeM.pure_bind,
        eval_liftBind, ReadOnlyVec.natCost_evalQuery]
      split_ifs with hEq hLe
      · apply propext
        constructor <;> intro
        · exact (by simpa [Fin.getElem_fin] using (LawfulBEq.eq_of_beq hEq).symm) ▸
            Vector.getElem_mem mid.isLt
        · trivial
      · rw [ih2 (vector_pairwise_extract (fun a b => le a b) hSorted (mid + 1) n)]
        have hmid_ne : v[mid] ≠ x := by
          simpa [beq_iff_eq] using hEq
        apply propext
        constructor
        · exact Vector.extract_mem v (mid + 1) n x
        · intro hx
          rcases list_mem_take_or_mem_drop ((Vector.mem_toList_iff).2 hx) with
              hxTake | hxDrop
          · rcases list_mem_take_succ_cases hmid_lt hxTake with (hxTakeMid | hxMid)
            · by_contra
              have hxm : le x v[mid] := List.Pairwise.rel_of_mem_take_of_mem_drop
                (R := fun a b => le a b) hSorted hxTakeMid (list_getElem_mem_drop hmid_lt)
              grind [Std.Antisymm.antisymm (r := fun a b => le a b)]
            · by_contra
              exact hmid_ne <| by
                simpa [eq_comm] using hxMid
          · exact vector_mem_extract_from_drop hxDrop
      · rw [ih1 (vector_pairwise_extract (fun a b => le a b) hSorted 0 (mid : Nat))]
        have hmid_ne : v[mid] ≠ x := by
          simpa [beq_iff_eq] using hEq
        apply propext
        constructor
        · exact Vector.extract_mem v 0 mid x
        · intro hx
          rcases list_mem_take_or_mem_drop ((Vector.mem_toList_iff).2 hx) with (hxTake | hxDrop)
          · exact vector_mem_extract_zero_of_take hxTake
          · rcases list_mem_drop_cases hmid_lt hxDrop with hxMid | hxDropSucc
            · by_contra
              exact hmid_ne hxMid.symm
            · by_contra
              apply hLe
              exact List.Pairwise.rel_of_mem_take_of_mem_drop (R := fun a b => le a b = true)
                hSorted (list_getElem_mem_take_succ hmid_lt) hxDropSucc
end BinarySearch
end Algorithms

end Algolean
