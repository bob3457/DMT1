import Mathlib.Data.Set.basic
inductive Person : Type where
|Mary
|Bob
|Ella
open Person

inductive Nice : Person → Prop
|mn : Nice Mary
open Nice

def nicePeople  : Set Person :=
  {p : Person | Nice p}

example : Mary ∈ nicePeople := mn

example : Nice Mary := mn

example : Bob ∉ nicePeople := by
  intro h
  nomatch h


def s : Set Nat := {1,2}
#reduce s

def t : Set Nat := {1,2,3}

example : s ⊆ t := by
  unfold s t
  intro n ns
  cases ns
  apply Or.inl
  assumption
  apply Or.inr
  apply Or.inl
  assumption

--example s ⊊ t := by
  --apply And.intro
  --top proof for first part
  --proof that there exists a obj in t that
  --doesn't exist in s

/-
product set = all ordered pairs

powerset - all subsets
size 2^n
-/


