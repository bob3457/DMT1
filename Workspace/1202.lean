/-
sets are made of the same types are the only sets
talked about in this class, called homogenous sets

notation for empty set is 0 with slash through it

universal set includes all possible types

membership determines if in a certain set, notation
for 2 in universal set is 2 ε univ

!!sets are written as predicates!!

Set of all even numbers:
fun n=> n%2 = 0

Set of number from 0-9 inclusive
fun n=>  (n >=0) ∧ (n <= 9)

Set of all numbers, or the universal set
fun n=> True


Set of no numbers, or the empty set
fun n=> False
-/

--Math library
import Mathlib.Data.Set.Basic

def oneTwoTrhee : Set Nat :=
  fun n=> n=1 ∨ n=2 ∨ n=3

def fewNats' : Set Nat := {1, 2, 3}

#reduce fewNats'
example : fewNats' 3 := by
  unfold fewNats'
  apply Or.inr
  apply Or.inr
  rfl



example : ¬(fewNats' 5) := by
  intro h
  --after this just means 5=1 ∨ 5=2 ∨ 5=3 which is false
  unfold fewNats' at h
  nomatch h

def isEven : Nat → Prop := fun n => n%2 = 0

def theEvens: Set Nat := fun n => isEven n

def isInEvens (n : Nat) : n ∈ theEvens := by
  unfold theEvens
  rfl



/-
intersection of sets using ∩
means the intersection of elements within the two sets
if you have 1,2,3 and 3,4,5, the intersect would be 3


union of sets
-/
