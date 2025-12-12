import Mathlib.Data.Set.basic
/-
Property of a set:

Set α → Prop
would equal
(α → Prop) → Prop
-/
def isEmpty : Set α → Prop := fun s => s = ∅
def isEmpty' : Set α → Prop := fun a => a → False

#reduce isEmpty
#reduce isEmpty'

def hasThree : Set Nat → Prop := fun s => 3 ∈ s

def hasTwoTrhee : Set Nat → Prop :=
  fun s => {2,3} ⊆ s

#reduce (types := true) hasThree {1,4}

example : hasThree {1,2,3} :=
  by
  unfold hasThree
  right
  right
  rfl

example : ¬ hasThree {1,2} := by
  intro h
  nomatch h


/-
single valued relation
each value from one set is only connected
to one value on the other
ex. each person only has one age
    the graph x = y

example of non-single valued relation
  graph of a circle

single valued relations are FUNCTIONS!!

something is a function if it satisfies the
vertical line test.

r: Rel Person → Nat(age)
p : Person, n1 n2 : Nat
(p, n1) ∈ r  (p, n2) ∈ r => n1 = n2
-/

inductive Person where
|Mary
|Bob
|Ella
open Person

inductive ageOf : Person → Nat → Prop
|m22 : ageOf Mary 22
|b51 : ageOf Bob 51

open ageOf
def Rel (α β : Type) := α → β → Prop

def singleValued {α β : Type} : Rel α β → Prop :=
  fun r =>
    ∀ a : α, ∀ b1 b2 : β,
      r a b1 ∧ r a b2 → b1 = b2

example : singleValued ageOf := by
  unfold singleValued
  intro p n1 n2 ⟨pa1, pa2⟩
  rcases p
  repeat {
    rcases pa1
    rcases pa2
    rfl
  }
  nomatch pa1

/-
injective relations  each output can be gotten from one input
gotten using horizontal line test
ex. SSN's
-/

def inj {α β : Type} : Rel α β → Prop :=
  fun r =>
    ∀ a1 a2 : α, ∀ b: β,
    r a1 b ∧ r a2 b → a1 = a2

/-
Domain of definition of r : the set
domain : the numbers talked about in the set
range: numbers in output in the set
codomain : all possible output set
surjective: if all inputs and outputs in the relation
-/
