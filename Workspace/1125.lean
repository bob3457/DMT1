/-
The output type for every input value is different based
on the input for predicates

"cases" tactic that means match p with ...
-/

inductive Person
|Mary
|Bob
|Etta

#check Person.rec
#check String.rec

#check Nat.rec

/-
Nat.rec.{u}
{motive : Nat → Sort u}
(zero : motive Nat.zero)
(succ : (n : Nat) → motive n → motive n.succ)
(t : Nat) :
  motive t
-/

/-
sum all number 0 to n = n* (n+1)/2
-/

def sumup : Nat → Nat
|Nat.zero => 0
|Nat.succ n' => (Nat.succ n') + sumup n'

#reduce sumup 5

def P' (n : Nat) : Prop := sumup n = n* (n+1) /2
def P (n: Nat) : Prop := 2 * sumup n = n * (n+1)

/-
Prove (∀ n : Nat, P n)

proof is by inudction, need to define
answers for two situations:

1. if argument is 0, need a proof of zero

2. for any other number, a proof of that
number -1 and that you can get to that number
-/

def sumToNZero : sumup 0 = 0 := rfl

--def step : (n : Nat) → P n → P n.succ :=
--  fun n pn => _

def sumToNStep : ∀ (n : Nat), (h : P n) → P n.succ := by
  intro n
  intro pn
  unfold P
  unfold P at pn
  rw [Nat.mul_add]
