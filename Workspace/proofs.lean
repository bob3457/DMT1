def isEven (n : Nat) := n%2 = 0

def isOdd (n : Nat) := n%2 = 1

def isEvenOrOdd (n : Nat) := (isEven n) ∨ (isOdd n)

theorem nEvenOrOdd (n : Nat) : isEvenOrOdd n := by
  unfold isEvenOrOdd
  unfold isEven isOdd
  induction n with
  |zero => exact Or.inl rfl
  |succ n h => match h with
    |Or.inl x =>
      rw[Nat.add_mod]
      rw[x]
      apply Or.inr
      rfl
    |Or.inr x =>
      rw[Nat.add_mod]
      rw[x]
      apply Or.inl
      rfl


def sumPow2 : Nat → Nat
|Nat.zero => 1
|Nat.succ n'=> sumPow2 n' + 2^(n'+1)

theorem sumPow2_plus1 (n : Nat) : sumPow2 n = 2^(n+1) -1 :=
by
induction n with
|zero =>
  unfold sumPow2
  rfl
|succ x h=>
  rw[sumPow2]
  rw[h]
