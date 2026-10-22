module

@[expose] public section


namespace Chapter0

def hello₁ : String := "Hello world!"

def hello₂ (s : String) : String :=
 s!"Hello {s}!"

def factorial₀ (n : Nat) : Nat :=
  if n = 0
  then 1
  else n * factorial₀ (n - 1)

def factorial₁ (n : Nat) : Nat :=
  if h : n == 0
  then 1
  else
   have : n - 1 < n := by
    induction n with
    | zero => contradiction
    | succ n ih => omega
   n * factorial₁ (n - 1)

def factorial₂ : Nat → Nat
 | 0     => 1
 | n + 1 => factorial₂ n * (n + 1)


end Chapter0
