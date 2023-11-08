fibo : ℕ -> ℕ
fibo 0               = 0
fibo 1               = 1
fibo (succ (succ k)) = fibo k + fibo (succ k)
